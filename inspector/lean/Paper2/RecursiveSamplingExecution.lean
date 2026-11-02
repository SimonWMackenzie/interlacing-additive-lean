import Paper2.RecursiveSamplingTable
import Paper2.RecursiveSamplingSeed

/-!
# The lookup-seeded table on a public bounded fair-bit tape

Frozen v12 Appendix D, ideal sampling and the capped implementation.
The alphabet and draw caps below are explicit functions of public scalar
parameters, not maxima found by traversing all generated labels. The output
is the actual recursive sampled matrix, or the all-zero table on exhaustion.
All-event error is measured against its proved ideal positive rational law.
This remains finite random-tape semantics, not an encoded printer or a
polynomial machine-time theorem.
-/

namespace Paper2.RecursiveSamplingExecution

open SourceMatrix RecursiveEntries RecursiveSamplingProgram RecursiveSamplingLaws
open RecursiveSampling RecursiveSamplingSeed

variable {V : Type} [Fintype V] [Nonempty V]
  {s q₁ q₂ w Q : ℕ} [NeZero s] [NeZero q₁] [NeZero q₂] [NeZero w] [NeZero Q]

def alphabetCap (s q₁ q₂ w Q vertices p : ℕ) : ℕ :=
  512 + q₁ + q₂ + 4 * s + w + Q + vertices + p + 2

def drawCap (s q₁ q₂ w Q p k mX mY : ℕ) : ℕ :=
  sampleDrawBound s q₁ q₂ w Q p 1 k mX mY

def program (order : Fin (Fintype.card V) ≃ V) (hs : 4 ≤ s) (p : ℕ) (hp : 0 < p)
    (activity : SourceConstruction.Items s V → Fin q₂ → Option (Fin s))
    (ξ : Tails (Fin p → Bool) (Fin p) (SourceConstruction.Items s V) s q₁ q₂ w Q)
    (k mX mY : ℕ) : Program (Fin mX → Fin mY → Bool) :=
  tableProgram order hs (seedRow p) (seedColumn p hp) (LookupSeed.matrix p) activity ξ k mX mY

theorem program_alphabetBound (order : Fin (Fintype.card V) ≃ V) (hs : 4 ≤ s)
    (p : ℕ) (hp : 0 < p)
    (activity : SourceConstruction.Items s V → Fin q₂ → Option (Fin s))
    (ξ : Tails (Fin p → Bool) (Fin p) (SourceConstruction.Items s V) s q₁ q₂ w Q)
    (k mX mY : ℕ) :
    (program order hs p hp activity ξ k mX mY).maxAlphabet ≤
      alphabetCap s q₁ q₂ w Q (Fintype.card V) p := by
  have hr := maxAlphabet_seedRow_le p
  have hc := maxAlphabet_seedColumn p hp
  simp only [program, tableProgram, Program.maxAlphabet_map]
  apply samples_alphabetBound
  all_goals unfold alphabetCap
  all_goals omega

theorem program_drawBound (order : Fin (Fintype.card V) ≃ V) (hs : 4 ≤ s)
    (p : ℕ) (hp : 0 < p)
    (activity : SourceConstruction.Items s V → Fin q₂ → Option (Fin s))
    (ξ : Tails (Fin p → Bool) (Fin p) (SourceConstruction.Items s V) s q₁ q₂ w Q)
    (k mX mY : ℕ) :
    (program order hs p hp activity ξ k mX mY).maxDraws ≤ drawCap s q₁ q₂ w Q p k mX mY := by
  simp only [program, tableProgram, Program.maxDraws_map, drawCap]
  exact samples_drawBound order hs (seedRow p) (seedColumn p hp) p 1
    (maxDraws_seedRow_le p) (le_of_eq (maxDraws_seedColumn p hp)) k mX mY

def state (order : Fin (Fintype.card V) ≃ V) (hs : 4 ≤ s) (p : ℕ) (hp : 0 < p)
    (activity : SourceConstruction.Items s V → Fin q₂ → Option (Fin s))
    (ξ : Tails (Fin p → Bool) (Fin p) (SourceConstruction.Items s V) s q₁ q₂ w Q)
    (k mX mY : ℕ) : RecursiveSamplingCapped.State (Fin mX → Fin mY → Bool)
      (alphabetCap s q₁ q₂ w Q (Fintype.card V) p) :=
  ⟨program order hs p hp activity ξ k mX mY,
    program_alphabetBound order hs p hp activity ξ k mX mY⟩

def Tape (V : Type) [Fintype V] (s q₁ q₂ w Q p k mX mY : ℕ) :=
  CappedSampler.Adaptive.Tape (Nat.clog 2 (alphabetCap s q₁ q₂ w Q (Fintype.card V) p))
    (rejectionAttemptCap (drawCap s q₁ q₂ w Q p k mX mY)) (drawCap s q₁ q₂ w Q p k mX mY)

def run (order : Fin (Fintype.card V) ≃ V) (hs : 4 ≤ s) (p : ℕ) (hp : 0 < p)
    (activity : SourceConstruction.Items s V → Fin q₂ → Option (Fin s))
    (ξ : Tails (Fin p → Bool) (Fin p) (SourceConstruction.Items s V) s q₁ q₂ w Q)
    (k mX mY : ℕ) (t : Tape V s q₁ q₂ w Q p k mX mY) : Fin mX → Fin mY → Bool :=
  CappedSampler.completed
    (RecursiveSamplingCapped.run _ _ le_rfl _ (state order hs p hp activity ξ k mX mY) t)
    (fun _ _ => false)

/-- On each individual tape, exhaustion returns the same-dimensional zero table. -/
theorem run_eq_zero_of_abort (order : Fin (Fintype.card V) ≃ V) (hs : 4 ≤ s)
    (p : ℕ) (hp : 0 < p)
    (activity : SourceConstruction.Items s V → Fin q₂ → Option (Fin s))
    (ξ : Tails (Fin p → Bool) (Fin p) (SourceConstruction.Items s V) s q₁ q₂ w Q)
    (k mX mY : ℕ) (t : Tape V s q₁ q₂ w Q p k mX mY)
    (h : RecursiveSamplingCapped.run _ _ le_rfl _
      (state order hs p hp activity ξ k mX mY) t = none) :
    run order hs p hp activity ξ k mX mY t = (fun _ _ => false) := by
  simp only [run, h, CappedSampler.completed]
  rfl

noncomputable def tapeLaw (V : Type) [Fintype V] (s q₁ q₂ w Q p k mX mY : ℕ) :=
  CappedSampler.Adaptive.law (Nat.clog 2 (alphabetCap s q₁ q₂ w Q (Fintype.card V) p))
    (rejectionAttemptCap (drawCap s q₁ q₂ w Q p k mX mY)) (drawCap s q₁ q₂ w Q p k mX mY)

theorem run_event_error (order : Fin (Fintype.card V) ≃ V) (hs : 4 ≤ s)
    (p : ℕ) (hp : 0 < p)
    (activity : SourceConstruction.Items s V → Fin q₂ → Option (Fin s))
    (ξ : Tails (Fin p → Bool) (Fin p) (SourceConstruction.Items s V) s q₁ q₂ w Q)
    (k mX mY : ℕ) (E : Set (Fin mX → Fin mY → Bool)) :
    |(tapeLaw V s q₁ q₂ w Q p k mX mY).prob
        (fun t => run order hs p hp activity ξ k mX mY t ∈ E) -
      (sampleLaw (V := V) hs (LookupSeed.rowLaw p) (LookupSeed.columnLaw p hp)
        k mX mY).toFiniteLaw.prob
        (fun z => sampleMatrix (RecursiveEntries.matrix (LookupSeed.matrix p) activity ξ k)
          z.2 z.1 ∈ E)| ≤ (1 / 2 : ℝ) ^ 13 := by
  have h := RecursiveSamplingCapped.scheduled_output_event_error
    (Nat.clog 2 (alphabetCap s q₁ q₂ w Q (Fintype.card V) p)) le_rfl
    (drawCap s q₁ q₂ w Q p k mX mY) (state order hs p hp activity ξ k mX mY)
    (program_drawBound order hs p hp activity ξ k mX mY) (fun _ _ => false) E
  change |(tapeLaw V s q₁ q₂ w Q p k mX mY).prob
        (fun t => run order hs p hp activity ξ k mX mY t ∈ E) -
      (program order hs p hp activity ξ k mX mY).eventProb E| ≤ _ at h
  rw [program, tableProgram_event order hs (seedRow p) (seedColumn p hp)
    (LookupSeed.rowLaw p) (LookupSeed.columnLaw p hp)
    (generates_seedRow p) (generates_seedColumn p hp)] at h
  exact h

end Paper2.RecursiveSamplingExecution
