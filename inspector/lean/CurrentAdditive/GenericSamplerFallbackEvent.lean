import CurrentAdditive.GenericSamplerFallbackMaterialization
import CurrentAdditive.ProgramFallbackLaw

/-! The manuscript-faithful total sampler has the same ideal sampled-table
law up to the exact public rejection-cap error, for every matrix event. -/

namespace Paper2.GenericSamplerFallbackEvent

open Paper2.RecursiveSamplingExecution
open Paper2.RecursiveSampling
open Paper2.RecursiveSamplingSeed
open Paper2.RecursiveEntries

variable {V : Type} [Fintype V] [Nonempty V]
  {s q₁ q₂ w Q : ℕ} [NeZero s] [NeZero q₁] [NeZero q₂] [NeZero w] [NeZero Q]

theorem run_event_error (order : Fin (Fintype.card V) ≃ V) (hs : 4 ≤ s)
    (p : ℕ) (hp : 0 < p)
    (activity : SourceConstruction.Items s V → Fin q₂ → Option (Fin s))
    (ξ : Tails (Fin p → Bool) (Fin p) (SourceConstruction.Items s V)
      s q₁ q₂ w Q)
    (k mX mY : ℕ) (E : Set (Fin mX → Fin mY → Bool)) :
    |(tapeLaw V s q₁ q₂ w Q p k mX mY).prob
        (fun t => GenericSamplerFallbackTable.run
          order hs p hp activity ξ k mX mY t ∈ E) -
      (sampleLaw (V := V) hs (LookupSeed.rowLaw p) (LookupSeed.columnLaw p hp)
        k mX mY).toFiniteLaw.prob
        (fun z => sampleMatrix
          (RecursiveEntries.matrix (LookupSeed.matrix p) activity ξ k)
          z.2 z.1 ∈ E)| ≤ (1 / 2 : ℝ) ^ 13 := by
  have h := RecursiveSamplingCapped.scheduled_runProgramFallback_event_error
    (Nat.clog 2 (alphabetCap s q₁ q₂ w Q (Fintype.card V) p)) le_rfl
    (drawCap s q₁ q₂ w Q p k mX mY)
    (state order hs p hp activity ξ k mX mY)
    (program_drawBound order hs p hp activity ξ k mX mY) E
  change |(tapeLaw V s q₁ q₂ w Q p k mX mY).prob
      (fun t => GenericSamplerFallbackTable.run
        order hs p hp activity ξ k mX mY t ∈ E) -
      (program order hs p hp activity ξ k mX mY).eventProb E| ≤ _ at h
  rw [program, tableProgram_event order hs (seedRow p) (seedColumn p hp)
    (LookupSeed.rowLaw p) (LookupSeed.columnLaw p hp)
    (generates_seedRow p) (generates_seedColumn p hp)] at h
  exact h

theorem materialize_bits_event_error
    (order : Fin (Fintype.card V) ≃ V) (hs : 4 ≤ s)
    (p : ℕ) (hp : 0 < p)
    (activity : SourceConstruction.Items s V → Fin q₂ → Option (Fin s))
    (ξ : Tails (Fin p → Bool) (Fin p) (SourceConstruction.Items s V)
      s q₁ q₂ w Q)
    (k mX mY : ℕ) (E : Set (List Bool)) :
    |(tapeLaw V s q₁ q₂ w Q p k mX mY).prob
        (fun t => (GenericSamplerFallbackMaterialization.materialize
          order hs p hp activity ξ k mX mY t).bits ∈ E) -
      (sampleLaw (V := V) hs (LookupSeed.rowLaw p) (LookupSeed.columnLaw p hp)
        k mX mY).toFiniteLaw.prob
        (fun z => (YaoMaterialization.tabulate (sampleMatrix
          (RecursiveEntries.matrix (LookupSeed.matrix p) activity ξ k)
          z.2 z.1)).bits ∈ E)| ≤ (1 / 2 : ℝ) ^ 13 := by
  exact run_event_error order hs p hp activity ξ k mX mY
    {F | (YaoMaterialization.tabulate F).bits ∈ E}

#print axioms run_event_error
#print axioms materialize_bits_event_error

end Paper2.GenericSamplerFallbackEvent
