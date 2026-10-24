import CurrentAdditive.GenericSamplerFallbackEvent

/-! Uniform law for literal fixed-length input bit lists, read by the same
total per-draw fallback sampler and row-major table printer. -/

namespace Paper2.GenericSamplerFallbackTapeList

open Paper2.RecursiveSamplingExecution
open Paper2.RecursiveSamplingSeed
open Paper2.RecursiveSampling
open Paper2.RecursiveEntries

variable {V : Type} [Fintype V] [Nonempty V]
  {s q₁ q₂ w Q : ℕ} [NeZero s] [NeZero q₁] [NeZero q₂] [NeZero w] [NeZero Q]

abbrev TapeList (V : Type) [Fintype V] (s q₁ q₂ w Q p k mX mY : ℕ) :=
  RecursiveSamplingMaterialization.TapeList V s q₁ q₂ w Q p k mX mY

def materializeTapeList (order : Fin (Fintype.card V) ≃ V) (hs : 4 ≤ s)
    (p : ℕ) (hp : 0 < p)
    (activity : SourceConstruction.Items s V → Fin q₂ → Option (Fin s))
    (ξ : Tails (Fin p → Bool) (Fin p) (SourceConstruction.Items s V)
      s q₁ q₂ w Q)
    (k mX mY : ℕ)
    (bits : TapeList V s q₁ q₂ w Q p k mX mY) :
    YaoMaterialization.SerializedTable mX mY :=
  GenericSamplerFallbackMaterialization.materialize
    order hs p hp activity ξ k mX mY
    (RecursiveSamplingTape.readTape _ _ _ bits)

theorem materializeTapeList_bits_event_error
    (order : Fin (Fintype.card V) ≃ V) (hs : 4 ≤ s)
    (p : ℕ) (hp : 0 < p)
    (activity : SourceConstruction.Items s V → Fin q₂ → Option (Fin s))
    (ξ : Tails (Fin p → Bool) (Fin p) (SourceConstruction.Items s V)
      s q₁ q₂ w Q)
    (k mX mY : ℕ) (E : Set (List Bool)) :
    let B := Nat.clog 2 (alphabetCap s q₁ q₂ w Q (Fintype.card V) p)
    let N := drawCap s q₁ q₂ w Q p k mX mY
    let R := rejectionAttemptCap N
    |(RecursiveSamplingTape.serializedTapeLaw B R N).prob
        (fun bits => (materializeTapeList order hs p hp activity ξ k mX mY bits).bits ∈ E) -
      (sampleLaw (V := V) hs (LookupSeed.rowLaw p) (LookupSeed.columnLaw p hp)
        k mX mY).toFiniteLaw.prob
        (fun z => (YaoMaterialization.tabulate (sampleMatrix
          (RecursiveEntries.matrix (LookupSeed.matrix p) activity ξ k)
          z.2 z.1)).bits ∈ E)| ≤ (1 / 2 : ℝ) ^ 13 := by
  intro B N R
  have h := GenericSamplerFallbackEvent.materialize_bits_event_error
    order hs p hp activity ξ k mX mY E
  dsimp only [tapeLaw] at h
  rw [← RecursiveSamplingTape.serializedTapeLaw_prob B R N
    (fun t => (GenericSamplerFallbackMaterialization.materialize
      order hs p hp activity ξ k mX mY t).bits ∈ E)] at h
  exact h

#print axioms materializeTapeList_bits_event_error

end Paper2.GenericSamplerFallbackTapeList
