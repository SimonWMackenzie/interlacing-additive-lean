import CurrentAdditive.GenericSamplerFallbackTable
import Paper2.RecursiveSamplingMaterialization

/-! Row-major serialization of the total per-draw fallback sampler. -/

namespace Paper2.GenericSamplerFallbackMaterialization

open Paper2.RecursiveSamplingExecution
open Paper2.RecursiveSamplingMaterialization
open Paper2.RecursiveEntries

variable {V : Type} [Fintype V] [Nonempty V]
  {s q₁ q₂ w Q : ℕ} [NeZero s] [NeZero q₁] [NeZero q₂] [NeZero w] [NeZero Q]

def materialize (order : Fin (Fintype.card V) ≃ V) (hs : 4 ≤ s)
    (p : ℕ) (hp : 0 < p)
    (activity : SourceConstruction.Items s V → Fin q₂ → Option (Fin s))
    (ξ : Tails (Fin p → Bool) (Fin p) (SourceConstruction.Items s V)
      s q₁ q₂ w Q)
    (k mX mY : ℕ)
    (t : Tape V s q₁ q₂ w Q p k mX mY) :
    YaoMaterialization.SerializedTable mX mY :=
  YaoMaterialization.tabulate
    (GenericSamplerFallbackTable.run order hs p hp activity ξ k mX mY t)

theorem materialize_length (order : Fin (Fintype.card V) ≃ V) (hs : 4 ≤ s)
    (p : ℕ) (hp : 0 < p)
    (activity : SourceConstruction.Items s V → Fin q₂ → Option (Fin s))
    (ξ : Tails (Fin p → Bool) (Fin p) (SourceConstruction.Items s V)
      s q₁ q₂ w Q)
    (k mX mY : ℕ)
    (t : Tape V s q₁ q₂ w Q p k mX mY) :
    (materialize order hs p hp activity ξ k mX mY t).bits.length = mX * mY :=
  YaoMaterialization.tabulate_length _

theorem materialize_entry (order : Fin (Fintype.card V) ≃ V) (hs : 4 ≤ s)
    (p : ℕ) (hp : 0 < p)
    (activity : SourceConstruction.Items s V → Fin q₂ → Option (Fin s))
    (ξ : Tails (Fin p → Bool) (Fin p) (SourceConstruction.Items s V)
      s q₁ q₂ w Q)
    (k mX mY : ℕ)
    (t : Tape V s q₁ q₂ w Q p k mX mY) (i : Fin mX) (j : Fin mY) :
    (materialize order hs p hp activity ξ k mX mY t).matrix i j =
      GenericSamplerFallbackTable.run order hs p hp activity ξ k mX mY t i j :=
  YaoMaterialization.tabulate_matrix _ i j

theorem materialize_is_sampled_table
    (order : Fin (Fintype.card V) ≃ V) (hs : 4 ≤ s)
    (p : ℕ) (hp : 0 < p)
    (activity : SourceConstruction.Items s V → Fin q₂ → Option (Fin s))
    (ξ : Tails (Fin p → Bool) (Fin p) (SourceConstruction.Items s V)
      s q₁ q₂ w Q)
    (k mX mY : ℕ)
    (t : Tape V s q₁ q₂ w Q p k mX mY) :
    ∃ rows : Fin mX → Row (Fin p → Bool) (Fin p)
        (SourceConstruction.Items s V) s q₁ q₂ w Q k,
      ∃ cols : Fin mY → Column (Fin p → Bool) (Fin p)
        (SourceConstruction.Items s V) s q₁ q₂ w Q k,
        materialize order hs p hp activity ξ k mX mY t =
          YaoMaterialization.tabulate
            (RecursiveEntries.table (LookupSeed.matrix p) activity ξ k rows cols) := by
  obtain ⟨rows, cols, h⟩ := GenericSamplerFallbackTable.run_is_sampled_table
    order hs p hp activity ξ k mX mY t
  exact ⟨rows, cols, congrArg YaoMaterialization.tabulate h⟩

#print axioms materialize_is_sampled_table

end Paper2.GenericSamplerFallbackMaterialization
