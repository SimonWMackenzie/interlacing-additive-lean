import CurrentAdditive.GeneratedWAlignmentMass

/-! Pay the actual initially deleted protected rows once from the original
uniform-copy row law.  The owner-origin injection prevents double counting. -/

namespace CurrentAdditive.DeterministicIndexedMatrix.Sources

open Paper2 Paper2.ReferenceCertificateTree Paper2.ReferenceOwners
open scoped BigOperators

variable {X Y : Type*} [Fintype X] [Fintype Y]
  [DecidableEq X] [DecidableEq Y]
  {q₁ q₂ s w : ℕ} [NeZero s] [NeZero q₁] [NeZero q₂] [NeZero w]
  {μX : PositiveRationalLaw X} {μY : PositiveRationalLaw Y}
  (src : Sources (D := 8192) (q₁ := q₁) (q₂ := q₂)
    (s := s) μX μY)

theorem indexed_owner_protected_deleted_le
    {B J Ω : Type*} [Fintype Ω]
    (μ : FiniteLaw Ω) (input : J → Ω → Fin w × Column src)
    (floor : ℕ → ℝ) (depth fuel : ℕ)
    (state : State (Fin w × Column src) B J Ω)
    (O : Finset (run μ input floor depth fuel state).Leaves)
    (origin : O → Fin w) (hinjective : Function.Injective origin)
    (η : ℝ)
    (hR : 1-η/(16*w) ≤
      (((PositiveRationalLaw.uniform (Fin w)).prod
        (columnLaw src)).toFiniteLaw).prob (· ∈ state.rows)) :
    (Finset.univ.sum (fun u : ↥O =>
      protectedDeleted src state.rows (origin u))) ≤ η/16 := by
  classical
  have hwR : (0 : ℝ) < w := by exact_mod_cast NeZero.pos w
  have htotal := total_protectedDeleted_le src state.rows
    (η/(16*w)) hR
  have hnonneg (i : Fin w) :
      0 ≤ protectedDeleted src state.rows i := by
    unfold protectedDeleted
    have hf := src.outer.law.toFiniteLaw.prob_nonneg
      (fun z => (i,Column.fixedTail z) ∉ state.rows)
    have hd := (diagonalLaw src).toFiniteLaw.prob_nonneg
      (fun z => (i,Column.diagonal z) ∉ state.rows)
    positivity
  calc
    _ = ∑ i ∈ Finset.univ.image origin,
        protectedDeleted src state.rows i := by
      rw [Finset.sum_image]
      intro a _ b _ he
      exact hinjective he
    _ ≤ ∑ i : Fin w, protectedDeleted src state.rows i :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun i _ _ => hnonneg i)
    _ ≤ (w : ℝ) * (η/(16*w)) := htotal
    _ = η/16 := by
      field_simp

end CurrentAdditive.DeterministicIndexedMatrix.Sources

#print axioms CurrentAdditive.DeterministicIndexedMatrix.Sources.indexed_owner_protected_deleted_le
