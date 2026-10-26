import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Tactic

/-!
# Rank of necessary-constraint witnesses

Source: Paper 2, v12, Section 2, proof of `thm:rank-count`.
The two square witness matrices are the identity and its Boolean complement.
The complement has full real rank except in dimension one. These statements
concern actual submatrices, including arbitrary repeated input labels.
-/

namespace Paper2

open scoped BigOperators

/-- The Boolean complement of the identity matrix. -/
def complementIdentity (I : Type*) [DecidableEq I] : Matrix I I ℝ :=
  fun i j => if i = j then 0 else 1

theorem complementIdentity_mulVec {I : Type*} [Fintype I] [DecidableEq I]
    (v : I → ℝ) (i : I) :
    (complementIdentity I).mulVec v i = (∑ j, v j) - v i := by
  classical
  have hentry : complementIdentity I = Matrix.of (fun (_ _ : I) => (1 : ℝ)) -
      (1 : Matrix I I ℝ) := by
    ext a b
    by_cases h : a = b <;> simp [complementIdentity, h]
  rw [hentry, Matrix.sub_mulVec, Matrix.one_mulVec]
  simp [Matrix.mulVec, dotProduct]

/-- The complement of the identity has full real rank when the number of
indices is not one. The empty matrix is included. -/
theorem rank_complementIdentity {I : Type*} [Fintype I] [DecidableEq I]
    (hcard : Fintype.card I ≠ 1) :
    (complementIdentity I).rank = Fintype.card I := by
  have hinj : Function.Injective (complementIdentity I).mulVecLin := by
    apply (LinearMap.ker_eq_bot).mp
    apply LinearMap.ker_eq_bot'.mpr
    intro v hv
    have heq (i : I) : v i = ∑ j, v j := by
      have h := congrFun hv i
      change (complementIdentity I).mulVec v i = 0 at h
      rw [complementIdentity_mulVec] at h
      linarith
    have hsum : (∑ j, v j) = (Fintype.card I : ℝ) * (∑ j, v j) := by
      conv_lhs => arg 2; ext j; rw [heq j]
      simp
    have hn : (Fintype.card I : ℝ) - 1 ≠ 0 := by
      exact sub_ne_zero.mpr (by exact_mod_cast hcard)
    have hz : (∑ j, v j) = 0 := by
      apply (mul_eq_zero.mp (show ((Fintype.card I : ℝ) - 1) * (∑ j, v j) = 0 by
        nlinarith)).resolve_left hn
    ext i
    simpa [heq i] using hz
  rw [Matrix.rank, LinearMap.finrank_range_of_inj hinj, Module.finrank_pi]

/-- Identity-shaped actual witnesses bound their number by the matrix rank. -/
theorem card_le_rank_of_zero_witness
    {X Y I : Type*} [Fintype Y] [Fintype I]
    (M : Matrix X Y ℝ) (rows : I → X) (cols : I → Y)
    (hdiag : ∀ i, M (rows i) (cols i) = 1)
    (hoff : ∀ i j, i ≠ j → M (rows i) (cols j) = 0) :
    Fintype.card I ≤ M.rank := by
  classical
  have hmat : M.submatrix rows cols = (1 : Matrix I I ℝ) := by
    ext i j
    by_cases h : i = j
    · subst j
      simpa using hdiag i
    · simpa [Matrix.one_apply, h] using hoff i j h
  simpa [hmat] using Matrix.rank_submatrix_le M rows cols

/-- Complement-identity-shaped actual witnesses bound their number by rank,
apart from the exceptional one-row zero matrix. -/
theorem card_le_rank_of_one_witness
    {X Y I : Type*} [Fintype Y] [Fintype I]
    (M : Matrix X Y ℝ) (rows : I → X) (cols : I → Y)
    (hcard : Fintype.card I ≠ 1)
    (hdiag : ∀ i, M (rows i) (cols i) = 0)
    (hoff : ∀ i j, i ≠ j → M (rows i) (cols j) = 1) :
    Fintype.card I ≤ M.rank := by
  classical
  have hmat : M.submatrix rows cols = complementIdentity I := by
    ext i j
    by_cases h : i = j
    · subst j
      simpa [complementIdentity] using hdiag i
    · simpa [complementIdentity, h] using hoff i j h
  have hbound := Matrix.rank_submatrix_le M rows cols
  rw [hmat, rank_complementIdentity hcard] at hbound
  exact hbound

end Paper2

#print axioms Paper2.rank_complementIdentity
#print axioms Paper2.card_le_rank_of_zero_witness
#print axioms Paper2.card_le_rank_of_one_witness
