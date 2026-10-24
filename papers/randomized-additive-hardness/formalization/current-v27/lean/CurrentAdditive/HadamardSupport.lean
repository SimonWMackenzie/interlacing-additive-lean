import Mathlib.Analysis.InnerProductSpace.Orientation
import CurrentAdditive.CramerMinorBound

set_option maxHeartbeats 1000000

namespace CurrentAdditive.HadamardSupport

open Matrix

/-- Hadamard's determinant inequality for a real square matrix, expressed
with the Euclidean norms of its column vectors. -/
theorem det_abs_le_prod_column_norm (r : Nat)
    (A : Matrix (Fin r) (Fin r) ℝ) :
    |A.det| ≤ ∏ j : Fin r,
      ‖(EuclideanSpace.equiv (Fin r) ℝ).symm (fun i => A i j)‖ := by
  let b := EuclideanSpace.basisFun (Fin r) ℝ
  let v : Fin r → EuclideanSpace ℝ (Fin r) :=
    fun j => (EuclideanSpace.equiv (Fin r) ℝ).symm (fun i => A i j)
  have hmat : b.toBasis.toMatrix v = A := by
    ext i j
    simp [b, v, Module.Basis.toMatrix_apply]
  have hdet : b.toBasis.det v = A.det := by
    rw [Module.Basis.det_apply, hmat]
  letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin r)) = r) :=
    ⟨by simp⟩
  let o := b.toBasis.orientation
  have hvol : |o.volumeForm v| = |b.toBasis.det v| :=
    o.volumeForm_robust' b v
  rw [hdet] at hvol
  exact hvol ▸ o.abs_volumeForm_apply_le v

/-- The exact Hadamard envelope in integer arithmetic. The squared form
avoids rounding when `r` is odd: it is precisely `|det| ≤ r^(r/2)` over
the reals. -/
theorem det_zero_one_natAbs_sq_le_pow (r : Nat)
    (A : Matrix (Fin r) (Fin r) ℤ)
    (h01 : ∀ i j, A i j = 0 ∨ A i j = 1) :
    A.det.natAbs ^ 2 ≤ r ^ r := by
  let R : Matrix (Fin r) (Fin r) ℝ := fun i j => (A i j : ℝ)
  have hR01 : ∀ i j, R i j = 0 ∨ R i j = 1 := by
    intro i j
    rcases h01 i j with h | h <;> simp [R, h]
  have hnorm (j : Fin r) :
      ‖(EuclideanSpace.equiv (Fin r) ℝ).symm (fun i => R i j)‖ ≤
        Real.sqrt (r : ℝ) := by
    apply Real.le_sqrt_of_sq_le
    rw [EuclideanSpace.real_norm_sq_eq]
    have hterm : ∀ i : Fin r, (R i j : ℝ) ^ 2 ≤ 1 := by
      intro i
      rcases hR01 i j with h | h <;> simp [h]
    calc
      (∑ i : Fin r, (R i j : ℝ) ^ 2) ≤
          ∑ _i : Fin r, (1 : ℝ) :=
        Finset.sum_le_sum (fun i _ => hterm i)
      _ = (r : ℝ) := by simp
  have hdet : |R.det| ≤ (Real.sqrt (r : ℝ)) ^ r := by
    calc
      |R.det| ≤ ∏ j : Fin r,
          ‖(EuclideanSpace.equiv (Fin r) ℝ).symm (fun i => R i j)‖ :=
        det_abs_le_prod_column_norm r R
      _ ≤ ∏ _j : Fin r, Real.sqrt (r : ℝ) := by
        apply Finset.prod_le_prod
        · intro j hj
          exact norm_nonneg _
        · intro j hj
          exact hnorm j
      _ = (Real.sqrt (r : ℝ)) ^ r := by simp
  have hsq : |R.det| ^ 2 ≤ ((r : ℝ) ^ r) := by
    have hsq' : |R.det| ^ 2 ≤ (Real.sqrt (r : ℝ) ^ r) ^ 2 := by
      gcongr
    calc
      |R.det| ^ 2 ≤ (Real.sqrt (r : ℝ) ^ r) ^ 2 := hsq'
      _ = (r : ℝ) ^ r := by
        rw [← pow_mul, mul_comm r 2, pow_mul, Real.sq_sqrt (by positivity)]
  have hcast : R.det = (A.det : ℝ) := by
    simpa [R] using (Int.cast_det A).symm
  rw [hcast] at hsq
  have hnat : (((A.det.natAbs ^ 2 : Nat) : ℝ)) ≤ ((r ^ r : Nat) : ℝ) := by
    simpa only [Nat.cast_pow, Nat.cast_natAbs, Int.cast_abs] using hsq
  exact_mod_cast hnat

#print axioms det_abs_le_prod_column_norm
#print axioms det_zero_one_natAbs_sq_le_pow

end CurrentAdditive.HadamardSupport
