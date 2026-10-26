import Paper2.RestorationWidthSchedule

/-!
An explicit finite cutoff for quadratic polynomials in the public
ceiling logarithm. No eventual-growth oracle is used.
-/

namespace Paper2.LogSquareCutoff

open RestorationWidthScheduleScratch

/-- A deliberately conservative elementary exponential comparison. -/
private theorem cube_le_dyadic (n : ℕ) (hn : 16 ≤ n) :
    n ^ 3 ≤ 2 ^ (n - 2) := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
      have hnext : n + 1 - 2 = (n - 2) + 1 := by omega
      rw [hnext, pow_succ]
      have hpoly : (n + 1) ^ 3 ≤ 2 * n ^ 3 := by
        nlinarith [sq_nonneg ((n : ℤ) - 4)]
      calc
        (n + 1) ^ 3 ≤ 2 * n ^ 3 := hpoly
        _ ≤ 2 * 2 ^ (n - 2) := Nat.mul_le_mul_left _ ih
        _ = 2 ^ (n - 2) * 2 := by omega

/-- A computable cutoff depending only on the natural coefficients. -/
def cutoff (A B C : ℕ) : ℕ := 2 ^ (A + B + C + 16)

/-- Above the public cutoff, a quadratic polynomial in the actual
`ell(L)=clog₂(L+1)` is bounded by `L`. -/
theorem quadratic_log_le (A B C L : ℕ) (hL : cutoff A B C ≤ L) :
    A * (ell L) ^ 2 + B * ell L + C ≤ L := by
  let n := ell L
  let K := A + B + C
  have hhigh : K + 16 ≤ n := by
    have hp : 2 ^ (K + 16) ≤ L + 1 := by
      unfold cutoff at hL
      dsimp [K] at *
      omega
    have hc := Nat.clog_mono_right 2 hp
    simpa only [Nat.clog_pow 2 (K + 16) (by decide), n, ell] using hc
  have hn : 16 ≤ n := by omega
  have hK : K ≤ n := by omega
  have hn1 : 1 ≤ n := by omega
  have hbn : n ≤ n ^ 2 := by nlinarith
  have hcn : 1 ≤ n ^ 2 := by nlinarith
  have hpoly : A * n ^ 2 + B * n + C ≤ K * n ^ 2 := by
    have hB := Nat.mul_le_mul_left B hbn
    have hC := Nat.mul_le_mul_left C hcn
    dsimp [K]
    nlinarith
  have hcubic : K * n ^ 2 ≤ n ^ 3 := by
    have h := Nat.mul_le_mul_right (n ^ 2) hK
    nlinarith
  have hd := cube_le_dyadic n hn
  have hfloor : 2 ^ (n - 1) ≤ L := by
    have hp := Nat.pow_pred_clog_lt_self (by decide : 1 < 2)
      (show 1 < L + 1 by
        have hcut : 0 < cutoff A B C := by unfold cutoff; positivity
        omega)
    change 2 ^ (n - 1) < L + 1 at hp
    omega
  have hstep : 2 ^ (n - 2) ≤ 2 ^ (n - 1) := by
    exact Nat.pow_le_pow_right (by decide) (by omega)
  exact hpoly.trans (hcubic.trans (hd.trans (hstep.trans hfloor)))

#print axioms quadratic_log_le

end Paper2.LogSquareCutoff
