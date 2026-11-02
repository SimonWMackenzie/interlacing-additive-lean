import Mathlib

/-!
# Numerical error in a finite product of balanced families

Source: the locked current paper, Appendix A, Lemma `paper-product-extraction`,
part (3). We prove its numerical error bound by elementary polynomial
inequalities. The proof does not require an analytic estimate for the
exponential function.
-/

namespace EthInapproximability.CurrentPaper.ProductErrorSmall

/-- An elementary reciprocal form of the geometric upper bound. -/
theorem one_add_pow_mul_one_sub_nat_mul_le_one (ε : ℝ) (hε : 0 ≤ ε) (n : ℕ) :
    (1 + ε) ^ n * (1 - (n : ℝ) * ε) ≤ 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc
      (1 + ε) ^ (n + 1) * (1 - ((n + 1 : ℕ) : ℝ) * ε) =
          (1 + ε) ^ n * (1 - (n : ℝ) * ε) -
            ((n : ℝ) + 1) * ε ^ 2 * (1 + ε) ^ n := by
        rw [pow_succ, Nat.cast_add, Nat.cast_one]
        ring
      _ ≤ (1 + ε) ^ n * (1 - (n : ℝ) * ε) := by
        apply sub_le_self
        positivity
      _ ≤ 1 := ih

/-- The hypothesis used for one family bounds the sum of the factor errors. -/
theorem total_error_le_one_hundredth {ε : ℝ} {t : ℕ} (ht : 0 < t)
    (hε : ε ≤ 1 / (100 * (t : ℝ))) :
    (t : ℝ) * ε ≤ 1 / 100 := by
  have htR : (0 : ℝ) < t := by exact_mod_cast ht
  have hden : (0 : ℝ) < 100 * (t : ℝ) := by positivity
  have h := (le_div_iff₀ hden).mp hε
  nlinarith

/-- Explicit rational upper bound for the accumulated upper error. -/
theorem upper_error_le_one_ninety_ninth {ε : ℝ} {t : ℕ} (ht : 0 < t)
    (hε : 0 ≤ ε) (hsmall : ε ≤ 1 / (100 * (t : ℝ))) :
    (1 + ε) ^ t - 1 ≤ 1 / 99 := by
  have htotal := total_error_le_one_hundredth ht hsmall
  have hrecip := one_add_pow_mul_one_sub_nat_mul_le_one ε hε t
  have hpow : 0 ≤ (1 + ε) ^ t := by positivity
  have hmul := mul_nonneg hpow (show (0 : ℝ) ≤ 1 / 100 - (t : ℝ) * ε by linarith)
  nlinarith

/-- The upper accumulated relative error is strictly below `1/50`. -/
theorem upper_error_lt_one_fiftieth {ε : ℝ} {t : ℕ} (ht : 0 < t)
    (hε : 0 ≤ ε) (hsmall : ε ≤ 1 / (100 * (t : ℝ))) :
    (1 + ε) ^ t - 1 < 1 / 50 := by
  have := upper_error_le_one_ninety_ninth ht hε hsmall
  linarith

/-- Bernoulli's inequality bounds the accumulated lower error. -/
theorem lower_error_le_one_hundredth {ε : ℝ} {t : ℕ} (ht : 0 < t)
    (hε : 0 ≤ ε) (hsmall : ε ≤ 1 / (100 * (t : ℝ))) :
    1 - (1 - ε) ^ t ≤ 1 / 100 := by
  have htR : (1 : ℝ) ≤ t := by exact_mod_cast ht
  have htotal := total_error_le_one_hundredth ht hsmall
  have hεBound : ε ≤ 1 / 100 := by nlinarith
  have hbernoulli := one_add_mul_le_pow (by linarith : (-2 : ℝ) ≤ -ε) t
  have hbase : 1 + -ε = 1 - ε := by ring
  rw [hbase] at hbernoulli
  nlinarith

/-- The literal maximum of the two errors displayed in the paper is small. -/
theorem max_error_lt_one_fiftieth {ε : ℝ} {t : ℕ} (ht : 0 < t)
    (hε : 0 ≤ ε) (hsmall : ε ≤ 1 / (100 * (t : ℝ))) :
    max ((1 + ε) ^ t - 1) (1 - (1 - ε) ^ t) < 1 / 50 := by
  apply max_lt
  · exact upper_error_lt_one_fiftieth ht hε hsmall
  · have := lower_error_le_one_hundredth ht hε hsmall
    linarith

end EthInapproximability.CurrentPaper.ProductErrorSmall
