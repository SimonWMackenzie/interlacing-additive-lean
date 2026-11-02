import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic

/-!
# Numerical margin in the defect induction

Frozen v12 Appendix A, `cl:defect-margin`: the strict logarithmic inequality
is proved from an exact rational-power comparison. The final estimate turns
a nonnegative logarithmic defect into a lower bound on retained density.
These are arithmetic facts only; no communication lower bound is assumed.
-/

namespace Paper2.DefectLogMargin

/-- The strict margin is an exact consequence of
`2^7 (3/5)^10 < 1`, not a decimal approximation to the logarithm. -/
theorem log_margin : (7 : ℝ) / 5 < -2 * Real.logb 2 (3 / 5) := by
  have hpos : 0 < (2 : ℝ) ^ 7 * (3 / 5) ^ 10 := by norm_num
  have hlt : (2 : ℝ) ^ 7 * (3 / 5) ^ 10 < 1 := by norm_num
  have h := Real.logb_lt_logb (b := 2) (by norm_num) hpos hlt
  rw [Real.logb_mul (by norm_num) (by norm_num),
    Real.logb_pow, Real.logb_pow,
    Real.logb_self_eq_one (by norm_num), Real.logb_one] at h
  norm_num at h
  linarith

/-- All three comparisons in frozen v12 `cl:defect-margin`.
Nonnegativity of `δ` is not needed for this upper-margin calculation. -/
theorem defect_margin {δ : ℝ} (hδ : δ ≤ 1 / 64) :
    3 * δ + 4 / 3 ≤ 265 / 192 ∧
      (265 : ℝ) / 192 < 7 / 5 ∧
      (7 : ℝ) / 5 < -2 * Real.logb 2 (3 / 5) := by
  refine ⟨?_, by norm_num, log_margin⟩
  linarith

/-- A slightly stronger natural-logarithm margin suitable for the existing
natural-defect induction. Here the logarithmic defect allowance is
`δ * log 2`. The constants are established from Mathlib's proved rational
enclosures of logarithms, not from floating-point evaluation. -/
theorem natural_log_margin {δ : ℝ} (hδ : δ ≤ 1 / 64) :
    3 * (δ * Real.log 2) + (7 / 5) * Real.log 2 ≤
      -2 * Real.log (3 / 5) := by
  have hscaled := mul_le_mul_of_nonneg_right hδ
    (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le
  have hlog2 := Real.log_two_lt_d9
  have hlog3 := Real.log_three_lt_d9
  have hlog5 := Real.log_five_gt_d9
  rw [Real.log_div (by norm_num : (3 : ℝ) ≠ 0)
    (by norm_num : (5 : ℝ) ≠ 0)]
  linarith

/-- The density estimate needed in the small-defect case. It holds for
every nonnegative defect, so the manuscript's additional `v ≤ 1` is not
needed for this inequality. -/
theorem one_sub_le_two_rpow_neg {v : ℝ} (hv : 0 ≤ v) :
    1 - v ≤ (2 : ℝ) ^ (-v) := by
  have hlog : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (x := 2) (by norm_num)
    norm_num at h
    exact h
  have hexp := Real.add_one_le_exp (Real.log 2 * (-v))
  rw [Real.rpow_def_of_pos (by norm_num)]
  nlinarith [mul_le_mul_of_nonneg_right hlog hv]

/-- The same density estimate expressed using natural logarithms. -/
theorem one_sub_le_exp_neg_mul_log_two {δ : ℝ} (hδ : 0 ≤ δ) :
    1 - δ ≤ Real.exp (-(δ * Real.log 2)) := by
  have h := one_sub_le_two_rpow_neg hδ
  rw [Real.rpow_def_of_pos (by norm_num)] at h
  convert h using 1
  congr 1
  ring

end Paper2.DefectLogMargin
