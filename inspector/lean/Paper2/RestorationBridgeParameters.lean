import Paper2.DefectInduction
import EthBridge.Entry

/-!
# Numerical parameters for restoration

Frozen v12 Appendix A, `cl:bridge`. The inherited entry theorem uses
natural logarithms and a column margin `1/10`. Here its parameter package
is derived from exactly `2^r * delta >= 80b` and `2^r * theta < 1/20`.
Leastness of the power of two is unnecessary for these lower bounds.
-/

namespace Paper2.RestorationBridge

theorem dyadic_defect (b : ℕ) :
    EthBridge.entryDefect ((2 : ℝ) ^ (-(b : ℝ))) = (b : ℝ) * Real.log 2 := by
  rw [EthBridge.entryDefect, one_div, Real.log_inv, Real.log_rpow (by norm_num)]
  ring

theorem dyadic_threshold_pos (b : ℕ) : 0 < (2 : ℝ) ^ (-(b : ℝ)) := by positivity

theorem dyadic_threshold_lt_one (b : ℕ) (hb : 1 ≤ b) :
    (2 : ℝ) ^ (-(b : ℝ)) < 1 := by
  apply Real.rpow_lt_one_of_one_lt_of_neg (by norm_num)
  have : (0 : ℝ) < b := by exact_mod_cast (by omega : 0 < b)
  linarith

theorem width_lower (r b : ℕ) (δ : ℝ) (hb : 1 ≤ b)
    (hδ : δ ≤ 1 / 64) (hQ : 80 * (b : ℝ) ≤ (2 : ℝ) ^ r * δ) :
    5120 ≤ (2 : ℝ) ^ r := by
  have hbR : (1 : ℝ) ≤ b := by exact_mod_cast hb
  have hp : 0 ≤ (2 : ℝ) ^ r := by positivity
  nlinarith

theorem exponent_lower (r b : ℕ) (δ : ℝ) (hb : 1 ≤ b)
    (hδ : δ ≤ 1 / 64) (hQ : 80 * (b : ℝ) ≤ (2 : ℝ) ^ r * δ) :
    4 ≤ r := by
  have hlarge := width_lower r b δ hb hδ hQ
  by_contra hh
  have hp : (2 : ℝ) ^ r ≤ 2 ^ 3 :=
    pow_le_pow_right₀ (by norm_num) (by omega)
  norm_num at hp
  linarith

theorem theta_upper (r : ℕ) (θ : ℝ) (hθ : 0 < θ)
    (hscale : (2 : ℝ) ^ r * θ < 1 / 20) : θ ≤ 1 / 4 := by
  have hp : (1 : ℝ) ≤ 2 ^ r := one_le_pow₀ (by norm_num)
  nlinarith

theorem entry_parameters (r b m : ℕ) (θ δ : ℝ)
    (hb : 1 ≤ b) (hm : 1 ≤ m) (hθ : 0 < θ)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 64)
    (hQ : 80 * (b : ℝ) ≤ (2 : ℝ) ^ r * δ)
    (hscale : (2 : ℝ) ^ r * θ < 1 / 20) :
    ∀ j : ℕ, j ≤ 2 →
      EthBridge.entryCopies r j ((2 : ℝ) ^ (-(b : ℝ))) (δ * Real.log 2) ≤ 2 ^ r ∧
      ((EthBridge.entryRowBound (2 ^ r) m
        (EthBridge.entryCopies r j ((2 : ℝ) ^ (-(b : ℝ))) (δ * Real.log 2))
        (EthBridge.rowThreshold m θ (EthBridge.entryLevel r j)) : ℕ) : ℝ)
        < (2 : ℝ) ^ r * m * (3 / 5) / 2 ^ j := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hQL : 8 * EthBridge.entryDefect ((2 : ℝ) ^ (-(b : ℝ))) /
      ((1 / 10) * (δ * Real.log 2)) ≤ (2 : ℝ) ^ r := by
    rw [dyadic_defect]
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith [mul_le_mul_of_nonneg_right hQ hlog.le]
  exact EthBridge.uniform_package r m θ (δ * Real.log 2)
    ((2 : ℝ) ^ (-(b : ℝ))) (1 / 10) (3 / 5)
    (exponent_lower r b δ hb hδ1 hQ) hm (by norm_num) (by norm_num)
    (by norm_num) (mul_pos hδ hlog) hθ (dyadic_threshold_pos b)
    (dyadic_threshold_lt_one b hb) hQL
    (by have := width_lower r b δ hb hδ1 hQ; norm_num; linarith)
    (by norm_num at *; exact hscale)

end Paper2.RestorationBridge
