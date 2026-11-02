import EthInapproximability.CurrentPaper.HardSeed

/-!
# The exact reduction's small column-density comparison

Source: locked v8 `E-exact-details.tex`, `eq:exact-coordinate-estimates`
and the fixed lower cutoff; `D-hard-seed.tex`, `thm:foundation-hard-seed`.
Here `s = log₂ log₂ d`, and `m = log₂ t₂`.  We give an explicit
matrix-independent cutoff for the scalar comparison used in the stopping
argument.  The actual sampler construction and its size are separate.
-/

namespace EthInapproximability.CurrentPaper.ExactHardSeedGate

/-- A logarithm estimate at the square-root scale of the hard-seed cutoff. -/
theorem log_le_eighth (x : ℝ) (hx : 1024 ≤ x) :
    Real.log x ≤ x / 8 * Real.log 2 := by
  have hxp : 0 < x := by linarith
  have hlo : (1 : ℝ) / 2 ≤ Real.log 2 := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h ⊢
    exact h
  have hhi : Real.log (2 : ℝ) ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h
    exact h
  have h64 : Real.log (64 : ℝ) = 6 * Real.log 2 := by
    convert Real.log_pow (2 : ℝ) 6 using 1
    norm_num
  have h := Real.log_le_sub_one_of_pos (div_pos hxp (by norm_num : (0 : ℝ) < 64))
  rw [Real.log_div (ne_of_gt hxp) (by norm_num : (64 : ℝ) ≠ 0), h64] at h
  have hmul := mul_le_mul_of_nonneg_left hlo (show 0 ≤ x / 8 by linarith)
  nlinarith

/-- The double exponential in the hard-seed density dominates the exact
reduction's linear exponent, uniformly for every permitted second width. -/
theorem exponent_dominates {s m : ℕ} (hs : 2 ^ 21 ≤ s) (hsm : s / 2 ≤ m) :
    6 * (s : ℝ) + 3 ≤ (2 : ℝ) ^ ((49 / 100 : ℝ) * Real.sqrt (m : ℝ)) := by
  have hm : 2 ^ 20 ≤ m := by omega
  obtain ⟨hr, _, _⟩ := HardSeedArithmetic.base_estimates hm
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hlogm := log_le_eighth (Real.sqrt (m : ℝ)) hr
  rw [Real.log_sqrt (Nat.cast_nonneg m)] at hlogm
  have hlog2 : 0 ≤ Real.log (2 : ℝ) := Real.log_nonneg (by norm_num)
  have h16 : Real.log (16 : ℝ) = 4 * Real.log 2 := by
    convert Real.log_pow (2 : ℝ) 4 using 1
    norm_num
  have hlarge : (16 : ℝ) * m ≤
      (2 : ℝ) ^ ((49 / 100 : ℝ) * Real.sqrt (m : ℝ)) := by
    apply (Real.le_rpow_iff_log_le (by positivity) (by norm_num)).mpr
    rw [Real.log_mul (by norm_num : (16 : ℝ) ≠ 0) (ne_of_gt hmpos), h16]
    have hslack := mul_nonneg
      (show 0 ≤ (49 / 100 : ℝ) * Real.sqrt (m : ℝ) -
        (4 + Real.sqrt (m : ℝ) / 4) by linarith) hlog2
    nlinarith
  have hsm' : s ≤ 2 * m + 1 := by omega
  have hsmR : (s : ℝ) ≤ 2 * m + 1 := by exact_mod_cast hsm'
  have hmR : (1048576 : ℝ) ≤ m := by exact_mod_cast hm
  exact (show 6 * (s : ℝ) + 3 ≤ 16 * m by linarith).trans hlarge

/-- The hard-seed column fraction is small enough for the exact second
stopping call, including its original retained fraction and bias loss. -/
theorem column_density_le {s m : ℕ} {ε : ℝ}
    (hs : 2 ^ 21 ≤ s) (hsm : s / 2 ≤ m) (hms : m ≤ s)
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    HardSeed.columnDensity ((2 : ℝ) ^ m) ≤
      (1 / (2 : ℝ) ^ (3 * s)) *
        (2 : ℝ) ^ (-(((2 * s + 1) + 1 + m : ℕ) : ℝ)) / (1 + ε) := by
  have hexp := exponent_dominates hs hsm
  have hmsR : (m : ℝ) ≤ s := by exact_mod_cast hms
  have hsum : ((3 * s + ((2 * s + 1) + 1 + m) + 1 : ℕ) : ℝ) ≤
      (2 : ℝ) ^ ((49 / 100 : ℝ) * Real.sqrt (m : ℝ)) := by
    push_cast
    linarith
  have hpow : HardSeed.columnDensity ((2 : ℝ) ^ m) ≤
      (2 : ℝ) ^ (-(((3 * s + ((2 * s + 1) + 1 + m) + 1 : ℕ) : ℝ))) := by
    rw [HardSeed.columnDensity_pow]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (neg_le_neg hsum)
  have hid :
      (2 : ℝ) ^ (-(((3 * s + ((2 * s + 1) + 1 + m) + 1 : ℕ) : ℝ))) =
      (1 / (2 : ℝ) ^ (3 * s)) *
        (2 : ℝ) ^ (-(((2 * s + 1) + 1 + m : ℕ) : ℝ)) / 2 := by
    rw [one_div, ← Real.rpow_natCast, ← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    rw [div_eq_mul_inv, show (2 : ℝ)⁻¹ = (2 : ℝ) ^ (-1 : ℝ) by norm_num]
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    congr 1
    push_cast
    ring
  rw [hid] at hpow
  exact hpow.trans (div_le_div_of_nonneg_left (by positivity)
    (by linarith : 0 < 1 + ε) (by linarith : 1 + ε ≤ (2 : ℝ)))

end EthInapproximability.CurrentPaper.ExactHardSeedGate
