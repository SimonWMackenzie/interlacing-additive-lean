import EthInapproximability.CurrentPaper.ExactBinControl

/-!
# Exact ceiling gates for the four-bin protocol

Source: locked v8 `E-exact-details.tex`, the fixed lower cutoff and proof
of `lem:exact-matrix-bounds`. These are numerical consequences for the
literal real density and the original sampler label count. No protocol or
communication lower bound is a premise.
-/

namespace EthInapproximability.CurrentPaper.ExactBinNumericGates

open ExactBinControl

/-- Three elementary inequalities suffice for the exact bin threshold and
survival of every one-coordinate symbol class. The ceiling is unchanged. -/
theorem bin_gates_of_real_bounds {N : ℕ} {h ε w : ℝ}
    (hh : 0 < h) (hhSmall : h ≤ 1 / 16) (hN : 8 ≤ N)
    (hMass : 3 ≤ 2 * h * N) (_hw : 0 < w)
    (hRatio : 8 * h < (1 - ε) / w) :
    4 * densityThreshold N h < N ∧
    (3 : ℝ) * densityThreshold N h ≤ 8 * h * N ∧
    ((3 * densityThreshold N h : ℕ) : ℝ) < (1 - ε) * N / w := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hNReal : (8 : ℝ) ≤ N := by exact_mod_cast hN
  have hceil : (densityThreshold N h : ℝ) < 2 * h * N + 1 :=
    Nat.ceil_lt_add_one (by positivity)
  have hsmallProduct : 8 * h * (N : ℝ) ≤ (N : ℝ) / 2 := by
    have hhN := mul_le_mul_of_nonneg_right hhSmall hNpos.le
    nlinarith
  have hgap : (4 : ℝ) * densityThreshold N h < N := by linarith
  have hloss : (3 : ℝ) * densityThreshold N h ≤ 8 * h * N := by linarith
  refine ⟨by exact_mod_cast hgap, hloss, ?_⟩
  have hratioN := mul_lt_mul_of_pos_right hRatio hNpos
  push_cast
  apply hloss.trans_lt
  simpa only [div_mul_eq_mul_div, mul_assoc] using hratioN

/-- The literal densities `h=r⁻³`, `ε=(2^r)⁻⁸` satisfy all three gates
for every positive alphabet width at most `4r²`. This includes the
manuscript's rounded width `ceil₂(2r²)`. -/
theorem rounded_bin_gates {r N w : ℕ} (hr : 64 ≤ r) (hN : (2 ^ r) ^ 6 ≤ N)
    (hw : 0 < w) (hwMax : (w : ℝ) ≤ 4 * (r : ℝ) ^ 2) :
    4 * densityThreshold N (1 / (r : ℝ) ^ 3) < N ∧
    (3 : ℝ) * densityThreshold N (1 / (r : ℝ) ^ 3) ≤
      8 * (1 / (r : ℝ) ^ 3) * N ∧
    ((3 * densityThreshold N (1 / (r : ℝ) ^ 3) : ℕ) : ℝ) <
      (1 - 1 / ((2 ^ r : ℕ) : ℝ) ^ 8) * N / (w : ℝ) := by
  have hrpos : (0 : ℝ) < r := by exact_mod_cast (show 0 < r by omega)
  have hrReal : (64 : ℝ) ≤ r := by exact_mod_cast hr
  have hr3 : (64 : ℝ) ^ 3 ≤ (r : ℝ) ^ 3 := by gcongr
  norm_num at hr3
  have hrd : r ≤ 2 ^ r := Nat.le_of_lt Nat.lt_two_pow_self
  have hrN : r ^ 6 ≤ N := (Nat.pow_le_pow_left hrd 6).trans hN
  have hrNReal : (r : ℝ) ^ 6 ≤ N := by exact_mod_cast hrN
  have hN8 : 8 ≤ N := by
    have hpow : 64 ^ 6 ≤ r ^ 6 := Nat.pow_le_pow_left hr 6
    omega
  have hd2 : 2 ≤ 2 ^ r := by omega
  have hd8strict : (2 : ℝ) < ((2 ^ r : ℕ) : ℝ) ^ 8 := by
    have hp : 2 ^ 8 ≤ (2 ^ r) ^ 8 := Nat.pow_le_pow_left hd2 8
    have hpReal : (2 : ℝ) ^ 8 ≤ ((2 ^ r : ℕ) : ℝ) ^ 8 := by exact_mod_cast hp
    norm_num at hpReal ⊢
    linarith
  have hε : 1 / ((2 ^ r : ℕ) : ℝ) ^ 8 < (1 / 2 : ℝ) := by
    apply (div_lt_div_iff₀ (by linarith : (0 : ℝ) < ((2 ^ r : ℕ) : ℝ) ^ 8)
      (by norm_num : (0 : ℝ) < 2)).mpr
    simpa using hd8strict
  have hwReal : (0 : ℝ) < w := by exact_mod_cast hw
  apply bin_gates_of_real_bounds (by positivity) ?_ hN8 ?_ hwReal ?_
  · exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith :
      (16 : ℝ) ≤ (r : ℝ) ^ 3)
  · rw [show 2 * (1 / (r : ℝ) ^ 3) * N = (2 * N) / (r : ℝ) ^ 3 by ring]
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < (r : ℝ) ^ 3)).mpr
    nlinarith [sq_nonneg ((r : ℝ) ^ 3)]
  · apply (lt_div_iff₀ hwReal).mpr
    have heq : 8 * (1 / (r : ℝ) ^ 3) * (4 * (r : ℝ) ^ 2) = 32 / (r : ℝ) := by
      field_simp
      ring
    have hratio : 32 / (r : ℝ) ≤ (1 / 2 : ℝ) :=
      (div_le_iff₀ hrpos).mpr (by linarith)
    have hwBound := mul_le_mul_of_nonneg_left hwMax
      (show 0 ≤ 8 * (1 / (r : ℝ) ^ 3) by positivity)
    rw [heq] at hwBound
    linarith

/-- The dyadic logarithmic schedule `r=2^s` makes the rounded manuscript
alphabet exactly `w=2r²`. This corollary exposes that convenient interface. -/
theorem exact_bin_gates {r N : ℕ} (hr : 64 ≤ r) (hN : (2 ^ r) ^ 6 ≤ N) :
    4 * densityThreshold N (1 / (r : ℝ) ^ 3) < N ∧
    (3 : ℝ) * densityThreshold N (1 / (r : ℝ) ^ 3) ≤
      8 * (1 / (r : ℝ) ^ 3) * N ∧
    ((3 * densityThreshold N (1 / (r : ℝ) ^ 3) : ℕ) : ℝ) <
      (1 - 1 / ((2 ^ r : ℕ) : ℝ) ^ 8) * N / (2 * (r : ℝ) ^ 2) := by
  have hrpos : 0 < r := by omega
  have hwMax : ((2 * r ^ 2 : ℕ) : ℝ) ≤ 4 * (r : ℝ) ^ 2 := by
    push_cast
    nlinarith [sq_nonneg (r : ℝ)]
  obtain ⟨hgap, hloss, hsurvive⟩ := rounded_bin_gates (w := 2 * r ^ 2)
    hr hN (by positivity) hwMax
  refine ⟨hgap, hloss, ?_⟩
  have hwcast : ((2 * r ^ 2 : ℕ) : ℝ) = 2 * (r : ℝ) ^ 2 := by push_cast; rfl
  rwa [hwcast] at hsurvive

end EthInapproximability.CurrentPaper.ExactBinNumericGates
