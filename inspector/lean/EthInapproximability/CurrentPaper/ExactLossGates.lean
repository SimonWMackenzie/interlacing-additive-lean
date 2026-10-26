import EthInapproximability.ParameterizedNP.StageTwoRelaxed

/-!
# Retained-density gates for the exact reduction

Source: locked v8 `E-exact-details.tex`, residual indexing, the coordinate
matrix, and the fixed lower cutoff. We use the literal `NPCC.yLoss` and
prove the required scalar estimates from the displayed parameter formulas.
-/

namespace EthInapproximability.CurrentPaper.ExactLossGates

open NPCC
open EthInapproximability.ParameterizedNP.StageTwoRelaxed

/-- A factor `1+ε` with `ε ≤ 1` loses at most one binary exponent. -/
theorem ratio_lower {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (u c : ℕ) :
    (2 : ℝ) ^ (-((u + c + 1 : ℕ) : ℝ)) ≤
      (1 / (2 : ℝ) ^ u) * (2 : ℝ) ^ (-(c : ℝ)) / (1 + ε) := by
  have hid : (2 : ℝ) ^ (-((u + c + 1 : ℕ) : ℝ)) =
      (1 / (2 : ℝ) ^ u) * (2 : ℝ) ^ (-(c : ℝ)) / 2 := by
    rw [one_div, ← Real.rpow_natCast, ← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    rw [div_eq_mul_inv, show (2 : ℝ)⁻¹ = (2 : ℝ) ^ (-1 : ℝ) by norm_num]
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    congr 1
    push_cast
    ring
  rw [hid]
  exact div_le_div_of_nonneg_left (by positivity) (by linarith) (by linarith)

/-- A direct exponent-budget criterion for the literal loss density. -/
theorem power_le_yLoss {ε b : ℝ} {t u c : ℕ}
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (ht : 0 < t)
    (hbudget : ((u + c + 1 : ℕ) : ℝ) ≤ b * t) :
    (2 : ℝ) ^ (-b) ≤ yLoss ε t (1 / (2 : ℝ) ^ u) c := by
  have htR : (0 : ℝ) < t := by exact_mod_cast ht
  have hexp : -b ≤ (-((u + c + 1 : ℕ) : ℝ)) * (1 / (t : ℝ)) := by
    rw [mul_one_div, le_div_iff₀ htR]
    linarith
  calc
    (2 : ℝ) ^ (-b) ≤ (2 : ℝ) ^
        ((-((u + c + 1 : ℕ) : ℝ)) * (1 / (t : ℝ))) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
    _ = ((2 : ℝ) ^ (-((u + c + 1 : ℕ) : ℝ))) ^ (1 / (t : ℝ)) :=
      Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2) _ _
    _ ≤ yLoss ε t (1 / (2 : ℝ) ^ u) c :=
      Real.rpow_le_rpow (by positivity) (ratio_lower hε0 hε1 u c) (by positivity)

/-- The reciprocal power density always gives an upper bound of one. -/
theorem yLoss_le_one {ε : ℝ} (hε0 : 0 ≤ ε) (t u c : ℕ) :
    yLoss ε t (1 / (2 : ℝ) ^ u) c ≤ 1 := by
  apply yLoss_le_one_of_le_one (by positivity) _ hε0
  exact (div_le_one (by positivity : 0 < (2 : ℝ) ^ u)).mpr
    (one_le_pow₀ (by norm_num))

/-- A deliberately loose polynomial-versus-exponential estimate. -/
theorem linear_le_two_pow {s : ℕ} (hs : 128 ≤ s) : 16 * s + 16 ≤ 2 ^ s := by
  induction s, hs using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
      rw [pow_succ]
      nlinarith

/-- The first indexing call retains strictly more than half of its alphabet. -/
theorem indexing_density {s : ℕ} {ε : ℝ} (hs : 128 ≤ s)
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    1 / 2 < yLoss ε (64 * 2 ^ s) (1 / (2 : ℝ) ^ (3 * 2 ^ s))
      ((2 * s + 1) + 1) ∧
    yLoss ε (64 * 2 ^ s) (1 / (2 : ℝ) ^ (3 * 2 ^ s))
      ((2 * s + 1) + 1) ≤ 1 := by
  refine ⟨?_, yLoss_le_one hε0 _ _ _⟩
  apply NPCC.half_lt_yLoss (by positivity)
  have hlin := linear_le_two_pow hs
  have hexp : 3 * 2 ^ s + ((2 * s + 1) + 1) + 1 < 64 * 2 ^ s := by
    omega
  have hexpR : ((3 * 2 ^ s + ((2 * s + 1) + 1) + 1 : ℕ) : ℝ) <
      ((64 * 2 ^ s : ℕ) : ℝ) := by exact_mod_cast hexp
  exact (Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (neg_lt_neg hexpR)).trans_le
    (ratio_lower hε0 hε1 (3 * 2 ^ s) ((2 * s + 1) + 1))

/-- The second call's loss density is at least `2^(-s/2)`. The lower
width bound is exactly the rounded-up paper choice of `t₂`. -/
theorem coordinate_density {s m : ℕ} {ε : ℝ} (hs : 128 ≤ s)
    (hwidth : 3 * 2 ^ s ≤ s * 2 ^ m) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    (2 : ℝ) ^ (-(s : ℝ) / 2) ≤
      yLoss ε (2 ^ m) (1 / (2 : ℝ) ^ (3 * s)) ((2 * s + 1) + 1 + 2 ^ s) ∧
    yLoss ε (2 ^ m) (1 / (2 : ℝ) ^ (3 * s)) ((2 * s + 1) + 1 + 2 ^ s) ≤ 1 := by
  refine ⟨?_, yLoss_le_one hε0 _ _ _⟩
  have hlin := linear_le_two_pow hs
  have hbudget : 2 * (3 * s + ((2 * s + 1) + 1 + 2 ^ s) + 1) ≤ s * 2 ^ m := by
    omega
  have hbudgetR : (2 : ℝ) * ((3 * s + ((2 * s + 1) + 1 + 2 ^ s) + 1 : ℕ) : ℝ) ≤
      (s : ℝ) * ((2 ^ m : ℕ) : ℝ) := by exact_mod_cast hbudget
  have h := power_le_yLoss (b := (s : ℝ) / 2) hε0 hε1 (by positivity : 0 < 2 ^ m)
    (show ((3 * s + ((2 * s + 1) + 1 + 2 ^ s) + 1 : ℕ) : ℝ) ≤
      (s : ℝ) / 2 * ((2 ^ m : ℕ) : ℝ) by nlinarith)
  simpa only [neg_div] using h

/-- Enough row types survive the coordinate loss to contain the first
indexing stopping point, including the two duplicated row labels. -/
theorem coordinate_rows {s m : ℕ} {ε : ℝ} (hs : 128 ≤ s)
    (hwidth : 3 * 2 ^ s ≤ s * 2 ^ m) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    (36 : ℝ) * 2 ^ s + 2 ≤
      yLoss ε (2 ^ m) (1 / (2 : ℝ) ^ (3 * s)) ((2 * s + 1) + 1 + 2 ^ s) *
        (2 : ℝ) ^ (2 * s + 1) := by
  have hden := (coordinate_density hs hwidth hε0 hε1).1
  have hmul := mul_le_mul_of_nonneg_right hden
    (by positivity : 0 ≤ (2 : ℝ) ^ (2 * s + 1))
  have hprod : (2 : ℝ) ^ (-(s : ℝ) / 2) * (2 : ℝ) ^ (2 * s + 1) =
      (2 : ℝ) ^ (-(s : ℝ) / 2 + ((2 * s + 1 : ℕ) : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
  rw [hprod] at hmul
  push_cast at hmul
  have hsR : (128 : ℝ) ≤ s := by exact_mod_cast hs
  have hexp : ((s + 6 : ℕ) : ℝ) ≤ -(s : ℝ) / 2 + ((2 * s + 1 : ℕ) : ℝ) := by
    push_cast
    linarith
  have hpow := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hexp
  rw [Real.rpow_natCast, pow_add] at hpow
  norm_num at hpow
  have hr : (1 : ℝ) ≤ 2 ^ s := one_le_pow₀ (by norm_num)
  exact (show (36 : ℝ) * 2 ^ s + 2 ≤ (2 : ℝ) ^ s * 64 by linarith).trans
    (hpow.trans hmul)

end EthInapproximability.CurrentPaper.ExactLossGates
