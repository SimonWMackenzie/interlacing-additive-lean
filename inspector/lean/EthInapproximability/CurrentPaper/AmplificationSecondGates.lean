import EthInapproximability.CurrentPaper.ParameterGates

/-!
# Scalar extraction conditions for the second amplification interlace

Source: locked v8 `F-parameter-choices.tex`,
`eq:paper-stage2-block-gates`, and `03-parameterized-construction.tex`,
`eq:paper-M2-aux-robust`. The literal accepted parameters supply the two
block counts and density bounds needed by the second-matrix profiles.
This module contains only scalar inequalities and imports no matrix profile.
-/

namespace EthInapproximability.CurrentPaper.AmplificationSecondGates

open Parameters

theorem balanceExponent_floor (i : Input) : 2 ^ 20 ≤ balanceExponent i := by
  have hs : 1 ≤ scale i := by have := scale_floor i; omega
  have hp : 1 ≤ scale i ^ 4 := one_le_pow₀ hs
  unfold balanceExponent
  norm_num
  omega

theorem balanceExponent_add_two_le_second (i : Input)
    (hc : 0 < i.sourceConstant) (ha : Accepted i) :
    balanceExponent i + 2 ≤ secondExponent i := by
  apply (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp
  have h := accepted_balance_four_le_second i hc ha
  simpa only [balanceOrder, secondWidth, pow_add,
    show (2 : ℕ) ^ 2 = 4 by norm_num, Nat.mul_comm] using h

/-- Scaling the integer hard-seed count is exactly the printed `9d/16`. -/
theorem scaled_copyCount_eq {m : ℕ} (hm : 5 ≤ m) (r : ℕ) :
    2 ^ r * HardSeed.copyCount m = 9 * 2 ^ (r + m) / 16 := by
  rw [← HardSeed.copyCount_eq (show 5 ≤ r + m by omega)]
  unfold HardSeed.copyCount
  rw [show r + m - 5 = r + (m - 5) by omega, pow_add]
  ring

/-- All scalar extraction inputs for both second-matrix profiles follow
from the two original acceptance tests and positivity of the source constant. -/
theorem scalar_gates (i : Input) (hc : 0 < i.sourceConstant) (ha : Accepted i) :
    let m := balanceExponent i
    let R := secondExponent i - m
    let x := (2 : ℝ) ^ (-(firstDepth i : ℝ))
    2 ^ 20 ≤ m ∧ 1 ≤ R ∧ secondWidth i = 2 ^ R * 2 ^ m ∧
      (2 : ℝ) ^ m * x ≤ 1 ∧ (2 : ℝ) ^ (R + m) * x < 1 ∧
      2 ^ R * HardSeed.copyCount m ≤
        ⌈(secondWidth i : ℝ) * ((3 / 5 : ℝ) - (2 : ℝ) ^ (R + m) * x) /
          (1 - (2 : ℝ) ^ (R + m) * x)⌉₊ ∧
      2 ^ (R - 1) * HardSeed.copyCount m ≤
        ⌈(secondWidth i : ℝ) * ((3 / 10 : ℝ) - (2 : ℝ) ^ (R - 1 + m) * x) /
          (1 - (2 : ℝ) ^ (R - 1 + m) * x)⌉₊ := by
  dsimp only
  let m := balanceExponent i
  let k := secondExponent i
  let R := k - m
  let x := (2 : ℝ) ^ (-(firstDepth i : ℝ))
  change 2 ^ 20 ≤ m ∧ 1 ≤ R ∧ secondWidth i = 2 ^ R * 2 ^ m ∧
    (2 : ℝ) ^ m * x ≤ 1 ∧ (2 : ℝ) ^ (R + m) * x < 1 ∧
    2 ^ R * HardSeed.copyCount m ≤ _ ∧
    2 ^ (R - 1) * HardSeed.copyCount m ≤ _
  have hm : 2 ^ 20 ≤ m := balanceExponent_floor i
  have hmk : m + 2 ≤ k := balanceExponent_add_two_le_second i hc ha
  have hR : 1 ≤ R := by dsimp [R]; omega
  have hsum : R + m = k := by dsimp [R]; omega
  have hhalf : R - 1 + m = k - 1 := by omega
  have hwidth : secondWidth i = 2 ^ R * 2 ^ m := by
    rw [← pow_add, hsum]
    rfl
  have hsmall : (2 : ℝ) ^ (R + m) * x < 1 := by
    have h := (ParameterGates.second_alpha_bounds i hc ha 0 (by omega)).2
    simp only [Nat.sub_zero, Nat.cast_zero, neg_zero, Real.rpow_zero] at h
    rw [hsum]
    exact h.trans_lt (by norm_num)
  have hrow : (2 : ℝ) ^ m * x ≤ 1 := by
    apply le_trans (mul_le_mul_of_nonneg_right
      (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (show m ≤ R + m by omega))
      (show 0 ≤ x by dsimp [x]; positivity)) hsmall.le
  refine ⟨hm, hR, hwidth, hrow, hsmall, ?_, ?_⟩
  · rw [scaled_copyCount_eq (show 5 ≤ m by omega), hsum]
    have h := (ParameterGates.second_extraction_gate i hc ha 0 (by omega)).2.2
    simpa only [Nat.sub_zero, Nat.cast_zero, neg_zero, Real.rpow_zero, mul_one,
      mul_div_assoc] using h
  · rw [scaled_copyCount_eq (show 5 ≤ m by omega), hhalf]
    have h := (ParameterGates.second_extraction_gate i hc ha 1 (by omega)).2.2
    norm_num only [Nat.cast_one, Real.rpow_neg_one] at h
    simpa only [mul_div_assoc] using h

end EthInapproximability.CurrentPaper.AmplificationSecondGates
