import Mathlib

/-!
# Polynomial source padding for the exact reduction

Source: locked v8 `03-exact-hardness.tex`, the five-copy edge encoding and
polynomial-time reduction; `E-exact-details.tex`, the fixed lower cutoff.
The slightly sparser allowed dimensions `d = 2^(2^s)` retain polynomial
growth while making the numerical parameter formulas exact.
-/

namespace EthInapproximability.CurrentPaper.ExactSourcePadding

/-- The exponent selected from the number of original graph edges. -/
def paddedExponent (edges : ℕ) : ℕ :=
  max (2 ^ 21) (Nat.clog 2 (Nat.clog 2 (max 1 (5 * edges))))

/-- The dimension supplies a coordinate for every edge in five graph copies. -/
def paddedDimension (edges : ℕ) : ℕ := 2 ^ (2 ^ paddedExponent edges)

/-- A fixed constant, independent of the source graph. -/
def paddingConstant : ℕ := 2 ^ (2 ^ (2 ^ 21))

theorem cutoff (edges : ℕ) : 2 ^ 21 ≤ paddedExponent edges := le_max_left _ _

theorem dimension_pos (edges : ℕ) : 0 < paddedDimension edges := by
  unfold paddedDimension
  positivity

/-- Coverage includes the zero-edge case without taking a logarithm of zero. -/
theorem coverage (edges : ℕ) : 5 * edges ≤ paddedDimension edges := by
  calc
    5 * edges ≤ max 1 (5 * edges) := le_max_right _ _
    _ ≤ 2 ^ Nat.clog 2 (max 1 (5 * edges)) := Nat.le_pow_clog (by norm_num) _
    _ ≤ 2 ^ (2 ^ Nat.clog 2 (Nat.clog 2 (max 1 (5 * edges)))) :=
      Nat.pow_le_pow_right (by norm_num) (Nat.le_pow_clog (by norm_num) _)
    _ ≤ paddedDimension edges := by
      apply Nat.pow_le_pow_right (by norm_num)
      apply Nat.pow_le_pow_right (by norm_num)
      exact le_max_right _ _

/-- Rounding a positive integer up to a power of two loses at most factor two. -/
theorem pow_clog_le_twice {q : ℕ} (hq : 0 < q) : 2 ^ Nat.clog 2 q ≤ 2 * q := by
  by_cases hq1 : q = 1
  · subst q
    norm_num
  have hq2 : 1 < q := by omega
  have hk : 0 < Nat.clog 2 q := Nat.clog_pos (by norm_num) hq2
  have hpred := Nat.pow_pred_clog_lt_self (by norm_num : 1 < 2) hq2
  calc
    2 ^ Nat.clog 2 q = 2 ^ ((Nat.clog 2 q).pred + 1) := by
      congr 1
      simp only [Nat.pred_eq_sub_one]
      omega
    _ = 2 ^ (Nat.clog 2 q).pred * 2 := pow_succ _ _
    _ ≤ 2 * q := by omega

/-- Two rounds of dyadic rounding give a quadratic size bound. -/
theorem double_rounding_le_square {q : ℕ} (hq : 0 < q) :
    2 ^ (2 ^ Nat.clog 2 (Nat.clog 2 q)) ≤ (2 * q) ^ 2 := by
  by_cases hq1 : q = 1
  · subst q
    norm_num
  have hq2 : 1 < q := by omega
  have hk : 0 < Nat.clog 2 q := Nat.clog_pos (by norm_num) hq2
  calc
    2 ^ (2 ^ Nat.clog 2 (Nat.clog 2 q)) ≤ 2 ^ (2 * Nat.clog 2 q) :=
      Nat.pow_le_pow_right (by norm_num) (pow_clog_le_twice hk)
    _ = (2 ^ Nat.clog 2 q) ^ 2 := by rw [mul_comm 2 _, pow_mul]
    _ ≤ (2 * q) ^ 2 := Nat.pow_le_pow_left (pow_clog_le_twice hq) _

/-- The source dimension is bounded by a fixed cutoff or a quadratic
polynomial in the input edge count. -/
theorem dimension_le_max (edges : ℕ) :
    paddedDimension edges ≤ max paddingConstant ((2 * max 1 (5 * edges)) ^ 2) := by
  by_cases hs : Nat.clog 2 (Nat.clog 2 (max 1 (5 * edges))) ≤ 2 ^ 21
  · unfold paddedDimension paddedExponent
    rw [max_eq_left hs]
    exact le_max_left _ _
  · have hs' : 2 ^ 21 ≤ Nat.clog 2 (Nat.clog 2 (max 1 (5 * edges))) := by omega
    unfold paddedDimension paddedExponent
    rw [max_eq_right hs']
    exact (double_rounding_le_square (by omega : 0 < max 1 (5 * edges))).trans
      (le_max_right _ _)

private theorem max_le_product (C q : ℕ) (hC : 1 ≤ C) (hq : 1 ≤ q) :
    max C q ≤ C * q := by
  apply max_le <;> nlinarith

/-- A conventional fixed-coefficient polynomial upper bound. -/
theorem dimension_le_polynomial (edges : ℕ) :
    paddedDimension edges ≤ paddingConstant * ((2 * max 1 (5 * edges)) ^ 2) := by
  exact (dimension_le_max edges).trans
    (max_le_product paddingConstant ((2 * max 1 (5 * edges)) ^ 2)
      (Nat.one_le_pow (2 ^ (2 ^ 21)) 2 (by norm_num))
      (Nat.one_le_pow 2 (2 * max 1 (5 * edges)) (by omega)))

end EthInapproximability.CurrentPaper.ExactSourcePadding
