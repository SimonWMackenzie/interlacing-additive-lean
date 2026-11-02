import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Data.Nat.Log
import Mathlib.Tactic

/-!
# Numeric budgets for Paper 2 sampling

Statement source: `2026-09-22-protocol-labels-v12`.

* `sections/02-compression.tex`, `eq:compression-sizes` and the two estimates
  in the proof of `thm:compression`.
* `appendices/D-implementation.tex`, the capped-draw budget and final error
  estimate in the proof of `thm:uniform-reduction`.
* `sections/06-reduction.tex`, the success margin in `thm:uniform-reduction`.

These are exact rational arithmetic results only. They do not assert the
protocol-domain count, sampling independence, union bound, coupling, or an
effective randomized reduction. Those require separate formal proofs.
-/

namespace Paper2

/-- Number of column draws in `eq:compression-sizes`. -/
def compressionColumnDraws (Z : ℕ) : ℕ := 2 * (Z + 12)

/-- Number of row draws; the denominator must be positive in applications. -/
def compressionRowDraws (Z L : ℕ) : ℕ := (Z + 12) ⌈/⌉ L

/-- The entropy parameter in `eq:compression-sizes`. -/
def compressionEntropy (r H : ℕ) : ℕ := (r * (r + 1) + 2) * 2 ^ (H - 1)

theorem compressionEntropy_pos (r H : ℕ) : 1 ≤ compressionEntropy r H := by
  unfold compressionEntropy
  exact Nat.mul_pos (by omega) (pow_pos (by decide) _)

/-- Positivity prevents the ceiling expression from silently using division by zero. -/
theorem compressionRowDraws_cover (Z L : ℕ) (hL : 1 ≤ L) :
    Z + 12 ≤ L * compressionRowDraws Z L := by
  exact (ceilDiv_le_iff_le_mul (by omega : 0 < L)).mp le_rfl

theorem compressionRowDraws_pos (Z L : ℕ) (hL : 1 ≤ L) :
    1 ≤ compressionRowDraws Z L := by
  have hc := compressionRowDraws_cover Z L hL
  by_contra hn
  have hz : compressionRowDraws Z L = 0 := by omega
  simp [hz] at hc

/-- Exact cancellation of the domain count against the dyadic sample mass. -/
theorem dyadic_sampling_cancellation (n slack : ℕ) :
    (2 : ℚ) ^ n * (1 / 2 : ℚ) ^ (n + slack) = (1 / 2 : ℚ) ^ slack := by
  rw [pow_add, ← mul_assoc, ← mul_pow]
  norm_num

/-- First numerical estimate in the proof of `thm:compression`. -/
theorem compression_column_error (Z : ℕ) (hZ : 1 ≤ Z) :
    (2 : ℚ) ^ (Z - 1) * (3 / 5 : ℚ) ^ compressionColumnDraws Z ≤
      (1 / 2 : ℚ) ^ 13 := by
  have he : Z + 12 = (Z - 1) + 13 := by omega
  calc
    (2 : ℚ) ^ (Z - 1) * (3 / 5 : ℚ) ^ compressionColumnDraws Z =
        (2 : ℚ) ^ (Z - 1) * ((3 / 5 : ℚ) ^ 2) ^ (Z + 12) := by
          rw [compressionColumnDraws, pow_mul]
    _ ≤ (2 : ℚ) ^ (Z - 1) * (1 / 2 : ℚ) ^ (Z + 12) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact pow_le_pow_left₀ (by norm_num) (by norm_num) _
    _ = (1 / 2 : ℚ) ^ 13 := by rw [he, dyadic_sampling_cancellation]

/-- Second numerical estimate in the proof of `thm:compression`. -/
theorem compression_row_error (Z L : ℕ) (hZ : 1 ≤ Z) (hL : 1 ≤ L) :
    (2 : ℚ) ^ (Z - 1) * (1 / 2 : ℚ) ^ (L * compressionRowDraws Z L) ≤
      (1 / 2 : ℚ) ^ 13 := by
  have he : Z + 12 = (Z - 1) + 13 := by omega
  calc
    (2 : ℚ) ^ (Z - 1) * (1 / 2 : ℚ) ^ (L * compressionRowDraws Z L) ≤
        (2 : ℚ) ^ (Z - 1) * (1 / 2 : ℚ) ^ (Z + 12) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact pow_le_pow_of_le_one (by norm_num) (by norm_num)
        (compressionRowDraws_cover Z L hL)
    _ = (1 / 2 : ℚ) ^ 13 := by rw [he, dyadic_sampling_cancellation]

/-- Addition of the two already-established one-sided numeric error budgets. -/
theorem compression_error_sum (Z L : ℕ) (hZ : 1 ≤ Z) (hL : 1 ≤ L) :
    (2 : ℚ) ^ (Z - 1) * (3 / 5 : ℚ) ^ compressionColumnDraws Z +
      (2 : ℚ) ^ (Z - 1) * (1 / 2 : ℚ) ^ (L * compressionRowDraws Z L) ≤
        (1 / 2 : ℚ) ^ 12 := by
  have hc := compression_column_error Z hZ
  have hr := compression_row_error Z L hZ hL
  norm_num at hc hr ⊢
  linarith

/-- Number of rejection attempts allocated to each elementary draw. -/
def rejectionAttemptCap (N : ℕ) : ℕ := Nat.clog 2 (2 ^ 12 * N) + 1

/-- The ceiling logarithm grants a factor `2^13` over the draw count. -/
theorem rejectionAttemptCap_cover (N : ℕ) :
    2 ^ 13 * N ≤ 2 ^ rejectionAttemptCap N := by
  have h := Nat.le_pow_clog (by decide : 1 < 2) (2 ^ 12 * N)
  unfold rejectionAttemptCap
  rw [pow_succ]
  norm_num at h ⊢
  omega

/-- Numeric union-bound budget for exhausting any capped rejection sampler. -/
theorem rejection_cap_error (N : ℕ) :
    (N : ℚ) * (1 / 2 : ℚ) ^ rejectionAttemptCap N ≤ (1 / 2 : ℚ) ^ 13 := by
  have hc : (2 : ℚ) ^ 13 * N ≤ (2 : ℚ) ^ rejectionAttemptCap N := by
    exact_mod_cast rejectionAttemptCap_cover N
  have hp : (0 : ℚ) < 2 ^ rejectionAttemptCap N := by positivity
  rw [one_div_pow]
  rw [mul_one_div]
  apply (div_le_iff₀ hp).mpr
  norm_num at hc ⊢
  linarith

/-- We retain the manuscript's conservative combined error constant. -/
theorem total_sampling_error {compressionError abortError : ℚ}
    (hc : compressionError ≤ (1 / 2 : ℚ) ^ 12)
    (ha : abortError ≤ (1 / 2 : ℚ) ^ 12) :
    compressionError + abortError ≤ (1 / 2 : ℚ) ^ 11 := by
  norm_num at hc ha ⊢
  linarith

/-- The actual column, row, and capped-draw budgets satisfy the final error bound. -/
theorem concrete_total_sampling_error (Z L N : ℕ) (hZ : 1 ≤ Z) (hL : 1 ≤ L) :
    (2 : ℚ) ^ (Z - 1) * (3 / 5 : ℚ) ^ compressionColumnDraws Z +
      (2 : ℚ) ^ (Z - 1) * (1 / 2 : ℚ) ^ (L * compressionRowDraws Z L) +
      (N : ℚ) * (1 / 2 : ℚ) ^ rejectionAttemptCap N ≤ (1 / 2 : ℚ) ^ 11 := by
  apply total_sampling_error (compression_error_sum Z L hZ hL)
  exact (rejection_cap_error N).trans (by norm_num)

/-- The final success margin is strictly greater than `0.981`. -/
theorem sampling_success_margin {failure : ℚ}
    (hf : failure ≤ (1 / 2 : ℚ) ^ 11) :
    (981 / 1000 : ℚ) < 1 - failure := by
  norm_num at hf ⊢
  linarith

/-! The probability layer uses real weights; these are the same constants
transported from the exact rational proofs, not numerical approximations. -/

theorem compression_column_error_real (Z : ℕ) (hZ : 1 ≤ Z) :
    (2 : ℝ) ^ (Z - 1) * (3 / 5 : ℝ) ^ compressionColumnDraws Z ≤
      (1 / 2 : ℝ) ^ 13 := by
  have h := (Rat.cast_le (K := ℝ)).2 (compression_column_error Z hZ)
  simpa only [Rat.cast_mul, Rat.cast_pow, Rat.cast_div, Rat.cast_ofNat, Rat.cast_one] using h

theorem compression_row_error_real (Z L : ℕ) (hZ : 1 ≤ Z) (hL : 1 ≤ L) :
    (2 : ℝ) ^ (Z - 1) * (1 / 2 : ℝ) ^ (L * compressionRowDraws Z L) ≤
      (1 / 2 : ℝ) ^ 13 := by
  have h := (Rat.cast_le (K := ℝ)).2 (compression_row_error Z L hZ hL)
  simpa only [Rat.cast_mul, Rat.cast_pow, Rat.cast_div, Rat.cast_ofNat, Rat.cast_one] using h

/-- The row estimate written as the mass of one domain raised to the draw count. -/
theorem compression_row_error_mass_real (Z L : ℕ) (hZ : 1 ≤ Z) (hL : 1 ≤ L) :
    (2 : ℝ) ^ (Z - 1) * ((1 / 2 : ℝ) ^ L) ^ compressionRowDraws Z L ≤
      (1 / 2 : ℝ) ^ 13 := by
  simpa only [pow_mul] using compression_row_error_real Z L hZ hL

theorem compression_error_sum_real (Z L : ℕ) (hZ : 1 ≤ Z) (hL : 1 ≤ L) :
    (2 : ℝ) ^ (Z - 1) * (3 / 5 : ℝ) ^ compressionColumnDraws Z +
      (2 : ℝ) ^ (Z - 1) * (1 / 2 : ℝ) ^ (L * compressionRowDraws Z L) ≤
        (1 / 2 : ℝ) ^ 12 := by
  have h := (Rat.cast_le (K := ℝ)).2 (compression_error_sum Z L hZ hL)
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_pow, Rat.cast_div, Rat.cast_ofNat,
    Rat.cast_one] using h

theorem rejection_cap_error_real (N : ℕ) :
    (N : ℝ) * (1 / 2 : ℝ) ^ rejectionAttemptCap N ≤ (1 / 2 : ℝ) ^ 13 := by
  have h := (Rat.cast_le (K := ℝ)).2 (rejection_cap_error N)
  simpa only [Rat.cast_mul, Rat.cast_pow, Rat.cast_div, Rat.cast_ofNat, Rat.cast_one,
    Rat.cast_natCast] using h

theorem total_sampling_error_real {compressionError abortError : ℝ}
    (hc : compressionError ≤ (1 / 2 : ℝ) ^ 12)
    (ha : abortError ≤ (1 / 2 : ℝ) ^ 12) :
    compressionError + abortError ≤ (1 / 2 : ℝ) ^ 11 := by
  norm_num at hc ha ⊢
  linarith

theorem concrete_total_sampling_error_real (Z L N : ℕ) (hZ : 1 ≤ Z) (hL : 1 ≤ L) :
    (2 : ℝ) ^ (Z - 1) * (3 / 5 : ℝ) ^ compressionColumnDraws Z +
      (2 : ℝ) ^ (Z - 1) * (1 / 2 : ℝ) ^ (L * compressionRowDraws Z L) +
      (N : ℝ) * (1 / 2 : ℝ) ^ rejectionAttemptCap N ≤ (1 / 2 : ℝ) ^ 11 := by
  have h := (Rat.cast_le (K := ℝ)).2 (concrete_total_sampling_error Z L N hZ hL)
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_pow, Rat.cast_div, Rat.cast_ofNat,
    Rat.cast_one, Rat.cast_natCast] using h

theorem sampling_success_margin_real {failure : ℝ}
    (hf : failure ≤ (1 / 2 : ℝ) ^ 11) :
    (981 / 1000 : ℝ) < 1 - failure := by
  norm_num at hf ⊢
  linarith

end Paper2
