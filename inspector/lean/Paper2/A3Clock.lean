import Mathlib

/-!
# Unit 3 endpoint assembly, segment 4 (clock conversion)

Lane `owner:a-h-a3-assembly-1` (private). Converts the clock-lane form `2^(c(k+1)L)`,
`L = Nat.clog 2 n`, into the H_A3 form `(n+2)^(E(k+1))` with `E = 2c`. Pure arithmetic.
-/

namespace Paper2.A3Assembly.Clock

/-- `2^(clog 2 n) ≤ (n+2)^2` for every `n`. -/
theorem two_pow_clog_le (n : ℕ) : 2 ^ Nat.clog 2 n ≤ (n + 2) ^ 2 := by
  rcases Nat.lt_or_ge n 2 with hn | hn
  · have h0 : Nat.clog 2 n = 0 := Nat.clog_of_right_le_one (by omega) 2
    rw [h0]
    exact Nat.one_le_pow _ _ (by omega)
  · have hpos : 0 < Nat.clog 2 n := Nat.clog_pos (by omega) (by omega)
    have hlt : 2 ^ (Nat.clog 2 n).pred < n := Nat.pow_pred_clog_lt_self (by omega) (by omega)
    have heq : 2 ^ Nat.clog 2 n = 2 * 2 ^ (Nat.clog 2 n).pred := by
      rw [← pow_succ']
      congr 1
      exact (Nat.succ_pred_eq_of_pos hpos).symm
    rw [heq]
    nlinarith

/-- The clock-lane bound in the H_A3 exponent form. -/
theorem two_pow_mul_clog_le (c k n : ℕ) :
    2 ^ (c * (k + 1) * Nat.clog 2 n) ≤ (n + 2) ^ ((2 * c) * (k + 1)) := by
  have h := two_pow_clog_le n
  calc 2 ^ (c * (k + 1) * Nat.clog 2 n)
      = (2 ^ Nat.clog 2 n) ^ (c * (k + 1)) := by rw [← pow_mul, Nat.mul_comm]
    _ ≤ ((n + 2) ^ 2) ^ (c * (k + 1)) := Nat.pow_le_pow_left h _
    _ = (n + 2) ^ ((2 * c) * (k + 1)) := by rw [← pow_mul]; ring_nf

/-- A clock `A · 2^(c(k+1)L)` is within `A · (n+2)^((2c)(k+1))`. -/
theorem clock_convert (A c k n : ℕ) :
    A * 2 ^ (c * (k + 1) * Nat.clog 2 n) ≤ A * (n + 2) ^ ((2 * c) * (k + 1)) :=
  Nat.mul_le_mul_left A (two_pow_mul_clog_le c k n)

end Paper2.A3Assembly.Clock

#print axioms Paper2.A3Assembly.Clock.two_pow_clog_le
#print axioms Paper2.A3Assembly.Clock.two_pow_mul_clog_le
#print axioms Paper2.A3Assembly.Clock.clock_convert
