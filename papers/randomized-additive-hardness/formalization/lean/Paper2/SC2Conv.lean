import Mathlib

/-! Lane a-success-clock-owner-2, segment (5), conversion: at `L = clog₂ n`,
`2^(c (k+1) L) ≤ 1 * (n + 2)^((2c) (k+1))`, the clock shape of the H-A3 interface
(`CA * (g.vertices + 2) ^ (EA * (k + 1))`). Pure arithmetic. -/

namespace Paper2.SuccessClock2

theorem two_pow_clog_le (n : ℕ) : 2 ^ Nat.clog 2 n ≤ (n + 2) ^ 2 := by
  rcases Nat.lt_or_ge n 2 with h | h
  · rw [Nat.clog_of_right_le_one (by omega)]; nlinarith
  · have h1 := Nat.pow_pred_clog_lt_self (b := 2) (by norm_num) (x := n) (by omega)
    have h0 := Nat.clog_pos (b := 2) (by norm_num) (n := n) (by omega)
    have hp : (Nat.clog 2 n).pred + 1 = Nat.clog 2 n := Nat.succ_pred_eq_of_pos h0
    have e : 2 ^ Nat.clog 2 n = 2 * 2 ^ (Nat.clog 2 n).pred := by
      rw [← pow_succ', hp]
    rw [e]; nlinarith

/-- The conversion into the H-A3 clock shape. -/
theorem clock_conv (c k n : ℕ) :
    2 ^ (c * (k + 1) * Nat.clog 2 n) ≤ 1 * (n + 2) ^ ((2 * c) * (k + 1)) := by
  have h := Nat.pow_le_pow_left (two_pow_clog_le n) (c * (k + 1))
  rw [← pow_mul, ← pow_mul] at h
  rw [one_mul]
  calc 2 ^ (c * (k + 1) * Nat.clog 2 n) = 2 ^ (Nat.clog 2 n * (c * (k + 1))) := by ring_nf
    _ ≤ (n + 2) ^ (2 * (c * (k + 1))) := h
    _ = (n + 2) ^ ((2 * c) * (k + 1)) := by ring_nf

end Paper2.SuccessClock2

#print axioms Paper2.SuccessClock2.two_pow_clog_le
#print axioms Paper2.SuccessClock2.clock_conv
