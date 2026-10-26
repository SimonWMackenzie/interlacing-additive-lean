import Paper2.A3Front
import Paper2.A3Clock

/-! Unit 3, lane a-success-table-13, segment (3), part A: generic clock arithmetic and the `lBd` block.
Pure arithmetic: every block clock is bounded by a power of one abstract base `V` from atom bounds. -/

set_option maxHeartbeats 16000000
set_option maxRecDepth 16384

namespace Paper2.FrontClock13

open EthInapproximability.CurrentPaper

theorem clog_le' (v : ℕ) : Nat.clog 2 v ≤ v := Nat.clog_le_of_le_pow (Nat.lt_two_pow_self).le

theorem pw {V i j : ℕ} (hV : 1 ≤ V) (h : i ≤ j) : V ^ i ≤ V ^ j := Nat.pow_le_pow_right hV h

theorem mulb {x y V i j : ℕ} (hx : x ≤ V ^ i) (hy : y ≤ V ^ j) : x * y ≤ V ^ (i + j) := by
  rw [pow_add]; exact Nat.mul_le_mul hx hy

theorem cV {c V i : ℕ} (hc : c ≤ V) : c * V ^ i ≤ V ^ (i + 1) := by
  rw [pow_succ, Nat.mul_comm (V ^ i) V]; exact Nat.mul_le_mul_right _ hc

/-- `e² ≤ 2^(e-1) + 9`. -/
theorem sq_le_pow (e : ℕ) : e * e ≤ 2 ^ (e - 1) + 9 := by
  induction e with
  | zero => simp
  | succ e ih =>
    rcases Nat.lt_or_ge e 5 with h | h
    · interval_cases e <;> norm_num
    · have h2 : 2 * e + 1 ≤ 2 ^ (e - 1) := by
        clear ih
        induction e with
        | zero => omega
        | succ e ih2 =>
          rcases Nat.lt_or_ge e 5 with h' | h'
          · interval_cases e <;> omega
          · have := ih2 h'
            have e1 : 2 ^ (e + 1 - 1) = 2 * 2 ^ (e - 1) := by
              rw [show e + 1 - 1 = (e - 1) + 1 by omega, pow_succ]; ring
            omega
      have e1 : 2 ^ (e + 1 - 1) = 2 * 2 ^ (e - 1) := by
        rw [show e + 1 - 1 = (e - 1) + 1 by omega, pow_succ]; ring
      nlinarith

/-- `(clog₂ (L+1))² ≤ L + 9`. -/
theorem clog_sq_le (L : ℕ) : Nat.clog 2 (L + 1) * Nat.clog 2 (L + 1) ≤ L + 9 := by
  have h := sq_le_pow (Nat.clog 2 (L + 1))
  rcases Nat.lt_or_ge L 1 with hL | hL
  · have : L = 0 := by omega
    subst this; simp
  · have hp : 2 ^ (Nat.clog 2 (L + 1)).pred < L + 1 := Nat.pow_pred_clog_lt_self (by omega) (by omega)
    rw [Nat.pred_eq_sub_one] at hp
    omega

/-- `2 ^ clog₂ v ≤ (v + 2)²`, in the base form. -/
theorem two_pow_clog_V {v V i : ℕ} (hV : 2 ≤ V) (hv : v ≤ V ^ i) : 2 ^ Nat.clog 2 v ≤ V ^ (2 * i + 4) := by
  have h := Paper2.A3Assembly.Clock.two_pow_clog_le v
  have h1 : V ^ i + 2 ≤ V ^ (i + 2) := by
    have hp : 1 ≤ V ^ i := Nat.one_le_pow _ _ (by omega)
    have e3 : V ^ (i + 2) = V ^ i * (V * V) := by ring
    have h4 : 4 ≤ V * V := Nat.mul_le_mul hV hV
    have h5 := Nat.mul_le_mul_left (V ^ i) h4
    rw [e3]; omega
  have h2 : (v + 2) ^ 2 ≤ (V ^ (i + 2)) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  calc 2 ^ Nat.clog 2 v ≤ (v + 2) ^ 2 := h
    _ ≤ (V ^ (i + 2)) ^ 2 := h2
    _ = V ^ (2 * i + 4) := by rw [← pow_mul]; ring_nf

/-! ### The `lBd` block -/

theorem lBd_le (n V : ℕ) (hV : 2 ^ 32 ≤ V) (hc : UnaryBinaryEncoding.coefficient + 6 ≤ V) (hn : n + 3 ≤ V)
    (hL : 2 ^ Nat.clog 2 n ≤ V) (he : 2 ^ Nat.clog 2 (Nat.clog 2 n + 1) ≤ V)
    (hee : 2 ^ (Nat.clog 2 (Nat.clog 2 n + 1) * Nat.clog 2 (Nat.clog 2 n + 1)) ≤ V ^ 2) :
    LProducer.lBd n ≤ V ^ 6 := by
  have hLn : Nat.clog 2 n ≤ n := clog_le' n
  unfold LProducer.lBd LProducer.logBd MatrixAddressMachine.exactTime
  generalize Nat.clog 2 n = L at *
  have heL : Nat.clog 2 (L + 1) ≤ L + 1 := clog_le' _
  generalize Nat.clog 2 (L + 1) = e at *
  have hV1 : 1 ≤ V := by omega
  have t1 : (UnaryBinaryEncoding.coefficient + 6) * (n + 1) ^ 2 ≤ V ^ 3 := by
    have : (n + 1) ^ 2 ≤ V ^ 2 := Nat.pow_le_pow_left (by omega) 2
    have := Nat.mul_le_mul hc this
    calc _ ≤ V * V ^ 2 := this
      _ = V ^ 3 := by ring
  have t2 : (UnaryBinaryEncoding.coefficient + 6) * (L + 1 + 1) ^ 2 ≤ V ^ 3 := by
    have : (L + 1 + 1) ^ 2 ≤ V ^ 2 := Nat.pow_le_pow_left (by omega) 2
    have := Nat.mul_le_mul hc this
    calc _ ≤ V * V ^ 2 := this
      _ = V ^ 3 := by ring
  have t3 : 2 * e * e ≤ 2 * V ^ 2 := by
    have : e * e ≤ V * V := Nat.mul_le_mul (by omega) (by omega)
    have e2 : V ^ 2 = V * V := by ring
    rw [e2, Nat.mul_assoc]; omega
  have t3' : e * e ≤ V ^ 2 := by
    have : e * e ≤ V * V := Nat.mul_le_mul (by omega) (by omega)
    have e2 : V ^ 2 = V * V := by ring
    omega
  have t4 : 2 ^ (6 + e) ≤ 64 * V := by rw [pow_add]; omega
  have t5 : 2 ^ (16 + e) ≤ 65536 * V := by rw [pow_add]; omega
  have t6 : 2 ^ (32 + (e + (e + L))) ≤ 2 ^ 32 * V ^ 3 := by
    rw [pow_add, pow_add, pow_add]
    have : 2 ^ e * (2 ^ e * 2 ^ L) ≤ V ^ 3 := by
      have := Nat.mul_le_mul he (Nat.mul_le_mul he hL)
      calc _ ≤ V * (V * V) := this
        _ = V ^ 3 := by ring
    exact Nat.mul_le_mul_left _ this
  have s1 : 2 ^ 32 * V ^ 3 ≤ V ^ 4 := cV hV
  have s2 : V ^ 2 ≤ V ^ 3 := pw hV1 (by omega)
  have s3 : V ^ 3 ≤ V ^ 4 := pw hV1 (by omega)
  have s0 : V ≤ V ^ 2 := by
    have := pw (i := 1) (j := 2) hV1 (by omega); simpa using this
  have s4 : 65536 * V ≤ V ^ 2 := by
    have := cV (c := 65536) (i := 1) (V := V) (by omega); simpa using this
  have s5 : 1000 * V ^ 4 ≤ V ^ 5 := cV (by omega)
  have s6 : V ^ 5 ≤ V ^ 6 := pw hV1 (by omega)
  omega

end Paper2.FrontClock13

#print axioms Paper2.FrontClock13.clog_sq_le
#print axioms Paper2.FrontClock13.two_pow_clog_V
#print axioms Paper2.FrontClock13.lBd_le
