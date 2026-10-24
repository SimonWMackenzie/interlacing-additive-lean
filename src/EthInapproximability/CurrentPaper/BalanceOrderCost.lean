import EthInapproximability.CurrentPaper.BalanceOrderCleanup

/-! Output-sensitive charged clock for the physical balance-order program. -/

namespace EthInapproximability.CurrentPaper.BalanceOrderCost

open BalanceOrderArithmetic BalanceOrderCleanup

private theorem scale_le_exponent (s : ℕ) : s ≤ exponent s := by
  by_cases hs : s = 0
  · simp [hs, exponent]
  · have hp : s ≤ s^4 := Nat.le_self_pow (by decide : 4 ≠ 0) s
    unfold exponent
    omega

private theorem exponent_le_output (s : ℕ) :
    exponent s ≤ 2^(exponent s) :=
  Nat.le_of_lt Nat.lt_two_pow_self

private theorem scale_le_output (s : ℕ) :
    s ≤ 2^(exponent s) :=
  (scale_le_exponent s).trans (exponent_le_output s)

private theorem clearTime_eq (s : ℕ) :
    clearTime s = 10000 + 10000*s + 2*(10000*s^2) + exponent s + 7 := by
  have h0 : afterPower s (clearSlots 0) = unary 10000 := rfl
  have h1 : afterPower s (clearSlots (Fin.succ 0)) =
      unary (10000*s) := rfl
  have h2 : afterPower s (clearSlots (Fin.succ (Fin.succ 0))) =
      unary (10000*s^2) := rfl
  have h3 : afterPower s (clearSlots (Fin.succ (Fin.succ (Fin.succ 0)))) =
      unary (10000*s^2) := rfl
  have h4 : afterPower s (clearSlots
      (Fin.succ (Fin.succ (Fin.succ (Fin.succ 0))))) =
      unary (exponent s) := rfl
  unfold clearTime
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  rw [h0, h1, h2, h3, h4]
  simp only [List.length_replicate]
  omega

/-- The explicit clock is polynomial in the output word length alone.
The coefficient is intentionally generous; this does not claim a machine
runtime polynomial in the binary length of the enormous balance order. -/
theorem fullTime_output_bound (s : ℕ) :
    fullTime s ≤ 1000000000 * (2^(exponent s)+1)^2 := by
  have hs := scale_le_output s
  have he := exponent_le_output s
  have hc := clearTime_eq s
  have hsq : s^2 ≤ (2^(exponent s))^2 := Nat.pow_le_pow_left hs 2
  have hbig : 2*(10000*s^2)*(10000*s^2) = 2*exponent s := by
    unfold exponent; ring
  simp only [fullTime, arithmeticTime,
    ETHBinsCoefficientScratch.time, MatrixAddressMachine.exactTime] at *
  rw [hbig]
  nlinarith [hc]

#print axioms fullTime_output_bound

end EthInapproximability.CurrentPaper.BalanceOrderCost
