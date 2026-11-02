import CurrentAdditive.GaussLoopBudgetEnvelope
import CurrentAdditive.GaussInitialByteDimensions

namespace CurrentAdditive.GaussLoopOriginalBytes

open EthInapproximability.CurrentPaper

/-- A literal polynomial expression in the original encoded matrix length.
Its machine parameters and the arithmetic exponent are fixed. -/
noncomputable def byteBudget (stepMachine : BitMachine.Machine)
    (inputLength : Nat) : Nat :=
  let n := 2*(inputLength+1)
  GaussLoopBudgetEnvelope.loopBudget stepMachine n n

theorem columns_within_rows_times_columns (m k : Nat) (hm : 0 < m) :
    k ≤ m*k := by
  have h := Nat.mul_le_mul_right k (show 1 ≤ m by omega)
  simpa only [one_mul] using h

theorem actual_loop_budget_le_initial_bytes
    (stepMachine : BitMachine.Machine) {m k : Nat}
    (B : Fin m → Fin k → ℚ) (hm : 0 < m) :
    k * BitMachineIteration.roundBound stepMachine
      (GaussControlTrace.fullSupportStatePoly m k)
      (GaussLoopBudgetEnvelope.arithmeticTime m k) + 1 ≤
      byteBudget stepMachine (GaussPhysical.encodeTypedMatrix B).length := by
  let b := (GaussPhysical.encodeTypedMatrix B).length
  let n := 2*(b+1)
  have hrows : m ≤ b := GaussInitialByteDimensions.rows_le_initial_bytes B
  have hcols : k ≤ b := GaussInitialByteDimensions.columns_le_initial_bytes B hm
  have hmn : m ≤ n := by omega
  have hkn : k ≤ n := by omega
  calc
    _ ≤ GaussLoopBudgetEnvelope.loopBudget stepMachine m k :=
      GaussLoopBudgetEnvelope.sum_rounds_le stepMachine m k k
        (columns_within_rows_times_columns m k hm)
    _ ≤ GaussLoopBudgetEnvelope.loopBudget stepMachine n n :=
      GaussLoopBudgetEnvelope.loopBudget_mono stepMachine m k n n hmn hkn
    _ = byteBudget stepMachine (GaussPhysical.encodeTypedMatrix B).length := rfl

#print axioms actual_loop_budget_le_initial_bytes

end CurrentAdditive.GaussLoopOriginalBytes
