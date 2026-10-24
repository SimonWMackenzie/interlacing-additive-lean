import CurrentAdditive.GaussUniformMatrixSupport
import CurrentAdditive.GaussIterationBridge

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

namespace CurrentAdditive.GaussLoopBudgetEnvelope

open EthInapproximability.CurrentPaper
open CurrentAdditive.GaussNestedMatrixMap
open CurrentAdditive.GaussMatrixClockPolynomial

noncomputable def arithmeticTime (m M : Nat) : Nat :=
  polyMatrixTime GaussCellSubtractCall.machine m (m*M)
    (GaussUniformMatrixActual.requestCap m)
    (GaussUniformMatrixActual.resultCap m)
    (GaussCellGlobalClock.coefficient *
      (GaussUniformMatrixActual.requestCap m+1)^
        GaussUniformMatrixRun.exponent)

noncomputable def loopBudget (stepMachine : BitMachine.Machine)
    (m M : Nat) : Nat :=
  m*M * BitMachineIteration.roundBound stepMachine
    (GaussControlTrace.fullSupportStatePoly m M)
    (arithmeticTime m M) + 1

theorem sum_rounds_le (stepMachine : BitMachine.Machine)
    (m k M : Nat) (hk : k ≤ m*M) :
    k * BitMachineIteration.roundBound stepMachine
      (GaussControlTrace.fullSupportStatePoly m M)
      (arithmeticTime m M) + 1 ≤
      loopBudget stepMachine m M := by
  unfold loopBudget
  exact Nat.add_le_add_right (Nat.mul_le_mul_right _ hk) 1

theorem arithmeticTime_mono (m M n N : Nat)
    (hm : m ≤ n) (hM : M ≤ N) :
    arithmeticTime m M ≤ arithmeticTime n N := by
  have hk : m*M ≤ n*N := Nat.mul_le_mul hm hM
  have hL : GaussUniformMatrixActual.requestCap m ≤
      GaussUniformMatrixActual.requestCap n := by
    unfold GaussUniformMatrixActual.requestCap
      GaussUniformMatrixActual.entryCap
    gcongr
  have hR : GaussUniformMatrixActual.resultCap m ≤
      GaussUniformMatrixActual.resultCap n := by
    unfold GaussUniformMatrixActual.resultCap
      GaussUniformMatrixActual.entryCap
    gcongr
  have hT : GaussCellGlobalClock.coefficient *
      (GaussUniformMatrixActual.requestCap m+1)^
        GaussUniformMatrixRun.exponent ≤
      GaussCellGlobalClock.coefficient *
      (GaussUniformMatrixActual.requestCap n+1)^
        GaussUniformMatrixRun.exponent := by
    gcongr
  unfold arithmeticTime polyMatrixTime polyRowEnvelope polyRowFramed
    polyRowTime cellEnvelope cellFramedTime listBytes
  dsimp only
  gcongr

theorem stateLimit_mono (m M n N : Nat)
    (hm : m ≤ n) (hM : M ≤ N) :
    GaussControlTrace.fullSupportStatePoly m M ≤
      GaussControlTrace.fullSupportStatePoly n N := by
  unfold GaussControlTrace.fullSupportStatePoly
  gcongr

theorem loopBudget_mono (stepMachine : BitMachine.Machine)
    (m M n N : Nat) (hm : m ≤ n) (hM : M ≤ N) :
    loopBudget stepMachine m M ≤ loopBudget stepMachine n N := by
  have hk : m*M ≤ n*N := Nat.mul_le_mul hm hM
  have hL := stateLimit_mono m M n N hm hM
  have hT := arithmeticTime_mono m M n N hm hM
  unfold loopBudget BitMachineIteration.roundBound
  gcongr

theorem diagonal_majorant (stepMachine : BitMachine.Machine)
    (m k M : Nat) (hk : k ≤ m*M) :
    k * BitMachineIteration.roundBound stepMachine
      (GaussControlTrace.fullSupportStatePoly m M)
      (arithmeticTime m M) + 1 ≤
      loopBudget stepMachine (m+M+1) (m+M+1) := by
  exact (sum_rounds_le stepMachine m k M hk).trans
    (loopBudget_mono stepMachine m M (m+M+1) (m+M+1)
      (by omega) (by omega))

#print axioms diagonal_majorant

end CurrentAdditive.GaussLoopBudgetEnvelope
