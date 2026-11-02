import EthInapproximability.CurrentPaper.ETHParameterScaleMachineLogCopy
import EthInapproximability.CurrentPaper.MatrixUnaryPower
import EthInapproximability.CurrentPaper.BitMachineComposition
import Paper2.YaoLookupEvaluation

/-! One genuinely joined fixed machine stage: source-preserving unary
ceiling-logarithm followed by a charged transfer and unary power construction.
This is a strict subprogram of the intended entry-parameter loader, not yet
the complete bank setup for EntryCombined. -/

namespace Paper2.YaoParameterLoader

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachine
open EthInapproximability.CurrentPaper.BitMachineComposition
open Paper2.YaoLookup

noncomputable def logPowerMachine : Machine :=
  composition ETHParameterScaleMachineLogCopy.machine MatrixUnaryPower.machine

private theorem clog_max_one (e : ℕ) :
    Nat.clog 2 (max 1 e) = Nat.clog 2 e := by
  cases e with
  | zero => decide
  | succ e => simp

/-- One fixed finite Boolean-stack controller starts with only unary `e`,
copies it, physically computes `b=clog₂(max 1 e)`, reverses/transfers that
word between machine banks, and physically expands it to `H=2^b`. Both
intermediate transfer passes are included in the stated bound. -/
theorem log_power_outputs (e : ℕ) :
    logPowerMachine.OutputsWithin (List.replicate e true)
      (List.replicate (paddedEdgeCount e) true)
      (2*e+2 + (UnaryBinaryEncoding.coefficient+6)*(e+1)^2 +
        2*paddedEdgeBits e+2 + 16*paddedEdgeCount e) := by
  have hlog := ETHParameterScaleMachineLogCopy.outputs e
  have hpow := MatrixUnaryPower.outputs
    (List.replicate (Nat.clog 2 e) true)
  have hc := composition_outputsWithin
    ETHParameterScaleMachineLogCopy.machine MatrixUnaryPower.machine hlog hpow
  simpa only [logPowerMachine, List.length_replicate,
    paddedEdgeBits, paddedEdgeCount, clog_max_one] using hc

#print axioms log_power_outputs

end Paper2.YaoParameterLoader
