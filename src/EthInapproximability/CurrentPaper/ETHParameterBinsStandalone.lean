import EthInapproximability.CurrentPaper.ETHParameterBinsCoefficient
import EthInapproximability.CurrentPaper.ExactParameterMachineLog
import EthInapproximability.CurrentPaper.ExactParameterMachineSquare
import EthInapproximability.CurrentPaper.MatrixUnaryPower
import EthInapproximability.CurrentPaper.BitMachineComposition
import EthInapproximability.CurrentPaper.Parameters

/-! A fixed physical chain for u = clog₂(scale), 10000*u², and 2^(10000*u²).
Each stage consumes the unary output of the previous stage through the
charged two-pass stack transfer in BitMachineComposition. -/

namespace EthInapproximability.CurrentPaper.ETHBinsStandaloneScratch

open BitMachineComposition

noncomputable section

def unary (n : ℕ) : List Bool := List.replicate n true
def aux (n : ℕ) : ℕ := Nat.clog 2 n
def exponent (n : ℕ) : ℕ := 10000*(aux n)^2
def bins (n : ℕ) : ℕ := 2^exponent n

noncomputable def logMachine : BitMachine.Machine := ExactParameterMachineLog.machine
noncomputable def squareMachine : BitMachine.Machine := ExactParameterMachineSquare.squareMachine
noncomputable def coefficientMachine : BitMachine.Machine := ETHBinsCoefficientScratch.machine
noncomputable def powerMachine : BitMachine.Machine := MatrixUnaryPower.machine
noncomputable def logSquareMachine : BitMachine.Machine := composition logMachine squareMachine
noncomputable def exponentMachine : BitMachine.Machine :=
  composition logSquareMachine coefficientMachine
noncomputable def machine : BitMachine.Machine :=
  composition exponentMachine powerMachine

def logTime (n : ℕ) : ℕ :=
  (UnaryBinaryEncoding.coefficient+6)*(n+1)^2
def squareTime (u : ℕ) : ℕ :=
  2*u+2 + 2*(2*u+1)+2 + 2*(2*u+2)^2
def exponentTime (n : ℕ) : ℕ :=
  logTime n + 2*aux n+2 + squareTime (aux n) +
    2*(aux n)^2+2 + ETHBinsCoefficientScratch.time ((aux n)^2)
def totalTime (n : ℕ) : ℕ :=
  exponentTime n + 2*exponent n+2 + 16*bins n

theorem log_outputs (n : ℕ) :
    logMachine.OutputsWithin (unary n) (unary (aux n)) (logTime n) := by
  simpa only [logMachine,unary,aux,logTime] using ExactParameterMachineLog.outputs n

theorem square_outputs (u : ℕ) :
    squareMachine.OutputsWithin (unary u) (unary (u^2)) (squareTime u) := by
  simpa only [squareMachine,unary,squareTime] using
    ExactParameterMachineSquare.square_outputs u

theorem coefficient_outputs (u : ℕ) :
    coefficientMachine.OutputsWithin (unary (u^2))
      (unary (10000*u^2)) (ETHBinsCoefficientScratch.time (u^2)) := by
  simpa only [coefficientMachine,unary] using ETHBinsCoefficientScratch.outputs (u^2)

/-- Actual unary auxiliary logarithm and its square are the two successive
outputs of this machine prefix, not separately supplied input data. -/
theorem log_square_outputs (n : ℕ) :
    logSquareMachine.OutputsWithin (unary n) (unary ((aux n)^2))
      (logTime n + 2*aux n+2 + squareTime (aux n)) := by
  have h := composition_outputsWithin logMachine squareMachine
    (log_outputs n) (square_outputs (aux n))
  simpa only [logSquareMachine,unary,List.length_replicate] using h

/-- The literal 10000 coefficient is emitted by fixed syntax and multiplied
by the produced square. No exponent word is assumed. -/
theorem exponent_outputs (n : ℕ) :
    exponentMachine.OutputsWithin (unary n) (unary (exponent n))
      (exponentTime n) := by
  have h := composition_outputsWithin logSquareMachine coefficientMachine
    (log_square_outputs n) (coefficient_outputs (aux n))
  simpa only [exponentMachine,exponentTime,exponent,unary,
    List.length_replicate] using h

/-- Physical power emission costs at most a fixed multiple of its output
length, in addition to logarithm, square, coefficient and transfers. -/
theorem bins_outputs (n : ℕ) :
    machine.OutputsWithin (unary n) (unary (bins n)) (totalTime n) := by
  have hp := MatrixUnaryPower.outputs (unary (exponent n))
  have h := composition_outputsWithin exponentMachine powerMachine
    (exponent_outputs n) hp
  simpa only [machine,powerMachine,totalTime,bins,unary,
    List.length_replicate] using h

theorem bins_eq_parameters (i : Parameters.Input) :
    bins (Parameters.scale i) = Parameters.bins i := rfl
theorem exponent_eq_parameters (i : Parameters.Input) :
    exponent (Parameters.scale i) = Parameters.binExponent i := rfl
theorem aux_eq_parameters (i : Parameters.Input) :
    aux (Parameters.scale i) = Parameters.auxiliaryLog i := rfl


end
end EthInapproximability.CurrentPaper.ETHBinsStandaloneScratch
