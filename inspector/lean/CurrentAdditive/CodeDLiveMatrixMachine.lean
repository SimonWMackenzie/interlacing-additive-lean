import CurrentAdditive.CodeDSourceTupleMachine
import CurrentAdditive.CodeDPacketRouting
import CurrentAdditive.OrdinaryPolynomialComposition
import CurrentAdditive.CylinderActualEvaluatorPolynomial
import EthInapproximability.CurrentPaper.BitMachineCopy

namespace CurrentAdditive.CodeDLiveMatrixMachine
noncomputable section
set_option maxRecDepth 16384
set_option maxHeartbeats 6000000
set_option synthInstance.maxSize 16384
open EthInapproximability.CurrentPaper
open CylinderFeatureCodec

def words (q D : Nat) (alphabet : Array Nat) (source : Array ((Fin q → Nat) × ℚ)) : Fin 3 → List Bool :=
  ![List.replicate q true,generatedFeatureBits q D alphabet,CodeDCanonicalSourceV2.encodedSource source]
def input (q D : Nat) (alphabet : Array Nat) (source : Array ((Fin q → Nat) × ℚ)) : List Bool :=
  BitMachineBankCodec.encode (words q D alphabet source)

abbrev S := BankFieldProjection.machine (2 : Fin 3)
abbrev T := CodeDSourceTupleMachine.machine
def tupleMachine := BitMachineComposition.composition S T
def tupleCoefficient := OrdinaryPolynomialComposition.coefficient S 10 CodeDSourceTupleMachine.coefficient 3
def tupleDegree := OrdinaryPolynomialComposition.degree 1 3

theorem tuple_outputs (q D : Nat) (alphabet : Array Nat) (source : Array ((Fin q → Nat) × ℚ)) :
    tupleMachine.OutputsWithin (input q D alphabet source)
      (SourceListEncoding.encode (CylinderProductionProjection.tupleWords source))
      (tupleCoefficient*((input q D alphabet source).length+1)^tupleDegree) := by
  have hs : S.OutputsWithin (input q D alphabet source)
      (CodeDCanonicalSourceV2.encodedSource source) (10*((input q D alphabet source).length+1)^1) := by
    simpa [input,words,BankFieldProjection.result_encode] using
      BankFieldProjection.outputs (2 : Fin 3) (input q D alphabet source)
  exact OrdinaryPolynomialComposition.outputsWithin S T hs (CodeDSourceTupleMachine.outputs source)

abbrev I := BitMachineCopy.bitMachine
def forkMachine := OrdinaryBankFork.machine I tupleMachine
def forkCoefficient := OrdinaryBankFork.coefficient I tupleMachine 2 tupleCoefficient
def forkDegree := OrdinaryBankFork.degree 1 tupleDegree
def routeMachine := BitMachineComposition.composition forkMachine CodeDPacketRouting.replaceLast.machine
def routeCoefficient := OrdinaryPolynomialComposition.coefficient forkMachine forkCoefficient
  CodeDPacketRouting.replaceLast.coefficient CodeDPacketRouting.replaceLast.degree
def routeDegree := OrdinaryPolynomialComposition.degree forkDegree CodeDPacketRouting.replaceLast.degree

theorem route_outputs (q D : Nat) (alphabet : Array Nat) (source : Array ((Fin q → Nat) × ℚ)) :
    routeMachine.OutputsWithin (input q D alphabet source)
      (CylinderActualMatrixEvaluator.input q D alphabet source)
      (routeCoefficient*((input q D alphabet source).length+1)^routeDegree) := by
  let x := input q D alphabet source
  let tuples := SourceListEncoding.encode (CylinderProductionProjection.tupleWords source)
  have hi : I.OutputsWithin x x (2*(x.length+1)^1) := by
    simpa only [pow_one] using BitMachineCopy.bitMachine_outputs x
  have hf := OrdinaryPolynomialComposition.fork_outputsWithin I tupleMachine hi
    (tuple_outputs q D alphabet source)
  have hr := CodeDPacketRouting.replaceLast_outputs (words q D alphabet source) tuples
  have h := OrdinaryPolynomialComposition.outputsWithin forkMachine CodeDPacketRouting.replaceLast.machine hf hr
  exact h

def machine := BitMachineComposition.composition routeMachine CylinderActualMatrixEvaluator.machine
def coefficient := OrdinaryPolynomialComposition.coefficient routeMachine routeCoefficient
  CylinderActualMatrixEvaluator.coefficient CylinderActualMatrixEvaluator.exponent
def exponent := OrdinaryPolynomialComposition.degree routeDegree CylinderActualMatrixEvaluator.exponent

/-- The weighted source is projected by an actual machine before the
actual descriptor evaluator computes every matrix entry. No tuple-only or
Boolean-row packet is supplied by the caller. -/
theorem outputs (q D : Nat) (alphabet : Array Nat) (source : Array ((Fin q → Nat) × ℚ)) :
    machine.OutputsWithin (input q D alphabet source)
      (cylinderMatrixBits q D alphabet source)
      (coefficient*((input q D alphabet source).length+1)^exponent) :=
  OrdinaryPolynomialComposition.outputsWithin routeMachine CylinderActualMatrixEvaluator.machine
    (route_outputs q D alphabet source) (CylinderActualMatrixEvaluator.outputs_polynomial q D alphabet source)

#print axioms tuple_outputs
#print axioms route_outputs
#print axioms outputs
end
end CurrentAdditive.CodeDLiveMatrixMachine
