import CurrentAdditive.FeatureRawPolynomial96
import CurrentAdditive.FeatureFinalAssemblerClock96
import CurrentAdditive.CylinderActualEvaluatorPolynomial

/-! The complete fixed physical cylinder matrix producer from the original
weighted alphabet/source packet. The result is the literal 0/1 matrix word
consumed by Code D, with a polynomial clock in that same original input. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option synthInstance.maxSize 65536
set_option maxRecDepth 4096
namespace CurrentAdditive.CylinderRawMatrixProducer
open EthInapproximability.CurrentPaper

def input {q : Nat} (alphabet : Array (Nat × ℚ))
    (source : Array ((Fin q → Nat) × ℚ)) := CylinderRawInputProjection.input alphabet source

def preparedWord {q : Nat} (alphabet : Array (Nat × ℚ))
    (source : Array ((Fin q → Nat) × ℚ)) :=
  CylinderActualMatrixEvaluator.input q 8192 (alphabet.map Prod.fst) source

def preparedMachine : BitMachine.Machine := BitMachineComposition.composition
  FeatureRawEnumeration96.stateMachine FeatureFinalAssembler96.machine

def preparedCoefficient : Nat := FeaturePhysicalCompositionBounds.inputCoefficient
  FeatureRawPolynomial96.stateCoefficient FeatureFinalAssemblerClock96.coefficient
  FeatureFinalAssemblerClock96.exponent FeatureRawEnumeration96.stateMachine.pushBound
def preparedExponent : Nat := FeaturePhysicalCompositionBounds.inputExponent
  FeatureRawPolynomial96.stateExponent FeatureFinalAssemblerClock96.exponent

theorem prepared_outputs_polynomial {q : Nat} (alphabet : Array (Nat × ℚ))
    (source : Array ((Fin q → Nat) × ℚ)) :
    preparedMachine.OutputsWithin (input alphabet source) (preparedWord alphabet source)
      (preparedCoefficient*((input alphabet source).length+1)^preparedExponent) := by
  exact FeaturePhysicalCompositionBounds.outputs_input_clock _ _ (input alphabet source)
    (FeatureGeneratedIteration96.states (alphabet.map Prod.fst).toList (input alphabet source) q)
    (preparedWord alphabet source)
    FeatureRawPolynomial96.stateCoefficient FeatureRawPolynomial96.stateExponent
    FeatureFinalAssemblerClock96.coefficient FeatureFinalAssemblerClock96.exponent
    (FeatureRawPolynomial96.state_outputs_polynomial alphabet source)
    (FeatureFinalAssemblerClock96.outputs_polynomial alphabet source)

def machine : BitMachine.Machine := BitMachineComposition.composition
  preparedMachine CylinderActualMatrixEvaluator.machine

def coefficient : Nat := FeaturePhysicalCompositionBounds.inputCoefficient
  preparedCoefficient CylinderActualMatrixEvaluator.coefficient CylinderActualMatrixEvaluator.exponent
  preparedMachine.pushBound
def exponent : Nat := FeaturePhysicalCompositionBounds.inputExponent
  preparedExponent CylinderActualMatrixEvaluator.exponent

/-- A single fixed physical machine takes exactly the original Fin3 packet
of unary q, weighted alphabet bytes, and weighted source bytes. It computes
all generated features and every source-coordinate equality, and prints the
exact cylinder matrix word. No rows, decoded bank, callback execution, clock
cap or output-size bound is supplied. Original array repetitions are kept. -/
theorem outputs_polynomial {q : Nat} (alphabet : Array (Nat × ℚ))
    (source : Array ((Fin q → Nat) × ℚ)) :
    machine.OutputsWithin (input alphabet source)
      (CylinderFeatureCodec.cylinderMatrixBits q 8192 (alphabet.map Prod.fst) source)
      (coefficient*((input alphabet source).length+1)^exponent) := by
  exact FeaturePhysicalCompositionBounds.outputs_input_clock _ _ (input alphabet source)
    (preparedWord alphabet source)
    (CylinderFeatureCodec.cylinderMatrixBits q 8192 (alphabet.map Prod.fst) source)
    preparedCoefficient preparedExponent CylinderActualMatrixEvaluator.coefficient
    CylinderActualMatrixEvaluator.exponent (prepared_outputs_polynomial alphabet source)
    (CylinderActualMatrixEvaluator.outputs_polynomial q 8192 (alphabet.map Prod.fst) source)

#print axioms prepared_outputs_polynomial
#print axioms outputs_polynomial
end CurrentAdditive.CylinderRawMatrixProducer
