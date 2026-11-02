import CurrentAdditive.GenericFeatureFinalAssemblerClock
import CurrentAdditive.CylinderActualEvaluatorPolynomial
import CurrentAdditive.FeaturePhysicalCompositionBounds

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

namespace CurrentAdditive.GenericCylinderStateMatrixProducer
open EthInapproximability.CurrentPaper

def input (D : Nat) {q : Nat} (alphabet : Array (Nat × ℚ))
    (source : Array ((Fin q → Nat) × ℚ)) :=
  GenericFeatureFinalStateProjection.states D (alphabet.map Prod.fst).toList
    (CylinderRawInputProjection.input alphabet source) q

def preparedWord (D : Nat) {q : Nat} (alphabet : Array (Nat × ℚ))
    (source : Array ((Fin q → Nat) × ℚ)) :=
  CylinderActualMatrixEvaluator.input q D (alphabet.map Prod.fst) source

def machine (D : Nat) : BitMachine.Machine := BitMachineComposition.composition
  (GenericFeatureFinalAssembler.machine D) CylinderActualMatrixEvaluator.machine

def coefficient (D : Nat) : Nat := FeaturePhysicalCompositionBounds.inputCoefficient
  (GenericFeatureFinalAssemblerClock.coefficient D) CylinderActualMatrixEvaluator.coefficient
  CylinderActualMatrixEvaluator.exponent (GenericFeatureFinalAssembler.machine D).pushBound

def exponent (D : Nat) : Nat := FeaturePhysicalCompositionBounds.inputExponent
  (GenericFeatureFinalAssemblerClock.exponent D) CylinderActualMatrixEvaluator.exponent

/-- Actual final packed state to every literal cylinder-matrix cell. The
source tuples and generated descriptors are physically projected first. -/
theorem outputs_polynomial (D : Nat) {q : Nat} (alphabet : Array (Nat × ℚ))
    (source : Array ((Fin q → Nat) × ℚ)) :
    (machine D).OutputsWithin (input D alphabet source)
      (CylinderFeatureCodec.cylinderMatrixBits q D (alphabet.map Prod.fst) source)
      (coefficient D * ((input D alphabet source).length + 1) ^ exponent D) := by
  exact FeaturePhysicalCompositionBounds.outputs_input_clock _ _ (input D alphabet source)
    (preparedWord D alphabet source)
    (CylinderFeatureCodec.cylinderMatrixBits q D (alphabet.map Prod.fst) source)
    (GenericFeatureFinalAssemblerClock.coefficient D) (GenericFeatureFinalAssemblerClock.exponent D)
    CylinderActualMatrixEvaluator.coefficient CylinderActualMatrixEvaluator.exponent
    (GenericFeatureFinalAssemblerClock.outputs_polynomial D alphabet source)
    (CylinderActualMatrixEvaluator.outputs_polynomial q D (alphabet.map Prod.fst) source)

end CurrentAdditive.GenericCylinderStateMatrixProducer
