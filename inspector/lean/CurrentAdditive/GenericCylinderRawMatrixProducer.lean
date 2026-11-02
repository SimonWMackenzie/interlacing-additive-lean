import CurrentAdditive.GenericFeatureRawPolynomial
import CurrentAdditive.GenericCylinderStateMatrixProducer

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option synthInstance.maxSize 65536
set_option maxRecDepth 4096

namespace CurrentAdditive.GenericCylinderRawMatrixProducer
open EthInapproximability.CurrentPaper

def input {q : Nat} (alphabet : Array (Nat × ℚ))
    (source : Array ((Fin q → Nat) × ℚ)) := CylinderRawInputProjection.input alphabet source

def machine (D : Nat) : BitMachine.Machine := BitMachineComposition.composition
  (GenericFeatureRawEnumeration.stateMachine D) (GenericCylinderStateMatrixProducer.machine D)

def coefficient (D : Nat) : Nat := FeaturePhysicalCompositionBounds.inputCoefficient
  (GenericFeatureRawPolynomial.stateCoefficient D) (GenericCylinderStateMatrixProducer.coefficient D)
  (GenericCylinderStateMatrixProducer.exponent D) (GenericFeatureRawEnumeration.stateMachine D).pushBound

def exponent (D : Nat) : Nat := FeaturePhysicalCompositionBounds.inputExponent
  (GenericFeatureRawPolynomial.stateExponent D) (GenericCylinderStateMatrixProducer.exponent D)

/-- One fixed machine for each fixed D reads the original Fin3 weighted
source packet and prints the exact cylinder matrix, preserving all original
positions and repetitions. No prepared field, run or cap is supplied. -/
theorem outputs_polynomial_all (D : Nat) {q : Nat} (alphabet : Array (Nat × ℚ))
    (source : Array ((Fin q → Nat) × ℚ)) :
    (machine D).OutputsWithin (input alphabet source)
      (CylinderFeatureCodec.cylinderMatrixBits q D (alphabet.map Prod.fst) source)
      (coefficient D * ((input alphabet source).length + 1) ^ exponent D) := by
  exact FeaturePhysicalCompositionBounds.outputs_input_clock _ _ (input alphabet source)
    (GenericCylinderStateMatrixProducer.input D alphabet source)
    (CylinderFeatureCodec.cylinderMatrixBits q D (alphabet.map Prod.fst) source)
    (GenericFeatureRawPolynomial.stateCoefficient D) (GenericFeatureRawPolynomial.stateExponent D)
    (GenericCylinderStateMatrixProducer.coefficient D) (GenericCylinderStateMatrixProducer.exponent D)
    (GenericFeatureRawPolynomial.state_outputs_polynomial D alphabet source)
    (GenericCylinderStateMatrixProducer.outputs_polynomial D alphabet source)

theorem outputs_polynomial (D : Nat) (_hD : 1 ≤ D) {q : Nat} (alphabet : Array (Nat × ℚ))
    (source : Array ((Fin q → Nat) × ℚ)) :
    (machine D).OutputsWithin (CylinderRawInputProjection.input alphabet source)
      (CylinderFeatureCodec.cylinderMatrixBits q D (alphabet.map Prod.fst) source)
      (coefficient D * ((CylinderRawInputProjection.input alphabet source).length + 1) ^ exponent D) :=
  outputs_polynomial_all D alphabet source

end CurrentAdditive.GenericCylinderRawMatrixProducer
