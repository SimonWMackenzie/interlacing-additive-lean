import CurrentAdditive.GenericFeatureRawEnumeration
import CurrentAdditive.FeaturePhysicalCompositionBounds
import CurrentAdditive.FeatureSeedClock96
import CurrentAdditive.GenericFeatureOuterRawClock

/-! Original-input polynomial clock for the actual complete feature producer.
Every scalar bound is proved for the same raw source word consumed by the
physical seed loader and coordinate loop. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option synthInstance.maxSize 65536
set_option maxRecDepth 4096
namespace CurrentAdditive.GenericFeatureRawPolynomial
open EthInapproximability.CurrentPaper

def stateCoefficient (D : Nat) : Nat := FeaturePhysicalCompositionBounds.coefficient
  FeatureSeedClock96.coefficient (GenericFeatureOuterRawClock.coefficient D) FeatureSeedMachine96.machine.pushBound
def stateExponent (D : Nat) : Nat := FeaturePhysicalCompositionBounds.exponent
  FeatureSeedClock96.exponent (GenericFeatureOuterRawClock.exponent D)

theorem state_outputs_polynomial (D : Nat) {q : Nat} (alphabet : Array (Nat × ℚ))
    (source : Array ((Fin q → Nat) × ℚ)) :
    let raw := CylinderRawInputProjection.input alphabet source
    (GenericFeatureRawEnumeration.stateMachine D).OutputsWithin raw
      (GenericFeatureGeneratedIteration.states D (alphabet.map Prod.fst).toList raw q)
      (stateCoefficient D*(raw.length+1)^stateExponent D) := by
  let raw := CylinderRawInputProjection.input alphabet source
  let ys := (alphabet.map Prod.fst).toList
  have hs := FeatureSeedClock96.outputs_polynomial alphabet source
  have hi := BitMachine.outputsWithin_mono (GenericFeatureIterationPacket.machine D)
    (GenericFeatureIterationPacket.outputs D q ys raw) (GenericFeatureOuterRawClock.clock_le D alphabet source)
  rw [←GenericFeatureRawEnumeration.seedWord_eq] at hi
  exact FeaturePhysicalCompositionBounds.outputs _ _ raw (FeatureSeedLayout.output raw q ys)
    (GenericFeatureGeneratedIteration.states D ys raw q)
    FeatureSeedClock96.coefficient FeatureSeedClock96.exponent
    (GenericFeatureOuterRawClock.coefficient D) (GenericFeatureOuterRawClock.exponent D) hs hi

def coefficient (D : Nat) : Nat := FeaturePhysicalCompositionBounds.inputCoefficient
  (stateCoefficient D) 196 1 (GenericFeatureRawEnumeration.stateMachine D).pushBound
def exponent (D : Nat) : Nat := FeaturePhysicalCompositionBounds.inputExponent (stateExponent D) 1

/-- One fixed machine and one fixed polynomial print the full feature packet
from every typed original q/alphabet/source word. No execution, prepared bank,
scalar cap, or output-size bound remains as a hypothesis. -/
theorem outputs_polynomial (D : Nat) {q : Nat} (alphabet : Array (Nat × ℚ))
    (source : Array ((Fin q → Nat) × ℚ)) :
    let raw := CylinderRawInputProjection.input alphabet source
    (GenericFeatureRawEnumeration.machine D).OutputsWithin raw
      (CylinderFeatureCodec.generatedFeatureBits q D (alphabet.map Prod.fst))
      (coefficient D*(raw.length+1)^exponent D) := by
  let raw := CylinderRawInputProjection.input alphabet source
  let ys := (alphabet.map Prod.fst).toList
  have hp : GenericFeatureFinalStateProjection.featureMachine.OutputsWithin
      (GenericFeatureGeneratedIteration.states D ys raw q)
      (CylinderFeatureCodec.generatedFeatureBits q D (alphabet.map Prod.fst))
      (196*((GenericFeatureGeneratedIteration.states D ys raw q).length+1)^1) := by
    simpa only [pow_one] using
      GenericFeatureFinalStateProjection.features_output D q (alphabet.map Prod.fst) raw
  exact FeaturePhysicalCompositionBounds.outputs_input_clock _ _ raw
    (GenericFeatureGeneratedIteration.states D ys raw q)
    (CylinderFeatureCodec.generatedFeatureBits q D (alphabet.map Prod.fst))
    (stateCoefficient D) (stateExponent D) 196 1 (state_outputs_polynomial D alphabet source) hp

#print axioms state_outputs_polynomial
#print axioms outputs_polynomial
end CurrentAdditive.GenericFeatureRawPolynomial
