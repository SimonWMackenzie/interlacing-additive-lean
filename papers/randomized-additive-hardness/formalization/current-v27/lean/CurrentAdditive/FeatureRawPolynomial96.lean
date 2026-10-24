import CurrentAdditive.FeatureRawEnumeration96
import CurrentAdditive.FeaturePhysicalCompositionBounds
import CurrentAdditive.FeatureSeedClock96
import CurrentAdditive.FeatureOuterRawClock96

/-! Original-input polynomial clock for the actual complete feature producer.
Every scalar bound is proved for the same raw source word consumed by the
physical seed loader and coordinate loop. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option synthInstance.maxSize 65536
set_option maxRecDepth 4096
namespace CurrentAdditive.FeatureRawPolynomial96
open EthInapproximability.CurrentPaper

def stateCoefficient : Nat := FeaturePhysicalCompositionBounds.coefficient
  FeatureSeedClock96.coefficient FeatureOuterRawClock96.coefficient FeatureSeedMachine96.machine.pushBound
def stateExponent : Nat := FeaturePhysicalCompositionBounds.exponent
  FeatureSeedClock96.exponent FeatureOuterRawClock96.exponent

theorem state_outputs_polynomial {q : Nat} (alphabet : Array (Nat × ℚ))
    (source : Array ((Fin q → Nat) × ℚ)) :
    let raw := CylinderRawInputProjection.input alphabet source
    FeatureRawEnumeration96.stateMachine.OutputsWithin raw
      (FeatureGeneratedIteration96.states (alphabet.map Prod.fst).toList raw q)
      (stateCoefficient*(raw.length+1)^stateExponent) := by
  let raw := CylinderRawInputProjection.input alphabet source
  let ys := (alphabet.map Prod.fst).toList
  have hs := FeatureSeedClock96.outputs_polynomial alphabet source
  have hi := BitMachine.outputsWithin_mono FeatureIterationPacket96.machine
    (FeatureIterationPacket96.outputs q ys raw) (FeatureOuterRawClock96.clock_le alphabet source)
  rw [←FeatureRawEnumeration96.seedWord_eq] at hi
  exact FeaturePhysicalCompositionBounds.outputs _ _ raw (FeatureSeedLayout.output raw q ys)
    (FeatureGeneratedIteration96.states ys raw q)
    FeatureSeedClock96.coefficient FeatureSeedClock96.exponent
    FeatureOuterRawClock96.coefficient FeatureOuterRawClock96.exponent hs hi

def coefficient : Nat := FeaturePhysicalCompositionBounds.inputCoefficient
  stateCoefficient 196 1 FeatureRawEnumeration96.stateMachine.pushBound
def exponent : Nat := FeaturePhysicalCompositionBounds.inputExponent stateExponent 1

/-- One fixed machine and one fixed polynomial print the full feature packet
from every typed original q/alphabet/source word. No execution, prepared bank,
scalar cap, or output-size bound remains as a hypothesis. -/
theorem outputs_polynomial {q : Nat} (alphabet : Array (Nat × ℚ))
    (source : Array ((Fin q → Nat) × ℚ)) :
    let raw := CylinderRawInputProjection.input alphabet source
    FeatureRawEnumeration96.machine.OutputsWithin raw
      (CylinderFeatureCodec.generatedFeatureBits q 8192 (alphabet.map Prod.fst))
      (coefficient*(raw.length+1)^exponent) := by
  let raw := CylinderRawInputProjection.input alphabet source
  let ys := (alphabet.map Prod.fst).toList
  have hp : FeatureFinalStateProjection96.featureMachine.OutputsWithin
      (FeatureGeneratedIteration96.states ys raw q)
      (CylinderFeatureCodec.generatedFeatureBits q 8192 (alphabet.map Prod.fst))
      (196*((FeatureGeneratedIteration96.states ys raw q).length+1)^1) := by
    simpa only [pow_one] using
      FeatureFinalStateProjection96.features_output q (alphabet.map Prod.fst) raw
  exact FeaturePhysicalCompositionBounds.outputs_input_clock _ _ raw
    (FeatureGeneratedIteration96.states ys raw q)
    (CylinderFeatureCodec.generatedFeatureBits q 8192 (alphabet.map Prod.fst))
    stateCoefficient stateExponent 196 1 (state_outputs_polynomial alphabet source) hp

#print axioms state_outputs_polynomial
#print axioms outputs_polynomial
end CurrentAdditive.FeatureRawPolynomial96
