import CurrentAdditive.GenericFeatureIterationPacket
import CurrentAdditive.GenericFeatureFinalStateProjection
import CurrentAdditive.FeatureSeedMachine96

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option synthInstance.maxSize 65536
set_option maxRecDepth 4096

namespace CurrentAdditive.GenericFeatureRawEnumeration
open EthInapproximability.CurrentPaper

theorem generated_state_eq (D : Nat) (ys : List Nat) (raw : List Bool) (q : Nat) :
    GenericFeatureGeneratedIteration.states D ys raw q =
      GenericFeatureFinalStateProjection.states D ys raw q := rfl

theorem seedWord_eq (D : Nat) (raw : List Bool) (q : Nat) (ys : List Nat) :
    FeatureSeedLayout.output raw q ys =
      BitMachineBankCodec.encode (GenericFeatureIterationPacket.words D q ys raw) := by
  rw [FeatureSeedLayout.output_exact]
  rfl

def stateMachine (D : Nat) : BitMachine.Machine := BitMachineComposition.composition
  FeatureSeedMachine96.machine (GenericFeatureIterationPacket.machine D)

def stateClock (D : Nat) (raw : List Bool) (q : Nat) (ys : List Nat) :=
  FeatureSeedMachine96.clock raw q ys + 2 * (FeatureSeedLayout.output raw q ys).length + 2 +
    GenericFeatureIterationPacket.clock D q ys raw

theorem state_outputs (D : Nat) {q : Nat} (alphabet : Array (Nat × ℚ))
    (source : Array ((Fin q → Nat) × ℚ)) :
    let raw := CylinderRawInputProjection.input alphabet source
    let ys := (alphabet.map Prod.fst).toList
    (stateMachine D).OutputsWithin raw (GenericFeatureGeneratedIteration.states D ys raw q)
      (stateClock D raw q ys) := by
  let raw := CylinderRawInputProjection.input alphabet source
  let ys := (alphabet.map Prod.fst).toList
  have hi := GenericFeatureIterationPacket.outputs D q ys raw
  rw [← seedWord_eq D] at hi
  exact BitMachineComposition.composition_outputsWithin _ _
    (FeatureSeedMachine96.outputs alphabet source) hi

def machine (D : Nat) : BitMachine.Machine := BitMachineComposition.composition
  (stateMachine D) GenericFeatureFinalStateProjection.featureMachine

def clock (D : Nat) (raw : List Bool) (q : Nat) (ys : List Nat) :=
  stateClock D raw q ys + 2 * (GenericFeatureGeneratedIteration.states D ys raw q).length + 2 +
    196 * ((GenericFeatureGeneratedIteration.states D ys raw q).length + 1)

theorem outputs (D : Nat) {q : Nat} (alphabet : Array (Nat × ℚ))
    (source : Array ((Fin q → Nat) × ℚ)) :
    let raw := CylinderRawInputProjection.input alphabet source
    (machine D).OutputsWithin raw
      (CylinderFeatureCodec.generatedFeatureBits q D (alphabet.map Prod.fst))
      (clock D raw q (alphabet.map Prod.fst).toList) := by
  exact BitMachineComposition.composition_outputsWithin _ _
    (state_outputs D alphabet source)
    (GenericFeatureFinalStateProjection.features_output D q (alphabet.map Prod.fst)
      (CylinderRawInputProjection.input alphabet source))

end CurrentAdditive.GenericFeatureRawEnumeration
