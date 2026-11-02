import CurrentAdditive.FeatureSeedMachine96
import CurrentAdditive.FeatureIterationPacket96
import CurrentAdditive.FeatureFinalStateProjection96

/-! Actual raw production input to the complete generated feature packet.
The exact operational clock is retained for the separate scalar bound. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option synthInstance.maxSize 65536
set_option maxRecDepth 4096
namespace CurrentAdditive.FeatureRawEnumeration96
open EthInapproximability.CurrentPaper

theorem seedWord_eq (raw : List Bool) (q : Nat) (ys : List Nat) :
    FeatureSeedLayout.output raw q ys=
      BitMachineBankCodec.encode (FeatureIterationPacket96.words q ys raw) := by
  rw [FeatureSeedLayout.output_exact]
  rfl

def stateMachine : BitMachine.Machine := BitMachineComposition.composition
  FeatureSeedMachine96.machine FeatureIterationPacket96.machine

def stateClock (raw : List Bool) (q : Nat) (ys : List Nat) :=
  FeatureSeedMachine96.clock raw q ys+2*(FeatureSeedLayout.output raw q ys).length+2+
    FeatureIterationPacket96.clock q ys raw

theorem state_outputs {q : Nat} (alphabet : Array (Nat × ℚ))
    (source : Array ((Fin q → Nat) × ℚ)) :
    let raw := CylinderRawInputProjection.input alphabet source
    let ys := (alphabet.map Prod.fst).toList
    stateMachine.OutputsWithin raw (FeatureGeneratedIteration96.states ys raw q)
      (stateClock raw q ys) := by
  let raw := CylinderRawInputProjection.input alphabet source
  let ys := (alphabet.map Prod.fst).toList
  have hi := FeatureIterationPacket96.outputs q ys raw
  rw [←seedWord_eq] at hi
  exact BitMachineComposition.composition_outputsWithin _ _
    (FeatureSeedMachine96.outputs alphabet source) hi

def machine : BitMachine.Machine := BitMachineComposition.composition
  stateMachine FeatureFinalStateProjection96.featureMachine

def clock (raw : List Bool) (q : Nat) (ys : List Nat) :=
  stateClock raw q ys+2*(FeatureGeneratedIteration96.states ys raw q).length+2+
    196*((FeatureGeneratedIteration96.states ys raw q).length+1)

/-- One fixed physical machine reads the actual raw q/alphabet/source packet
and prints every generated descriptor, in the required duplicate-preserving
order, with no installed-state or traversal premise. -/
theorem outputs {q : Nat} (alphabet : Array (Nat × ℚ))
    (source : Array ((Fin q → Nat) × ℚ)) :
    let raw := CylinderRawInputProjection.input alphabet source
    machine.OutputsWithin raw
      (CylinderFeatureCodec.generatedFeatureBits q 8192 (alphabet.map Prod.fst))
      (clock raw q (alphabet.map Prod.fst).toList) := by
  exact BitMachineComposition.composition_outputsWithin _ _
    (state_outputs alphabet source)
    (FeatureFinalStateProjection96.features_output q (alphabet.map Prod.fst)
      (CylinderRawInputProjection.input alphabet source))

#print axioms seedWord_eq
#print axioms state_outputs
#print axioms outputs
end CurrentAdditive.FeatureRawEnumeration96
