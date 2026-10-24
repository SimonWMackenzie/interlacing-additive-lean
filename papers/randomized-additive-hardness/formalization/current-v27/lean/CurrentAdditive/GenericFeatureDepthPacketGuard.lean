import CurrentAdditive.GenericFeatureDepthGuard
import CurrentAdditive.FeatureDepthPacketGuard

/-! Actual canonical descriptor-header parsing followed by exact strict
comparison with the fixed depth D. Unchanged parser/drop machines are reused. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace CurrentAdditive.GenericFeatureDepthPacketGuard
open EthInapproximability.CurrentPaper BitMachineEncoding EncodedCommunication

def machine (D : Nat) : BitMachine.Machine := BitMachineComposition.composition
  (BitMachineComposition.composition ProtocolBinaryHeader.machine FeatureDepthPacketGuard.dropSuccessMachine)
  (GenericFeatureDepthGuard.machine D)

theorem stack_count (D : Nat) : (machine D).stackCount = 8 := by
  simp [machine, BitMachineComposition.composition, BitMachineComposition.Stack, GenericFeatureDepthGuard.machine,
    FeatureDepthPacketGuard.dropSuccessMachine, ProtocolBinaryHeader.machine, ofFinite]

def clock (input : List Bool) : Nat := 8 * (input.length + 1) + 10

theorem physical_total (D : Nat) (input : List Bool) :
    (machine D).OutputsWithin input
      [decide (bitsValue (ProtocolBinaryHeader.result input).tail < D)] (clock input) := by
  have hp := ProtocolBinaryHeader.outputs input
  have hd := FeatureDepthPacketGuard.drop_success (ProtocolBinaryHeader.result input)
  have hf := BitMachineComposition.composition_outputsWithin _ _ hp hd
  have hg := GenericFeatureDepthGuard.physical_word D (ProtocolBinaryHeader.result input).tail
  have h := BitMachineComposition.composition_outputsWithin _ _ hf hg
  have hs := FeatureDepthPacketGuard.parser_result_length_le input
  have ht : (ProtocolBinaryHeader.result input).tail.length ≤
      (ProtocolBinaryHeader.result input).length := by
    cases h : ProtocolBinaryHeader.result input <;> simp [h]
  apply BitMachine.outputsWithin_mono _ h
  dsimp only [clock]
  omega

theorem physical_feature (D : Nat) (c : List (Nat × Nat)) :
    (machine D).OutputsWithin (CylinderFeatureCodec.encodeFeature c)
      [decide (c.length < D)] (clock (CylinderFeatureCodec.encodeFeature c)) := by
  have h := physical_total D (CylinderFeatureCodec.encodeFeature c)
  rw [FeatureDepthPacketGuard.header_result_feature] at h
  simpa only [List.tail_cons, bitsValue_bits] using h

#print axioms physical_total
#print axioms physical_feature
end CurrentAdditive.GenericFeatureDepthPacketGuard
