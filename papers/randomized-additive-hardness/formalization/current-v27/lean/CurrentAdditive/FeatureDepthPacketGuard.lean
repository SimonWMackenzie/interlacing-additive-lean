import CurrentAdditive.FeatureDepthGuard
import CurrentAdditive.CylinderFeatureCodec
import EthInapproximability.CurrentPaper.SourceListMachineFields
import EthInapproximability.CurrentPaper.BitMachineComposition

/-!
Physical eligibility test on one whole canonical V2 feature word.  The
existing checked binary-header parser extracts its count with a success bit;
one literal pop removes that bit, and the fixed 8192 guard reads the count.
The input may have an arbitrary field suffix, as a feature descriptor does.
-/

namespace CurrentAdditive.FeatureDepthPacketGuard

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachine
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper.EncodedCommunication
open Turing Turing.TM2.Stmt

def dropSuccessProgram (_ : Unit) :
    TM2.Stmt (fun _ : Unit => Bool) Unit Unit :=
  pop () (fun _ _ => ()) halt

noncomputable def dropSuccessMachine : Machine :=
  ofFinite () () () () dropSuccessProgram

theorem drop_success (input : List Bool) :
    dropSuccessMachine.OutputsWithin input input.tail 1 := by
  apply outputsWithin_of_raw_run () () () () dropSuccessProgram
    input input.tail 1 1 (by omega)
  · cases input <;> rfl
  · cases input <;> rfl

noncomputable def machine : Machine :=
  BitMachineComposition.composition
    (BitMachineComposition.composition
      ProtocolBinaryHeader.machine dropSuccessMachine)
    CurrentAdditive.FeatureDepthGuard.machine

theorem physical_total (input : List Bool) :
    machine.OutputsWithin input
      [decide ((ProtocolBinaryHeader.result input).tail.length ≤ 13)]
      ((2 * input.length + 2) +
        2 * (ProtocolBinaryHeader.result input).length + 2 + 1 +
        2 * (ProtocolBinaryHeader.result input).tail.length + 2 + 15) := by
  have hparser := ProtocolBinaryHeader.outputs input
  have hdrop := drop_success (ProtocolBinaryHeader.result input)
  have hfirst := BitMachineComposition.composition_outputsWithin
    ProtocolBinaryHeader.machine dropSuccessMachine hparser hdrop
  have hguard := CurrentAdditive.FeatureDepthGuard.physical_word
    (ProtocolBinaryHeader.result input).tail
  simpa only [machine] using
    BitMachineComposition.composition_outputsWithin
      (BitMachineComposition.composition
        ProtocolBinaryHeader.machine dropSuccessMachine)
      CurrentAdditive.FeatureDepthGuard.machine hfirst hguard

theorem parser_result_length_le (input : List Bool) :
    (ProtocolBinaryHeader.result input).length ≤ input.length + 1 := by
  cases hp : ProtocolBinaryHeader.readChecked none input with
  | none => simp [ProtocolBinaryHeader.result, hp]
  | some p =>
      rcases p with ⟨bs, rest⟩
      have hspec := ProtocolBinaryHeader.readChecked_spec input none
      rw [hp] at hspec
      cases hf : readField input with
      | none => simp [hf] at hspec
      | some p =>
          rcases p with ⟨ys, suffix⟩
          simp [hf] at hspec
          rcases hspec with ⟨_, hbs, hrest⟩
          subst bs
          subst rest
          have hs := readField_sound hf
          have hl := congrArg List.length hs
          simp only [List.length_append, field_length] at hl
          simp [ProtocolBinaryHeader.result, hp]
          omega

theorem physical_total_linear (input : List Bool) :
    machine.OutputsWithin input
      [decide ((ProtocolBinaryHeader.result input).tail.length ≤ 13)]
      (6 * (input.length + 1) + 20) := by
  have h := physical_total input
  have hr := parser_result_length_le input
  have ht : (ProtocolBinaryHeader.result input).tail.length ≤
      (ProtocolBinaryHeader.result input).length := by
    cases h : ProtocolBinaryHeader.result input with
    | nil => simp [h]
    | cons b bs => simp [h]
  exact BitMachine.outputsWithin_mono machine h (by omega)

theorem header_result_feature (c : List (Nat × Nat)) :
    ProtocolBinaryHeader.result
      (CurrentAdditive.CylinderFeatureCodec.encodeFeature c) =
        true :: c.length.bits := by
  have h := SourceListMachineFields.readChecked_natField
    c.length (SourceListEncoding.fields
      (c.map CurrentAdditive.CylinderFeatureCodec.encodePair))
  simp [ProtocolBinaryHeader.result,
    CurrentAdditive.CylinderFeatureCodec.encodeFeature,
    CurrentAdditive.CodeDCodecV2.encodeItems,
    SourceListEncoding.encode, h]

theorem physical_feature (c : List (Nat × Nat)) :
    machine.OutputsWithin
      (CurrentAdditive.CylinderFeatureCodec.encodeFeature c)
      [decide (c.length < 8192)]
      ((2 * (CurrentAdditive.CylinderFeatureCodec.encodeFeature c).length + 2) +
        2 * (true :: c.length.bits).length + 2 + 1 +
        2 * c.length.bits.length + 2 + 15) := by
  have hparser := ProtocolBinaryHeader.outputs
    (CurrentAdditive.CylinderFeatureCodec.encodeFeature c)
  rw [header_result_feature] at hparser
  have hdrop := drop_success (true :: c.length.bits)
  have hfirst := BitMachineComposition.composition_outputsWithin
    ProtocolBinaryHeader.machine dropSuccessMachine hparser hdrop
  have hguard := CurrentAdditive.FeatureDepthGuard.physical_guard c.length
  simpa only [machine, List.tail_cons] using
    BitMachineComposition.composition_outputsWithin
      (BitMachineComposition.composition
        ProtocolBinaryHeader.machine dropSuccessMachine)
      CurrentAdditive.FeatureDepthGuard.machine hfirst hguard

#print axioms physical_feature
#print axioms physical_total
#print axioms physical_total_linear

end CurrentAdditive.FeatureDepthPacketGuard
