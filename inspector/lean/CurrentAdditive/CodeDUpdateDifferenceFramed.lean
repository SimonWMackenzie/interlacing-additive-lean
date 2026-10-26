import CurrentAdditive.CodeDUpdateSubtractPairJoin
import CurrentAdditive.RationalSubtractCanonical
import EthInapproximability.CurrentPaper.SourceFieldWriter

/-! Physical canonical weight difference, framed for the final old-entry/new-weight pair. -/

namespace CurrentAdditive.CodeDUpdateDifferenceFramed

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.EncodedCommunication

noncomputable def differenceWord (x : List Bool) : List Bool :=
  RationalSubtractCanonical.result (CodeDUpdateSubtractPairJoin.output x)

noncomputable def machine : BitMachine.Machine :=
  BitMachineComposition.composition
    (BitMachineComposition.composition
      CodeDUpdateSubtractPairJoin.machine
      RationalSubtractCanonical.machine)
    SourceFieldWriter.fieldMachine

noncomputable def result (x : List Bool) : List Bool :=
  field (differenceWord x)

noncomputable def clock (x : List Bool) : Nat :=
  CodeDUpdateSubtractPairJoin.clock x +
  2*(CodeDUpdateSubtractPairJoin.output x).length+2 +
  RationalSubtractCanonical.coefficient *
    ((CodeDUpdateSubtractPairJoin.output x).length+1)^
      RationalSubtractCanonical.exponent +
  2*(differenceWord x).length+2 +
  (4*(differenceWord x).length+4)

theorem outputs (x : List Bool) :
    machine.OutputsWithin x (result x) (clock x) := by
  have h₁ := BitMachineComposition.composition_outputsWithin
    CodeDUpdateSubtractPairJoin.machine RationalSubtractCanonical.machine
    (CodeDUpdateSubtractPairJoin.outputs x)
    (RationalSubtractCanonical.outputsWithin
      (CodeDUpdateSubtractPairJoin.output x))
  have h₂ := BitMachineComposition.composition_outputsWithin
    (BitMachineComposition.composition CodeDUpdateSubtractPairJoin.machine
      RationalSubtractCanonical.machine)
    SourceFieldWriter.fieldMachine h₁
    (SourceFieldWriter.field_outputs (differenceWord x))
  simpa only [machine, result, clock, differenceWord] using h₂

theorem difference_request (old : CodeDSourceCodecV2.Entry)
    (lambda coefficient : ℚ) (hvalid : old.weight.Valid) :
    differenceWord
      (CodeDUpdateProductPairFields.requestPacket old lambda coefficient) =
    CodeDCodec.encodeRawRat
      (CodeDCanonicalSourceV2.rawOfRat
        (old.weight.value - lambda * coefficient)) := by
  rw [differenceWord, CodeDUpdateSubtractPairJoin.output_request]
  change RationalSubtractCanonical.result
    (RationalSubtractPairMachine.pairBytes old.weight
      (CodeDCanonicalSourceV2.rawOfRat (lambda * coefficient))) = _
  rw [RationalSubtractCanonical.canonical_pair]
  · rw [CodeDCanonicalSourceV2.rawOfRat_value]
    rfl
  · exact hvalid
  · exact CodeDCanonicalSourceV2.rawOfRat_valid _

#print axioms outputs
#print axioms difference_request

end CurrentAdditive.CodeDUpdateDifferenceFramed
