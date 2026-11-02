import CurrentAdditive.CodeDUpdateProductPolytime
import EthInapproximability.CurrentPaper.SourceFieldWriter

/-! Canonical product from the position request, framed for a Bank2 join. -/

namespace CurrentAdditive.CodeDUpdateProductFramed

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.EncodedCommunication

noncomputable def productWord (x : List Bool) : List Bool :=
  RationalCanonicalCallback.productResult (CodeDUpdateProductPairJoin.output x)

noncomputable def machine : BitMachine.Machine :=
  BitMachineComposition.composition
    CodeDUpdateProductPolytime.machine SourceFieldWriter.fieldMachine

noncomputable def result (x : List Bool) : List Bool := field (productWord x)

noncomputable def clock (x : List Bool) : Nat :=
  CodeDUpdateProductPolytime.coefficient *
    (x.length+1)^CodeDUpdateProductPolytime.exponent +
  2*(productWord x).length+2 + (4*(productWord x).length+4)

theorem outputs (x : List Bool) :
    machine.OutputsWithin x (result x) (clock x) := by
  have h := BitMachineComposition.composition_outputsWithin
    CodeDUpdateProductPolytime.machine SourceFieldWriter.fieldMachine
    (CodeDUpdateProductPolytime.outputs x)
    (SourceFieldWriter.field_outputs (productWord x))
  simpa only [machine, result, clock, productWord, Function.comp_def] using h

theorem product_request (old : CodeDSourceCodecV2.Entry)
    (lambda coefficient : ℚ) :
    productWord (CodeDUpdateProductPairFields.requestPacket old lambda coefficient) =
      CodeDCodec.encodeRawRat
        (CodeDCanonicalSourceV2.rawOfRat (lambda * coefficient)) := by
  rw [productWord, show CodeDUpdateProductPairJoin.output
      (CodeDUpdateProductPairFields.requestPacket old lambda coefficient) =
      CodeDPairProductTargetV2.pairBytes
        (CodeDCanonicalSourceV2.rawOfRat lambda)
        (CodeDCanonicalSourceV2.rawOfRat coefficient) by
          exact CodeDUpdateProductPairFields.fields_request old lambda coefficient]
  rw [RationalCanonicalCallback.product_result_pair]
  · rw [CodeDCanonicalSourceV2.rawOfRat_value,
      CodeDCanonicalSourceV2.rawOfRat_value]
    rfl
  · exact CodeDCanonicalSourceV2.rawOfRat_valid lambda
  · exact CodeDCanonicalSourceV2.rawOfRat_valid coefficient

#print axioms outputs
#print axioms product_request

end CurrentAdditive.CodeDUpdateProductFramed
