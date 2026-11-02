import CurrentAdditive.RationalSubtractSerialized
import CurrentAdditive.RawRatPacketTotal

/-! A total fixed TM2 callback for canonical rational subtraction. -/

namespace EthInapproximability.CurrentPaper.RationalSubtractCanonical

open CurrentAdditive.CodeDCodec

noncomputable def result : List Bool → List Bool :=
  CurrentAdditive.RawRatPacketTotal.result ∘ RationalSubtractSerialized.result

theorem polytime : BitMachine.Polytime result := by
  simpa only [result] using BitMachineComposition.polytime_comp
    RationalSubtractSerialized.polytime
    CurrentAdditive.RawRatPacketTotal.polytime

noncomputable def machine : BitMachine.Machine := Classical.choose polytime

noncomputable def coefficient : Nat :=
  Classical.choose (Classical.choose_spec polytime)

noncomputable def exponent : Nat :=
  Classical.choose (Classical.choose_spec (Classical.choose_spec polytime))

theorem outputsWithin (input : List Bool) :
    machine.OutputsWithin input (result input)
      (coefficient * (input.length+1)^exponent) :=
  (Classical.choose_spec (Classical.choose_spec
    (Classical.choose_spec polytime))) input

theorem canonical_pair (a b : RawRat) (ha : a.Valid) (hb : b.Valid) :
    result (RationalSubtractPairMachine.pairBytes a b) =
      encodeRawRat (CurrentAdditive.CodeDCanonicalSource.rawOfRat
        (a.value-b.value)) := by
  rw [result, Function.comp_apply,
    RationalSubtractSerialized.result_pair,
    CurrentAdditive.RawRatPacketTotal.canonical_result
      (RationalSubtractSpec.outputRat a b)
      (RationalSubtractSpec.output_valid a b ha hb),
    RationalSubtractSpec.output_value a b ha hb]

theorem canonical_pair_outputs (a b : RawRat)
    (ha : a.Valid) (hb : b.Valid) :
    machine.OutputsWithin
      (RationalSubtractPairMachine.pairBytes a b)
      (encodeRawRat (CurrentAdditive.CodeDCanonicalSource.rawOfRat
        (a.value-b.value)))
      (coefficient *
        ((RationalSubtractPairMachine.pairBytes a b).length+1)^exponent) := by
  simpa only [canonical_pair a b ha hb] using
    outputsWithin (RationalSubtractPairMachine.pairBytes a b)

#print axioms polytime
#print axioms canonical_pair_outputs

end EthInapproximability.CurrentPaper.RationalSubtractCanonical
