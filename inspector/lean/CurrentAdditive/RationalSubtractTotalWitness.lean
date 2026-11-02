import CurrentAdditive.RationalSubtractPairMachine

/-! A named fixed all-input witness for the nested-pair subtraction transform. -/

namespace EthInapproximability.CurrentPaper.RationalSubtractTotalWitness

noncomputable def machine : BitMachine.Machine :=
  Classical.choose RationalSubtractPairMachine.total_polytime

noncomputable def coefficient : Nat :=
  Classical.choose (Classical.choose_spec
    RationalSubtractPairMachine.total_polytime)

noncomputable def exponent : Nat :=
  Classical.choose (Classical.choose_spec (Classical.choose_spec
    RationalSubtractPairMachine.total_polytime))

theorem outputsWithin (input : List Bool) :
    machine.OutputsWithin input
      (RationalSubtractPairMachine.totalResult input)
      (coefficient * (input.length+1)^exponent) :=
  (Classical.choose_spec (Classical.choose_spec
    (Classical.choose_spec
      RationalSubtractPairMachine.total_polytime))) input

theorem pair_outputs (a b : CurrentAdditive.CodeDCodec.RawRat) :
    machine.OutputsWithin
      (RationalSubtractPairMachine.pairBytes a b)
      (RationalSubtractClock.result
        (RationalSubtractSpec.canonicalPacket a b))
      (coefficient *
        ((RationalSubtractPairMachine.pairBytes a b).length+1)^exponent) := by
  simpa only [RationalSubtractPairMachine.total_result_pair] using
    outputsWithin (RationalSubtractPairMachine.pairBytes a b)

#print axioms outputsWithin
#print axioms pair_outputs

end EthInapproximability.CurrentPaper.RationalSubtractTotalWitness
