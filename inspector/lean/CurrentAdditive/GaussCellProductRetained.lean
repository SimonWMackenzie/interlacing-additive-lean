import CurrentAdditive.GaussCellProductCall
import CurrentAdditive.RawRatPostPairCallRetainedScratch

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

/-! The original current-entry bytes survive the complete physical product. -/

namespace CurrentAdditive.GaussCellProductRetained

open EthInapproximability.CurrentPaper
open CurrentAdditive.CodeDCodec

private noncomputable abbrev Q :=
  BitMachineComposition.composition
    GaussPhysical.GaussBranchSelect.machine
    RationalCanonicalCallback.quotientMachine

noncomputable def machine : BitMachine.Machine :=
  CurrentAdditive.RawRatPostPairCallScratch.postPair_then_call
    Q RationalCanonicalCallback.productMachine
    GaussCellProductCall.rowIndex GaussCellProductCall.rowIndex_ne_output

noncomputable def savedCurrent : Fin machine.stackCount :=
  Fintype.equivFin
    (BitMachineComposition.Stack
      (CurrentAdditive.RawRatPostPairCallScratch.pairedMachine
        Q GaussCellProductCall.rowIndex
        GaussCellProductCall.rowIndex_ne_output)
      RationalCanonicalCallback.productMachine)
    (.inl (Fintype.equivFin
      (CurrentAdditive.RawRatPostMachinePair.Stack Q)
      (.inl GaussCellQuotientRetained.currentIndex)))

theorem output_and_current (current column row pivot : RawRat)
    (hcolumn : column.Valid) (hrow : row.Valid) (hpivot : pivot.Valid)
    (hnum : 0 < EncodedCommunication.bitsValue pivot.numerator) :
    ∃ T, machine.OutputsWithin
      (GaussPhysical.cellPacket false current column row pivot)
      (encodeRawRat (GaussCellArithmeticTarget.productRaw column row pivot)) T ∧
      (machine.run T
        (machine.init (GaussPhysical.cellPacket false current column row pivot))).stk
        savedCurrent = encodeRawRat current := by
  obtain ⟨t,hq,hs,hc⟩ := GaussCellQuotientRetained.quotient_keeps_row
    current column row pivot hcolumn hpivot hnum
  let q := GaussCellArithmeticTarget.quotientRaw column pivot
  let input := GaussPhysical.cellPacket false current column row pivot
  let pair := RawRatPairAssembler.pairWord
    (encodeRawRat q) (encodeRawRat row)
  let result := encodeRawRat (GaussCellArithmeticTarget.productRaw column row pivot)
  obtain ⟨u,hu⟩ := RationalCanonicalCallback.product_outputs_pair q row
    (GaussCellArithmeticTarget.quotient_valid column pivot) hrow
  have hu' : RationalCanonicalCallback.productMachine.OutputsWithin
      pair result (u*((CodeDPairProductTargetV2.pairBytes q row).length+1)^96) := by
    simpa only [pair, result, GaussCellArithmeticTarget.productRaw,
      GaussCellArithmeticTarget.quotientRaw,
      RawRatPairAssembler.pairWord_exact] using hu
  let U := u*((CodeDPairProductTargetV2.pairBytes q row).length+1)^96
  let T := t + 6*((encodeRawRat q).length+(encodeRawRat row).length+2)+1 +
    2*pair.length+2+U
  have hout := CurrentAdditive.RawRatPostPairCallScratch.postPair_then_call_outputs
    Q RationalCanonicalCallback.productMachine
    GaussCellProductCall.rowIndex GaussCellProductCall.rowIndex_ne_output
    input (encodeRawRat q) (encodeRawRat row) result t U hq hs hu'
  have hsave := CurrentAdditive.RawRatPostPairCallScratch.postPair_then_call_other_at_bound
    Q RationalCanonicalCallback.productMachine
    GaussCellProductCall.rowIndex GaussCellProductCall.rowIndex_ne_output
    input (encodeRawRat q) (encodeRawRat row) result t U hq hs hu'
    GaussCellQuotientRetained.currentIndex
    (by
      intro h
      have he := (Fintype.equivFin
        (BitMachineComposition.Stack
          GaussPhysical.GaussBranchSelect.machine
          RationalCanonicalCallback.quotientMachine)).injective h
      have hbad : (Sum.inl (GaussBranchBankAtBound.wordIndex 1) :
        BitMachineComposition.Stack
          GaussPhysical.GaussBranchSelect.machine
          RationalCanonicalCallback.quotientMachine) =
          .inr (.inl RationalCanonicalCallback.quotientMachine.output) := by
        simpa only [Q, GaussCellQuotientRetained.currentIndex,
          BitMachineComposition.composition,
          BitMachineEncoding.ofFinite] using he
      cases hbad)
    (by
      intro h
      have he := (Fintype.equivFin
        (BitMachineComposition.Stack
          GaussPhysical.GaussBranchSelect.machine
          RationalCanonicalCallback.quotientMachine)).injective h
      have he' : GaussBranchBankAtBound.wordIndex 1 =
          GaussBranchBankAtBound.wordIndex 3 := Sum.inl_injective he
      have he'' := (Fintype.equivFin
        GaussPhysical.GaussBranchSelect.Stack).injective he'
      have hbad : (1 : Fin 12) = 3 := Sum.inl_injective he''
      cases hbad)
  refine ⟨T, ?_, ?_⟩
  · simpa only [machine, input, result, T, pair] using hout
  · have hfinal := hsave.trans hc
    simpa only [machine, savedCurrent, input, T, pair] using hfinal

#print axioms output_and_current

end CurrentAdditive.GaussCellProductRetained
