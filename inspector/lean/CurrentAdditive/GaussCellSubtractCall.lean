import CurrentAdditive.GaussCellProductRetained
import CurrentAdditive.RawRatPostPairCallReverseScratch
import CurrentAdditive.RationalSubtractCanonical

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

/-! Fixed physical quotient, product, and subtraction for a nonpivot cell. -/

namespace CurrentAdditive.GaussCellSubtractCall

open EthInapproximability.CurrentPaper
open CurrentAdditive.CodeDCodec

private noncomputable abbrev P := GaussCellProductRetained.machine

theorem savedCurrent_ne_output :
    GaussCellProductRetained.savedCurrent ≠ P.output := by
  intro h
  have he := (Fintype.equivFin
    (BitMachineComposition.Stack
      (CurrentAdditive.RawRatPostPairCallScratch.pairedMachine
        (BitMachineComposition.composition
          GaussPhysical.GaussBranchSelect.machine
          RationalCanonicalCallback.quotientMachine)
        GaussCellProductCall.rowIndex
        GaussCellProductCall.rowIndex_ne_output)
      RationalCanonicalCallback.productMachine)).injective h
  have hbad :
      (Sum.inl (Fintype.equivFin
        (CurrentAdditive.RawRatPostMachinePair.Stack
          (BitMachineComposition.composition
            GaussPhysical.GaussBranchSelect.machine
            RationalCanonicalCallback.quotientMachine))
        (.inl GaussCellQuotientRetained.currentIndex)) :
        BitMachineComposition.Stack
          (CurrentAdditive.RawRatPostPairCallScratch.pairedMachine
            (BitMachineComposition.composition
              GaussPhysical.GaussBranchSelect.machine
              RationalCanonicalCallback.quotientMachine)
            GaussCellProductCall.rowIndex
            GaussCellProductCall.rowIndex_ne_output)
          RationalCanonicalCallback.productMachine) =
      .inr (.inl RationalCanonicalCallback.productMachine.output) := by
    simpa only [P, GaussCellProductRetained.machine,
      GaussCellProductRetained.savedCurrent,
      BitMachineComposition.composition,
      BitMachineEncoding.ofFinite] using he
  cases hbad

noncomputable def machine : BitMachine.Machine :=
  CurrentAdditive.RawRatPostPairCallReverseScratch.postPair_then_call
    P RationalSubtractCanonical.machine
    GaussCellProductRetained.savedCurrent savedCurrent_ne_output

theorem outputs_cell (current column row pivot : RawRat)
    (hcurrent : current.Valid) (hcolumn : column.Valid)
    (hrow : row.Valid) (hpivot : pivot.Valid)
    (hnum : 0 < EncodedCommunication.bitsValue pivot.numerator) :
    ∃ T, machine.OutputsWithin
      (GaussPhysical.cellPacket false current column row pivot)
      (encodeRawRat
        (GaussCellArithmeticTarget.differenceRaw current column row pivot)) T := by
  obtain ⟨t,hp,hs⟩ := GaussCellProductRetained.output_and_current
    current column row pivot hcolumn hrow hpivot hnum
  let p := GaussCellArithmeticTarget.productRaw column row pivot
  let input := GaussPhysical.cellPacket false current column row pivot
  let pair := RawRatPairAssembler.pairWord
    (encodeRawRat current) (encodeRawRat p)
  have hb := RationalSubtractCanonical.canonical_pair_outputs
    current p hcurrent (GaussCellArithmeticTarget.product_valid column row pivot)
  have hb' : RationalSubtractCanonical.machine.OutputsWithin pair
      (encodeRawRat (GaussCellArithmeticTarget.differenceRaw
        current column row pivot))
      (RationalSubtractCanonical.coefficient *
        ((RationalSubtractPairMachine.pairBytes current p).length+1)^
          RationalSubtractCanonical.exponent) := by
    simpa only [pair, GaussCellArithmeticTarget.differenceRaw,
      RawRatPairAssembler.pairWord_exact] using hb
  let U := RationalSubtractCanonical.coefficient *
    ((RationalSubtractPairMachine.pairBytes current p).length+1)^
      RationalSubtractCanonical.exponent
  refine ⟨t + 6*((encodeRawRat p).length+(encodeRawRat current).length+2)+1 +
    2*pair.length+2+U, ?_⟩
  have h := CurrentAdditive.RawRatPostPairCallReverseScratch.postPair_then_call_outputs
    P RationalSubtractCanonical.machine
    GaussCellProductRetained.savedCurrent savedCurrent_ne_output
    input (encodeRawRat p) (encodeRawRat current)
    (encodeRawRat (GaussCellArithmeticTarget.differenceRaw
      current column row pivot)) t U hp hs hb'
  simpa only [machine, input, pair, p, U,
    CurrentAdditive.RawRatPostPairCallReverseScratch.postPair_then_call]
    using h

#print axioms outputs_cell

end CurrentAdditive.GaussCellSubtractCall
