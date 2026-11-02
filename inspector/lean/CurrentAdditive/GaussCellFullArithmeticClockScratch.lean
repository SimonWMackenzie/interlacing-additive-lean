import CurrentAdditive.GaussCanonicalQuotientClockScratch
import CurrentAdditive.GaussCellSubtractCall
import CurrentAdditive.RawRatPostPairCallScratchClock
import CurrentAdditive.RawRatPostPairCallReverseScratchClock

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

namespace CurrentAdditive.GaussCellFullArithmeticClockScratch

open EthInapproximability.CurrentPaper

private noncomputable def Q : BitMachine.Machine :=
  GaussCellQuotient.canonicalMachine

private noncomputable def P : BitMachine.Machine :=
  GaussCellProductRetained.machine

private noncomputable def S : BitMachine.Machine :=
  GaussCellSubtractCall.machine

theorem full_machine_computes_polynomial :
    ∃ (f : List Bool → List Bool) (c : Nat),
      GaussCellSubtractCall.machine.ComputesWithin f
        (fun n => c*(n+1)^(
          19014*(RationalSubtractCanonical.exponent+1))) := by
  obtain ⟨cq,hq⟩ :=
    GaussCanonicalQuotientClockScratch.canonical_computes_polynomial
  obtain ⟨cp,hp⟩ := RationalCanonicalCallback.product_outputs_all
  let fprod := RationalCanonicalCallback.productResult ∘
    RawRatPostPairCallScratch.pairResult Q GaussCellProductCall.rowIndex
      GaussCellQuotient.canonicalResult cq 194
  let aq := 13+cq*(12*Q.pushBound+1)
  let cprod := aq + 2*(aq*(RawRatPostPairCallScratch.pairedMachine Q
      GaussCellProductCall.rowIndex
      GaussCellProductCall.rowIndex_ne_output).pushBound+1) +
    cp*(aq*(RawRatPostPairCallScratch.pairedMachine Q
      GaussCellProductCall.rowIndex
      GaussCellProductCall.rowIndex_ne_output).pushBound+1)^96
  have hprod : P.ComputesWithin fprod
      (fun n => cprod*(n+1)^19012) := by
    have h := RawRatPostPairCallScratch.postPair_then_call_computes_polynomial
      Q RationalCanonicalCallback.productMachine
      GaussCellProductCall.rowIndex
      GaussCellProductCall.rowIndex_ne_output
      GaussCellQuotient.canonicalResult
      RationalCanonicalCallback.productResult cq 194 cp 96
      hq (by intro input; exact hp input)
    simpa only [P, Q, GaussCellProductRetained.machine,
      fprod, cprod, aq,
      show (194+2)*(96+1)=19012 by norm_num] using h
  let ffull := RationalSubtractCanonical.result ∘
    RawRatPostPairCallReverseScratch.pairResult P
      GaussCellProductRetained.savedCurrent fprod cprod 19012
  let ap := 13+cprod*(12*P.pushBound+1)
  let cfull := ap + 2*(ap*(RawRatPostPairCallReverseScratch.pairedMachine P
      GaussCellProductRetained.savedCurrent
      GaussCellSubtractCall.savedCurrent_ne_output).pushBound+1) +
    RationalSubtractCanonical.coefficient *
      (ap*(RawRatPostPairCallReverseScratch.pairedMachine P
        GaussCellProductRetained.savedCurrent
        GaussCellSubtractCall.savedCurrent_ne_output).pushBound+1)^
        RationalSubtractCanonical.exponent
  have hfull : S.ComputesWithin ffull
      (fun n => cfull*(n+1)^(
        19014*(RationalSubtractCanonical.exponent+1))) := by
    have h := RawRatPostPairCallReverseScratch.postPair_then_call_computes_polynomial
      P RationalSubtractCanonical.machine
      GaussCellProductRetained.savedCurrent
      GaussCellSubtractCall.savedCurrent_ne_output
      fprod RationalSubtractCanonical.result cprod 19012
      RationalSubtractCanonical.coefficient
      RationalSubtractCanonical.exponent
      hprod RationalSubtractCanonical.outputsWithin
    simpa only [S, GaussCellSubtractCall.machine,
      ffull, cfull, ap,
      show (19012+2)*(RationalSubtractCanonical.exponent+1) =
        19014*(RationalSubtractCanonical.exponent+1) by norm_num] using h
  exact ⟨ffull,cfull,by simpa only [S] using hfull⟩

theorem full_machine_halts_polynomial :
    ∃ c : Nat, ∀ input : List Bool,
      ∃ output : List Bool,
        GaussCellSubtractCall.machine.OutputsWithin input output
          (c*(input.length+1)^(
            19014*(RationalSubtractCanonical.exponent+1))) := by
  obtain ⟨f,c,h⟩ := full_machine_computes_polynomial
  exact ⟨c,fun input => ⟨f input,h input⟩⟩

theorem full_machine_outputs_valid_cell_uniform :
    ∃ c : Nat, ∀ (current column row pivot : CodeDCodec.RawRat),
      current.Valid → column.Valid → row.Valid → pivot.Valid →
      0 < EncodedCommunication.bitsValue pivot.numerator →
      GaussCellSubtractCall.machine.OutputsWithin
        (GaussPhysical.cellPacket false current column row pivot)
        (CodeDCodec.encodeRawRat
          (GaussCellArithmeticTarget.differenceRaw
            current column row pivot))
        (c*((GaussPhysical.cellPacket false current column row pivot).length+1)^(
          19014*(RationalSubtractCanonical.exponent+1))) := by
  obtain ⟨f,c,h⟩ := full_machine_computes_polynomial
  refine ⟨c,?_⟩
  intro current column row pivot hcurrent hcolumn hrow hpivot hnum
  let input := GaussPhysical.cellPacket false current column row pivot
  let output := CodeDCodec.encodeRawRat
    (GaussCellArithmeticTarget.differenceRaw current column row pivot)
  obtain ⟨T,hvalid⟩ := GaussCellSubtractCall.outputs_cell
    current column row pivot hcurrent hcolumn hrow hpivot hnum
  have heq : f input = output :=
    BitMachine.outputsWithin_unique GaussCellSubtractCall.machine
      (h input) hvalid
  simpa only [input, output, heq] using h input

#print axioms full_machine_computes_polynomial
#print axioms full_machine_halts_polynomial
#print axioms full_machine_outputs_valid_cell_uniform

end CurrentAdditive.GaussCellFullArithmeticClockScratch
