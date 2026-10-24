import CurrentAdditive.GaussCellQuotientRetained
import CurrentAdditive.GaussCellArithmeticTarget
import CurrentAdditive.RawRatPostPairCallScratch

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

/-! A fixed quotient, physical pair assembly, and canonical product call. -/

namespace CurrentAdditive.GaussCellProductCall

open EthInapproximability.CurrentPaper
open CurrentAdditive.CodeDCodec

private noncomputable abbrev Q :=
  BitMachineComposition.composition
    GaussPhysical.GaussBranchSelect.machine
    RationalCanonicalCallback.quotientMachine

noncomputable def rowIndex : Fin Q.stackCount :=
  GaussCellQuotientRetained.rowIndex

theorem rowIndex_ne_output : rowIndex ≠ Q.output := by
  intro h
  have he := (Fintype.equivFin
    (BitMachineComposition.Stack
      GaussPhysical.GaussBranchSelect.machine
      RationalCanonicalCallback.quotientMachine)).injective h
  have hbad :
      (Sum.inl (GaussBranchBankAtBound.wordIndex 3) :
        BitMachineComposition.Stack
          GaussPhysical.GaussBranchSelect.machine
          RationalCanonicalCallback.quotientMachine) =
      .inr (.inl RationalCanonicalCallback.quotientMachine.output) := by
    simpa only [rowIndex, Q, GaussCellQuotientRetained.rowIndex,
      BitMachineComposition.composition,
      BitMachineEncoding.ofFinite] using he
  cases hbad

noncomputable def paired : BitMachine.Machine :=
  CurrentAdditive.RawRatPostPairCallScratch.pairedMachine
    Q rowIndex rowIndex_ne_output

noncomputable def pairedCurrentIndex : Fin paired.stackCount :=
  Fintype.equivFin
    (CurrentAdditive.RawRatPostMachinePair.Stack Q)
    (.inl GaussCellQuotientRetained.currentIndex)

noncomputable def machine : BitMachine.Machine :=
  BitMachineComposition.composition paired RationalCanonicalCallback.productMachine

noncomputable def currentIndex : Fin machine.stackCount :=
  Fintype.equivFin
    (BitMachineComposition.Stack paired RationalCanonicalCallback.productMachine)
    (.inl pairedCurrentIndex)

private theorem current_ne_output :
    GaussCellQuotientRetained.currentIndex ≠ Q.output := by
  intro h
  have he := (Fintype.equivFin
    (BitMachineComposition.Stack
      GaussPhysical.GaussBranchSelect.machine
      RationalCanonicalCallback.quotientMachine)).injective h
  have hbad :
      (Sum.inl (GaussBranchBankAtBound.wordIndex 1) :
        BitMachineComposition.Stack
          GaussPhysical.GaussBranchSelect.machine
          RationalCanonicalCallback.quotientMachine) =
      .inr (.inl RationalCanonicalCallback.quotientMachine.output) := by
    simpa only [Q, GaussCellQuotientRetained.currentIndex,
      BitMachineComposition.composition,
      BitMachineEncoding.ofFinite] using he
  cases hbad

private theorem current_ne_row :
    GaussCellQuotientRetained.currentIndex ≠ rowIndex := by
  intro h
  have he := (Fintype.equivFin
    (BitMachineComposition.Stack
      GaussPhysical.GaussBranchSelect.machine
      RationalCanonicalCallback.quotientMachine)).injective h
  have he' : GaussBranchBankAtBound.wordIndex 1 =
      GaussBranchBankAtBound.wordIndex 3 := by
    exact Sum.inl_injective he
  have he'' := (Fintype.equivFin
    GaussPhysical.GaussBranchSelect.Stack).injective he'
  have hbad : (1 : Fin 12) = 3 := by
    exact Sum.inl_injective he''
  cases hbad

theorem outputs_cell (current column row pivot : RawRat)
    (hcolumn : column.Valid) (hrow : row.Valid) (hpivot : pivot.Valid)
    (hnum : 0 < EncodedCommunication.bitsValue pivot.numerator) :
    ∃ T, machine.OutputsWithin
      (GaussPhysical.cellPacket false current column row pivot)
      (encodeRawRat (GaussCellArithmeticTarget.productRaw column row pivot)) T := by
  obtain ⟨t,hq,hs,_⟩ := GaussCellQuotientRetained.quotient_keeps_row
    current column row pivot hcolumn hpivot hnum
  let q := GaussCellArithmeticTarget.quotientRaw column pivot
  obtain ⟨u,hu⟩ := RationalCanonicalCallback.product_outputs_pair q row
    (GaussCellArithmeticTarget.quotient_valid column pivot) hrow
  have hu' : RationalCanonicalCallback.productMachine.OutputsWithin
      (RawRatPairAssembler.pairWord (encodeRawRat q) (encodeRawRat row))
      (encodeRawRat (CodeDCanonicalSource.rawOfRat (q.value*row.value)))
      (u*((CodeDPairProductTargetV2.pairBytes q row).length+1)^96) := by
    simpa only [RawRatPairAssembler.pairWord_exact] using hu
  refine ⟨t + 6*((encodeRawRat q).length+(encodeRawRat row).length+2)+1 +
    2*(CodeDPairProductTargetV2.pairBytes q row).length+2+
    u*((CodeDPairProductTargetV2.pairBytes q row).length+1)^96, ?_⟩
  have h := CurrentAdditive.RawRatPostPairCallScratch.postPair_then_call_outputs
    Q RationalCanonicalCallback.productMachine
    rowIndex rowIndex_ne_output
    (GaussPhysical.cellPacket false current column row pivot)
    (encodeRawRat q) (encodeRawRat row)
    (encodeRawRat (CodeDCanonicalSource.rawOfRat (q.value*row.value)))
    t (u*((CodeDPairProductTargetV2.pairBytes q row).length+1)^96)
    hq hs hu'
  simpa only [machine, paired,
    CurrentAdditive.RawRatPostPairCallScratch.postPair_then_call,
    q, GaussCellArithmeticTarget.productRaw,
    GaussCellArithmeticTarget.quotientRaw,
    RawRatPairAssembler.pairWord_exact] using h

#print axioms outputs_cell

end CurrentAdditive.GaussCellProductCall
