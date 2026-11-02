import CurrentAdditive.GaussBranchBankAtBound
import CurrentAdditive.GaussCompositionRetained

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

/-!
For a nonpivot row, the fixed selector–quotient machine finishes with both
the canonical quotient and the original row entry in different physical
stacks.  The latter is the second operand of the subsequent product call.
-/

namespace CurrentAdditive.GaussCellQuotientRetained

open EthInapproximability.CurrentPaper
open CurrentAdditive.CodeDCodec

private noncomputable abbrev A := GaussPhysical.GaussBranchSelect.machine
private noncomputable abbrev B := RationalCanonicalCallback.quotientMachine

noncomputable def rowIndex : Fin GaussCellQuotient.canonicalMachine.stackCount :=
  Fintype.equivFin (BitMachineComposition.Stack A B)
    (.inl (GaussBranchBankAtBound.wordIndex 3))

noncomputable def currentIndex : Fin GaussCellQuotient.canonicalMachine.stackCount :=
  Fintype.equivFin (BitMachineComposition.Stack A B)
    (.inl (GaussBranchBankAtBound.wordIndex 1))

private theorem rowIndex_ne_output :
    GaussBranchBankAtBound.wordIndex 3 ≠ A.output := by
  intro h
  have he := (Fintype.equivFin GaussPhysical.GaussBranchSelect.Stack).injective h
  have hbad : (Sum.inl (3 : Fin 12) :
      GaussPhysical.GaussBranchSelect.Stack) = .inr 2 := by
    simpa only [GaussBranchBankAtBound.wordIndex,
      A, GaussPhysical.GaussBranchSelect.machine,
      BitMachineEncoding.ofFinite] using he
  cases hbad

private theorem currentIndex_ne_output :
    GaussBranchBankAtBound.wordIndex 1 ≠ A.output := by
  intro h
  have he := (Fintype.equivFin GaussPhysical.GaussBranchSelect.Stack).injective h
  have hbad : (Sum.inl (1 : Fin 12) :
      GaussPhysical.GaussBranchSelect.Stack) = .inr 2 := by
    simpa only [GaussBranchBankAtBound.wordIndex,
      A, GaussPhysical.GaussBranchSelect.machine,
      BitMachineEncoding.ofFinite] using he
  cases hbad

theorem quotient_keeps_row (current column row pivot : RawRat)
    (hcolumn : column.Valid) (hpivot : pivot.Valid)
    (hnum : 0 < EncodedCommunication.bitsValue pivot.numerator) :
    ∃ t, (BitMachineComposition.composition A B).OutputsWithin
      (GaussPhysical.cellPacket false current column row pivot)
      (encodeRawRat (CodeDCanonicalSource.rawOfRat
        (column.value / pivot.value))) t ∧
      ((BitMachineComposition.composition A B).run t
        ((BitMachineComposition.composition A B).init
          (GaussPhysical.cellPacket false current column row pivot))).stk
        (Fintype.equivFin (BitMachineComposition.Stack A B)
          (.inl (GaussBranchBankAtBound.wordIndex 3))) =
        encodeRawRat row ∧
      ((BitMachineComposition.composition A B).run t
        ((BitMachineComposition.composition A B).init
          (GaussPhysical.cellPacket false current column row pivot))).stk
        (Fintype.equivFin (BitMachineComposition.Stack A B)
          (.inl (GaussBranchBankAtBound.wordIndex 1))) =
        encodeRawRat current := by
  let input := GaussPhysical.cellPacket false current column row pivot
  let pair := CodeDPairProductTargetV2.pairBytes column pivot
  let quotient := encodeRawRat
    (CodeDCanonicalSource.rawOfRat (column.value / pivot.value))
  obtain ⟨c,hb⟩ := RationalCanonicalCallback.quotient_outputs_pair
    column pivot hcolumn hpivot hnum
  have ha := GaussPhysical.GaussBranchSelect.outputs_cellPacket
    false current column row pivot
  have hc := BitMachineComposition.composition_outputsWithin A B ha hb
  have hr := GaussCompositionRetained.retained_left_at_bound A B
    ha hb (GaussBranchBankAtBound.wordIndex 3) rowIndex_ne_output
  have hcCurrent := GaussCompositionRetained.retained_left_at_bound A B
    ha hb (GaussBranchBankAtBound.wordIndex 1) currentIndex_ne_output
  have hrow := GaussBranchBankAtBound.row_at_bound_false
    current column row pivot
  have hcurrent := GaussBranchBankAtBound.current_at_bound
    false current column row pivot
  refine ⟨35*(input.length+1) + 2*pair.length+2 +
    c*(pair.length+1)^96, ?_, ?_, ?_⟩
  · simpa only [input, pair, quotient] using hc
  · dsimp only [input, pair]
    simp only [Bool.false_eq_true, ↓reduceIte] at hr
    rw [hr]
    change (A.run (35*((GaussPhysical.cellPacket
      false current column row pivot).length+1))
      (A.init (GaussPhysical.cellPacket
        false current column row pivot))).stk
      (GaussBranchBankAtBound.wordIndex 3) = encodeRawRat row at hrow
    exact hrow
  · dsimp only [input, pair]
    simp only [Bool.false_eq_true, ↓reduceIte] at hcCurrent
    rw [hcCurrent]
    change (A.run (35*((GaussPhysical.cellPacket
      false current column row pivot).length+1))
      (A.init (GaussPhysical.cellPacket
        false current column row pivot))).stk
      (GaussBranchBankAtBound.wordIndex 1) = encodeRawRat current at hcurrent
    exact hcurrent

#print axioms quotient_keeps_row

end CurrentAdditive.GaussCellQuotientRetained
