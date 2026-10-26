import EthInapproximability.CurrentPaper.SourceGenericConverterSize

/-!
# Polynomial clock of the fixed generic converter (unit 1, segment 5, part 2)

Paper B, locked v8 Section 6 and Appendix B; CP-SOURCE-EFFECTIVE.
The explicit accepted-branch clock of `Converter.accepted_run` is bounded by
`convC a q * (input.length + 1)^27`. The exponent is coarse and deliberately
not sharpened; `convC` is a proof-side function of the fixed `(a,q)` only
(it contains `perStep` constants of fixed programs, the admitted
`cubicCoefficient`, `ambientCoefficient`, `allCoefficient`, `loopCoefficient`
and `UnaryBinaryEncoding.coefficient`).
-/

namespace EthInapproximability.CurrentPaper.SourceGenericComposite.Converter

open Turing BitMachineEncoding BitMachineStackEmbedding
open SourceGenericPrefixMachine PrefixAmbientInstall
open scoped Classical

noncomputable def sufC (a q : Nat) : Nat :=
  SourceClauseClearExcept.workCount (SourceClauseRowWriterCleanup.keep q) +
    SourceClauseGenericAllSlotPolynomial.allCoefficient a q *
      (SourceGenericRowPairCost.rowCellCount q + 1) ^ 2 +
    SourceGenericAllRowLoopClock.loopCoefficient a q + 8

def timeC (a q : Nat) : Nat :=
  (SourceGenericVariableUnary.vertexCoefficient a q +
    SourceGenericVariableUnary.rowCoefficient a q + 2) * (q + 2)

noncomputable def phC (a q : Nat) : Nat :=
  2 * q + 2 + timeC a q + 3 * payC a q + 5 * cntC a q + envC a q +
    UnaryBinaryEncoding.coefficient * (cntC a q + 1) ^ 2 + varC a q + 40

noncomputable def convC (a q : Nat) : Nat :=
  2 * (ctlC a q + 1) +
    PrefixAmbientProgram.ambientCoefficient a q * (q + 1) ^ 9 +
    sufC a q * (hC a q + 1) ^ 9 + phC a q + 5

theorem hBound_le {n m a q L : Nat} (hq : 0 < q) (hm : 0 < m)
    (rows : Fin m → SourceCSPCodec.Row n a q)
    (hsize : n ≤ q * m) (hmL : m ≤ L) :
    FirstRow.hBound hq hm rows L ≤ hC a q * (L + 1) ^ 3 := by
  have hX : 0 < L + 1 := by omega
  have h1 : 1 ≤ (L + 1) ^ 3 := Nat.one_le_pow _ _ hX
  have hX1 : L + 1 ≤ (L + 1) ^ 3 := le_pow_self _ 3 hX (by norm_num)
  have hX2 : (L + 1) ^ 2 ≤ (L + 1) ^ 3 := pow_mono _ 2 3 hX (by norm_num)
  have e1 := envelope_le a q L
  have e2 : n ≤ q * (L + 1) ^ 3 :=
    hsize.trans (Nat.mul_le_mul_left q ((show m ≤ L + 1 by omega).trans hX1))
  have e3 : m ≤ (L + 1) ^ 3 := (show m ≤ L + 1 by omega).trans hX1
  have e4 : 1 + a ^ q ≤ (1 + a ^ q) * (L + 1) ^ 3 := Nat.le_mul_of_pos_right _ h1
  have hpid := congrArg List.length (Payload.payload_identity hq hm rows)
  have hcid := congrArg List.length (Payload.count_identity hq hm rows)
  simp only [List.length_append, List.length_reverse, List.length_replicate] at hpid hcid
  have hp : (SourceGenericOrder.sourceReversePayload
      (SourceCSPCodec.fromRows n m a q rows).system hq).length ≤
      payC a q * (L + 1) ^ 2 :=
    payload_le (n := n) (m := m) (SourceCSPCodec.fromRows n m a q rows).system
      hq hsize hmL
  have hc : SourceGenericOrder.sourceEmittedCount
      (SourceCSPCodec.fromRows n m a q rows).system hq ≤ cntC a q * (L + 1) :=
    cnt_le (n := n) (m := m) (SourceCSPCodec.fromRows n m a q rows).system
      hq hsize hmL
  have e5 : ((EncodedCNF.clauseFields (FirstRow.firstClauses hq hm rows)).reverse ++
      savedWord n a q).length ≤ payC a q * (L + 1) ^ 3 := by
    simp only [List.length_append, List.length_reverse]
    have := Nat.mul_le_mul_left (payC a q) hX2
    omega
  have e6 : (List.replicate (FirstRow.firstClauses hq hm rows).length true ++
      countWord n a).length ≤ cntC a q * (L + 1) ^ 3 := by
    simp only [List.length_append, List.length_replicate]
    have := Nat.mul_le_mul_left (cntC a q) hX1
    omega
  unfold FirstRow.hBound
  calc AcceptedSource.envelope a q L + n + m + (1 + a ^ q) +
        ((EncodedCNF.clauseFields (FirstRow.firstClauses hq hm rows)).reverse ++
          savedWord n a q).length +
        (List.replicate (FirstRow.firstClauses hq hm rows).length true ++
          countWord n a).length
      ≤ envC a q * (L + 1) ^ 3 + q * (L + 1) ^ 3 + (L + 1) ^ 3 +
          (1 + a ^ q) * (L + 1) ^ 3 + payC a q * (L + 1) ^ 3 +
          cntC a q * (L + 1) ^ 3 := by omega
    _ = hC a q * (L + 1) ^ 3 := by unfold hC; ring

theorem suffixClock_le {n m a q L : Nat} (hq : 0 < q) (hm : 0 < m)
    (rows : Fin m → SourceCSPCodec.Row n a q)
    (U : SourceCSPFirstRowController.Stack q → List Bool)
    (hU : ∀ x, (U x).length ≤ AcceptedSource.envelope a q L) :
    FirstRow.suffixClock hq hm rows U L ≤
      sufC a q * (FirstRow.hBound hq hm rows L + 1) ^ 9 := by
  obtain ⟨gE, gn, _, _, gS, gC⟩ := FirstRow.hBound_ge hq hm rows L
  have hsw : (savedWord n a q).length ≤ (FirstRow.hBound hq hm rows L) := by
    simp only [List.length_append] at gS; omega
  have hcw : (countWord n a).length ≤ (FirstRow.hBound hq hm rows L) := by
    simp only [List.length_append] at gC; omega
  have hcells : ∀ x, (FirstRow.installedRaw U n a x).length ≤ (FirstRow.hBound hq hm rows L) := by
    intro x
    by_cases hc : x = .inr SourceClauseRowWriterCleanup.countCell
    · subst hc
      rw [show FirstRow.installedRaw U n a (.inr SourceClauseRowWriterCleanup.countCell) =
        countWord n a from FirstRow.installedRaw_count U n a]
      exact hcw
    · by_cases hs : x = .inr SourceClauseRowWriterCleanup.savedCell
      · subst hs
        rw [show FirstRow.installedRaw U n a (.inr SourceClauseRowWriterCleanup.savedCell) =
          savedWord n a q from FirstRow.installedRaw_saved U n a]
        exact hsw
      · rw [FirstRow.installedRaw_other U n a x hs hc]
        exact (hU x).trans gE
  have hclean := SourceCSPEntryBound.cleanupTime_le (FirstRow.installedRaw U n a) hcells
  have hrow : ∀ x, (SourceCSPFirstSlotBridge.row (FirstRow.installedRaw U n a) x).length ≤ (FirstRow.hBound hq hm rows L) := by
    intro x
    rw [FirstRow.installedRaw_row]
    exact (hU _).trans gE
  have hin := SourceGenericRowPairCost.inputBits_le
    (SourceCSPFirstSlotBridge.row (FirstRow.installedRaw U n a)) n 0
    (savedWord n a q) [] (countWord n a) gn (Nat.zero_le _) hrow hsw
    (by simp) hcw
  have hY : 0 < (FirstRow.hBound hq hm rows L) + 1 := by omega
  have hY1 : (FirstRow.hBound hq hm rows L) + 1 ≤ ((FirstRow.hBound hq hm rows L) + 1) ^ 9 := le_pow_self _ 9 hY (by norm_num)
  have hY0 : 1 ≤ ((FirstRow.hBound hq hm rows L) + 1) ^ 9 := Nat.one_le_pow _ _ hY
  have hY2 : ((FirstRow.hBound hq hm rows L) + 1) ^ 2 ≤ ((FirstRow.hBound hq hm rows L) + 1) ^ 9 := pow_mono _ 2 9 hY (by norm_num)
  have hib : SourceClauseGenericRow.inputBits
      (SourceCSPFirstSlotBridge.row (FirstRow.installedRaw U n a)) n 0
      (savedWord n a q) [] (countWord n a) + 1 ≤ ((SourceGenericRowPairCost.rowCellCount q) + 1) * ((FirstRow.hBound hq hm rows L) + 1) := by
    have e : ((SourceGenericRowPairCost.rowCellCount q) + 1) * ((FirstRow.hBound hq hm rows L) + 1) = (SourceGenericRowPairCost.rowCellCount q) * (FirstRow.hBound hq hm rows L) + (SourceGenericRowPairCost.rowCellCount q) + (FirstRow.hBound hq hm rows L) + 1 := by ring
    omega
  have hsq : (SourceClauseGenericRow.inputBits
      (SourceCSPFirstSlotBridge.row (FirstRow.installedRaw U n a)) n 0
      (savedWord n a q) [] (countWord n a) + 1) ^ 2 ≤ ((SourceGenericRowPairCost.rowCellCount q) + 1) ^ 2 * ((FirstRow.hBound hq hm rows L) + 1) ^ 9 := by
    calc _ ≤ (((SourceGenericRowPairCost.rowCellCount q) + 1) * ((FirstRow.hBound hq hm rows L) + 1)) ^ 2 := Nat.pow_le_pow_left hib 2
      _ = ((SourceGenericRowPairCost.rowCellCount q) + 1) ^ 2 * ((FirstRow.hBound hq hm rows L) + 1) ^ 2 := by ring
      _ ≤ ((SourceGenericRowPairCost.rowCellCount q) + 1) ^ 2 * ((FirstRow.hBound hq hm rows L) + 1) ^ 9 := Nat.mul_le_mul_left _ hY2
  have hA := Nat.mul_le_mul_left (SourceClauseGenericAllSlotPolynomial.allCoefficient a q) hsq
  have hWY : (SourceClauseClearExcept.workCount (SourceClauseRowWriterCleanup.keep q)) * ((FirstRow.hBound hq hm rows L) + 1) ≤ (SourceClauseClearExcept.workCount (SourceClauseRowWriterCleanup.keep q)) * ((FirstRow.hBound hq hm rows L) + 1) ^ 9 := Nat.mul_le_mul_left (SourceClauseClearExcept.workCount (SourceClauseRowWriterCleanup.keep q)) hY1
  unfold FirstRow.suffixClock
  calc SourceCSPFirstSlotBridge.cleanupTime (FirstRow.installedRaw U n a) +
        (SourceClauseGenericAllSlotPolynomial.allCoefficient a q) * (SourceClauseGenericRow.inputBits
          (SourceCSPFirstSlotBridge.row (FirstRow.installedRaw U n a)) n 0
          (savedWord n a q) [] (countWord n a) + 1) ^ 2 +
        (FirstRow.hBound hq hm rows L) + 3 + (SourceGenericAllRowLoopClock.loopCoefficient a q) * ((FirstRow.hBound hq hm rows L) + 1) ^ 9 + 2
      ≤ (SourceClauseClearExcept.workCount (SourceClauseRowWriterCleanup.keep q)) * ((FirstRow.hBound hq hm rows L) + 1) ^ 9 + (SourceClauseGenericAllSlotPolynomial.allCoefficient a q) * (((SourceGenericRowPairCost.rowCellCount q) + 1) ^ 2 * ((FirstRow.hBound hq hm rows L) + 1) ^ 9) +
          8 * ((FirstRow.hBound hq hm rows L) + 1) ^ 9 + (SourceGenericAllRowLoopClock.loopCoefficient a q) * ((FirstRow.hBound hq hm rows L) + 1) ^ 9 := by omega
    _ = sufC a q * ((FirstRow.hBound hq hm rows L) + 1) ^ 9 := by unfold sufC; ring

theorem phaseClock_le {n m a q L V N P O : Nat}
    (hsize : n ≤ q * m) (hmL : m ≤ L)
    (hV : V ≤ varC a q * (L + 1)) (hN : N ≤ cntC a q * (L + 1))
    (hP : P ≤ payC a q * (L + 1) ^ 2) (hO : O ≤ envC a q * (L + 1) ^ 3) :
    phaseClock a q n m V N P O ≤ phC a q * (L + 1) ^ 3 := by
  have hX : 0 < L + 1 := by omega
  have h1 : 1 ≤ (L + 1) ^ 3 := Nat.one_le_pow _ _ hX
  have hX1 : L + 1 ≤ (L + 1) ^ 3 := le_pow_self _ 3 hX (by norm_num)
  have hX2 : (L + 1) ^ 2 ≤ (L + 1) ^ 3 := pow_mono _ 2 3 hX (by norm_num)
  have hn : n ≤ q * (L + 1) ^ 3 :=
    hsize.trans (Nat.mul_le_mul_left q ((show m ≤ L + 1 by omega).trans hX1))
  have hm : m ≤ (L + 1) ^ 3 := (show m ≤ L + 1 by omega).trans hX1
  have ht := SourceGenericVariableUnary.time_linear a q n m
  have hnm : n + m + 1 ≤ (q + 2) * (L + 1) := by
    have : n ≤ q * (L + 1) := hsize.trans (Nat.mul_le_mul_left q (by omega))
    have e : (q + 2) * (L + 1) = q * (L + 1) + (L + 1) + (L + 1) := by ring
    omega
  have htime : SourceGenericVariableUnary.time a q n m ≤ timeC a q * (L + 1) ^ 3 + 2 := by
    have h2 := Nat.mul_le_mul_left
      (SourceGenericVariableUnary.vertexCoefficient a q +
        SourceGenericVariableUnary.rowCoefficient a q + 2) hnm
    have h3 := Nat.mul_le_mul_left (timeC a q) hX1
    have e : (SourceGenericVariableUnary.vertexCoefficient a q +
        SourceGenericVariableUnary.rowCoefficient a q + 2) * ((q + 2) * (L + 1)) =
        timeC a q * (L + 1) := by unfold timeC; ring
    omega
  have hbits : (N.bits).length ≤ N := UnaryBinaryEncoding.bits_length_le N
  have hN3 : N ≤ cntC a q * (L + 1) ^ 3 := hN.trans (Nat.mul_le_mul_left _ hX1)
  have hV3 : V ≤ varC a q * (L + 1) ^ 3 := hV.trans (Nat.mul_le_mul_left _ hX1)
  have hP3 : P ≤ payC a q * (L + 1) ^ 3 := hP.trans (Nat.mul_le_mul_left _ hX2)
  have hN1 : N + 1 ≤ (cntC a q + 1) * (L + 1) := by
    have e : (cntC a q + 1) * (L + 1) = cntC a q * (L + 1) + (L + 1) := by ring
    omega
  have hsq : (N + 1) ^ 2 ≤ (cntC a q + 1) ^ 2 * (L + 1) ^ 3 := by
    calc (N + 1) ^ 2 ≤ ((cntC a q + 1) * (L + 1)) ^ 2 := Nat.pow_le_pow_left hN1 2
      _ = (cntC a q + 1) ^ 2 * (L + 1) ^ 2 := by ring
      _ ≤ (cntC a q + 1) ^ 2 * (L + 1) ^ 3 := Nat.mul_le_mul_left _ hX2
  have hK := Nat.mul_le_mul_left UnaryBinaryEncoding.coefficient hsq
  have h40 : 40 ≤ 40 * (L + 1) ^ 3 := by omega
  unfold phaseClock
  calc _ ≤ 2 * (q * (L + 1) ^ 3) + 2 * (L + 1) ^ 3 + timeC a q * (L + 1) ^ 3 +
          3 * (payC a q * (L + 1) ^ 3) + 5 * (cntC a q * (L + 1) ^ 3) +
          envC a q * (L + 1) ^ 3 +
          UnaryBinaryEncoding.coefficient * ((cntC a q + 1) ^ 2 * (L + 1) ^ 3) +
          varC a q * (L + 1) ^ 3 + 40 * (L + 1) ^ 3 := by omega
    _ = phC a q * (L + 1) ^ 3 := by unfold phC; ring

/-- The explicit accepted-branch clock of `accepted_run`, bounded by one fixed
polynomial of the raw input length. -/
theorem accepted_clock_le {n m a q : Nat} (hq : 0 < q) (hm : 0 < m)
    (input suffix : List Bool) (rows : Fin m → SourceCSPCodec.Row n a q)
    (U : SourceCSPFirstRowController.Stack q → List Bool)
    (S : SourceCSPGlobalDecisionProgram.Stack q → List Bool)
    (hsize : n ≤ q * m) (hmL : m ≤ input.length)
    (hsuffix : suffix.length ≤ input.length)
    (hU : ∀ x, (U x).length ≤ AcceptedSource.envelope a q input.length)
    (hS : (S SourceCSPGlobalDecisionProgram.outputSlot).length ≤
      AcceptedSource.envelope a q input.length) :
    SourceCSPGlobalTotalValidation.totalBound a q input.length + 1 + 1 +
        (((SourceCSPFirstRowController.stageBound suffix n +
            SourceCSPFirstRowController.rowBound a q n suffix + 1) +
          (PrefixAmbientProgram.cost n a q +
            FirstRow.suffixClock hq hm rows U input.length + 1) + 1) +
        phaseClock a q n m
          (SourceGenericOrder.sourceVariables
            (SourceCSPCodec.fromRows n m a q rows).system)
          (SourceGenericOrder.sourceEmittedCount
            (SourceCSPCodec.fromRows n m a q rows).system hq)
          (SourceGenericOrder.sourceReversePayload
            (SourceCSPCodec.fromRows n m a q rows).system hq).length
          (S SourceCSPGlobalDecisionProgram.outputSlot).length + 1) ≤
      convC a q * (input.length + 1) ^ 27 := by
  set L := input.length with hL
  have hX : 0 < L + 1 := by omega
  have h27 : 1 ≤ (L + 1) ^ 27 := Nat.one_le_pow _ _ hX
  have hX3 : (L + 1) ^ 3 ≤ (L + 1) ^ 27 := pow_mono _ 3 27 hX (by norm_num)
  have hX9 : (L + 1) ^ 9 ≤ (L + 1) ^ 27 := pow_mono _ 9 27 hX (by norm_num)
  obtain ⟨hTB, hUB⟩ := controller_parts_le a q L
  obtain ⟨hst, hrw⟩ := SourceCSPFirstRowController.bounds_le_uniform a q n m L suffix
    hsuffix hsize hmL
  -- ambient cost
  have hcost := PrefixAmbientProgram.cost_le_closed n a q
  have hn1 : n + 1 ≤ (q + 1) * (L + 1) := by
    have : n ≤ q * (L + 1) := hsize.trans (Nat.mul_le_mul_left q (by omega))
    have e : (q + 1) * (L + 1) = q * (L + 1) + (L + 1) := by ring
    omega
  have hcost' : PrefixAmbientProgram.cost n a q ≤
      PrefixAmbientProgram.ambientCoefficient a q * (q + 1) ^ 9 * (L + 1) ^ 27 := by
    calc PrefixAmbientProgram.cost n a q
        ≤ PrefixAmbientProgram.ambientCoefficient a q * (n + 1) ^ 9 := hcost
      _ ≤ PrefixAmbientProgram.ambientCoefficient a q * ((q + 1) * (L + 1)) ^ 9 := by
          gcongr
      _ = PrefixAmbientProgram.ambientCoefficient a q * (q + 1) ^ 9 * (L + 1) ^ 9 := by
          ring
      _ ≤ _ := Nat.mul_le_mul_left _ hX9
  -- suffix clock
  have hsuf := suffixClock_le hq hm rows U hU
  have hHb := hBound_le hq hm rows hsize hmL
  have hH1 : FirstRow.hBound hq hm rows L + 1 ≤ (hC a q + 1) * (L + 1) ^ 3 := by
    have : 1 ≤ (L + 1) ^ 3 := Nat.one_le_pow _ _ hX
    have e : (hC a q + 1) * (L + 1) ^ 3 = hC a q * (L + 1) ^ 3 + (L + 1) ^ 3 := by ring
    omega
  have hsuf' : FirstRow.suffixClock hq hm rows U L ≤
      sufC a q * (hC a q + 1) ^ 9 * (L + 1) ^ 27 := by
    calc FirstRow.suffixClock hq hm rows U L
        ≤ sufC a q * (FirstRow.hBound hq hm rows L + 1) ^ 9 := hsuf
      _ ≤ sufC a q * ((hC a q + 1) * (L + 1) ^ 3) ^ 9 := by gcongr
      _ = sufC a q * (hC a q + 1) ^ 9 * (L + 1) ^ 27 := by ring
  -- phase clock
  have hph := phaseClock_le (a := a) (q := q) (n := n) (m := m) (L := L) hsize hmL
    (vars_le (n := n) (m := m) (SourceCSPCodec.fromRows n m a q rows).system hsize hmL)
    (cnt_le (n := n) (m := m) (SourceCSPCodec.fromRows n m a q rows).system hq hsize hmL)
    (payload_le (n := n) (m := m) (SourceCSPCodec.fromRows n m a q rows).system hq hsize hmL)
    (hS.trans (envelope_le a q L))
  have hph' := hph.trans (Nat.mul_le_mul_left (phC a q) hX3)
  have hTB' : SourceCSPGlobalTotalValidation.totalBound a q L + 1 ≤
      (ctlC a q + 1) * (L + 1) ^ 27 := hTB.trans (Nat.mul_le_mul_left _ hX3)
  have hUB' : SourceCSPFirstRowController.uniformStageBound q L +
        SourceCSPFirstRowController.uniformRowBound a q L + 1 ≤
      (ctlC a q + 1) * (L + 1) ^ 27 := hUB.trans (Nat.mul_le_mul_left _ hX3)
  have e : convC a q * (L + 1) ^ 27 =
      2 * ((ctlC a q + 1) * (L + 1) ^ 27) +
      PrefixAmbientProgram.ambientCoefficient a q * (q + 1) ^ 9 * (L + 1) ^ 27 +
      sufC a q * (hC a q + 1) ^ 9 * (L + 1) ^ 27 + phC a q * (L + 1) ^ 27 +
      5 * (L + 1) ^ 27 := by
    unfold convC; ring
  have hph'' : phaseClock a q n m
      (SourceGenericOrder.sourceVariables (SourceCSPCodec.fromRows n m a q rows).system)
      (SourceGenericOrder.sourceEmittedCount
        (SourceCSPCodec.fromRows n m a q rows).system hq)
      (SourceGenericOrder.sourceReversePayload
        (SourceCSPCodec.fromRows n m a q rows).system hq).length
      (S SourceCSPGlobalDecisionProgram.outputSlot).length ≤
      phC a q * (L + 1) ^ 27 := hph'
  rw [e]
  omega

#print axioms hBound_le
#print axioms suffixClock_le
#print axioms phaseClock_le
#print axioms accepted_clock_le

end EthInapproximability.CurrentPaper.SourceGenericComposite.Converter
