import EthInapproximability.CurrentPaper.SourceGenericFirstRowComposite

/-!
# First-row join: the actual run (unit 1, segment 2)

Paper B, locked v8 Section 6 and Appendix B; CP-SOURCE-EFFECTIVE, arbitrary
fixed alphabet `a`. See `SourceGenericFirstRowComposite` for the program.
-/

namespace EthInapproximability.CurrentPaper.SourceGenericComposite.FirstRow

open Turing BitMachineEncoding BitMachineStackEmbedding
open SourceGenericPrefixMachine PrefixAmbientCopy PrefixAmbientSeed
  PrefixAmbientWork PrefixAmbientInstall
open scoped Classical

theorem hBound_ge {n m a q : Nat} (hq : 0 < q) (hm : 0 < m)
    (rows : Fin m → SourceCSPCodec.Row n a q) (L : Nat) :
    AcceptedSource.envelope a q L ≤ hBound hq hm rows L ∧
      n ≤ hBound hq hm rows L ∧ m ≤ hBound hq hm rows L ∧
      1 + a ^ q ≤ hBound hq hm rows L ∧
      ((EncodedCNF.clauseFields (firstClauses hq hm rows)).reverse ++
        savedWord n a q).length ≤ hBound hq hm rows L ∧
      (List.replicate (firstClauses hq hm rows).length true ++
        countWord n a).length ≤ hBound hq hm rows L := by
  unfold hBound
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega

/-- Segment 2: from the ACTUAL accepting validator halt, the fixed body
(staged first row, ambient generic prefix, row 0 and rows `1..m-1`) reaches
the exact whole bank `finalBank`. Every premise of `first_then_remaining` is
derived here from the reached banks and the typed source readback. -/
theorem body_run {a q : Nat} (hq : 0 < q) (input : List Bool) (tg : Nat)
    (vr : SourceCSPRowLoopController.QueryControl ×
      SourceCSPRowLoopController.ResetControl)
    (S : SourceCSPGlobalDecisionProgram.Stack q → List Bool)
    (hacc : ((advance (SourceCSPGlobalDecisionProgram.program a q))^[tg])
      (SourceCSPGlobalDecisionProgram.initial a q input) =
        ⟨none, .row (vr, some true), S⟩) :
    ∃ (n m : Nat) (hm : 0 < m) (suffix rest : List Bool)
      (rows : Fin m → SourceCSPCodec.Row n a q)
      (U : SourceCSPFirstRowController.Stack q → List Bool)
      (lastRow : SourceCSPRowQueryFrame.Stack q → List Bool) (t : Nat),
      0 < n ∧ n ≤ q * m ∧ m ≤ input.length ∧
      input = SourceCSPHeaderParse.header n m a q ++ suffix ∧
      SourceCSPCodec.readFn (SourceCSPCodec.readRow n a q) m suffix =
        some (rows, []) ∧
      suffix = SourceCSPCodec.rowFields (rows ⟨0, hm⟩) ++ rest ∧
      rest = SourceCSPCodec.fnFields SourceCSPCodec.rowFields
        (SourceGenericAllRowLoop.remainingRows rows 0 (m - 1) (by omega)) ∧
      S SourceCSPHeaderRowBridge.count = List.replicate m true ∧
      S SourceCSPHeaderRowBridge.capSource = List.replicate (n - 1) true ∧
      (∀ g, U (.inl g) = S g) ∧
      SourceCSPFirstSlotBridge.row U (.inr 2) =
        true :: List.ofFn (rows ⟨0, hm⟩).2 ∧
      (∀ j : Fin q, SourceCSPFirstSlotBridge.row U (.inl (j, 1)) =
        List.replicate ((rows ⟨0, hm⟩).1 j).val true) ∧
      SourceCSPFirstSlotBridge.row U (.inr 0) = rest ∧
      SourceCSPFirstSlotBridge.writer U SourceClauseRowWriterOperands.vertex =
        List.replicate n true ∧
      SourceCSPFirstSlotBridge.writer U SourceClauseRowWriterOperands.rowIndex = [] ∧
      SourceCSPFirstSlotBridge.writer U SourceClauseRowWriterCleanup.savedCell = [] ∧
      SourceCSPFirstSlotBridge.writer U SourceClauseRowWriterCleanup.outputCell = [] ∧
      SourceCSPFirstSlotBridge.writer U SourceClauseRowWriterCleanup.countCell = [] ∧
      (∀ x, (U x).length ≤ AcceptedSource.envelope a q input.length) ∧
      t ≤ (SourceCSPFirstRowController.stageBound suffix n +
            SourceCSPFirstRowController.rowBound a q n suffix + 1) +
          (PrefixAmbientProgram.cost n a q +
            suffixClock hq hm rows U input.length + 1) + 1 ∧
      ((advance (program (a := a) hq))^[t])
        (⟨some (BitMachineRawSequence.leftLabel
            (SourceCSPFirstRowController.bodyStart (q := q) (a := a))),
          (SourceCSPFirstRowController.bodyInitial,
            (ambControl a q, suffixStart (a := a) hq)),
          globalBank S⟩ : TM2.Cfg (fun _ : Stack q => Bool) _ _) =
        ⟨none,
          (SourceCSPFirstRowController.bodyInitial,
            (ambControl a q, suffixEnd (a := a) hq)),
          finalBank hq hm rows S U lastRow⟩ ∧
      lastRow (.inr 0) = [] := by
  obtain ⟨tb0, n, m, suffix, rows, htb0, hglob, hn, hm, hsize, hmL,
    hinput, hread, hsaved, hcap, hcount⟩ :=
    AcceptedSource.raw_accepted_source a q input tg vr S hacc
  -- the first-row-controller projection of the validator's terminal bank
  let B : SourceCSPFirstRowController.Stack q → List Bool := frPart (globalBank S)
  have hBeq : B = Sum.elim S (fun _ => []) := globalBank_fr S
  have hsavedB : B SourceCSPSecondPassInput.savedSource = suffix := by
    rw [hBeq]; exact hsaved
  have hcapB : B SourceCSPSecondPassInput.capSource =
      List.replicate (n - 1) true := by
    rw [hBeq]; exact hcap
  have hblank : ∀ k : SourceClauseRowWriterOperands.Stack q, B (.inr k) = [] := by
    intro k; rw [hBeq]; rfl
  obtain ⟨tb, F, rest, htb, hbody, hsuffix, hquery, htruth, hsource, hglobalF,
      hvertex, hindex, hsaved0, houtput0, hcount0⟩ :=
    SourceGenericStagedBlank.body_ready_blank suffix rows hm hn B
      hsavedB hcapB hblank hread
  -- word bounds for the staged bank
  have hsuffixL : suffix.length ≤ input.length := by
    rw [hinput]; simp
  obtain ⟨hstageU, hrowU⟩ := SourceCSPFirstRowController.bounds_le_uniform
    a q n m input.length suffix hsuffixL hsize hmL
  have hglobCells := AcceptedSource.global_cells_le a q input tb0 _ S htb0 hglob
  have hBX : ∀ x, (B x).length ≤ input.length +
      BitMachineStackGrowth.perStep (SourceCSPGlobalDecisionProgram.program a q) *
        (SourceCSPGlobalTotalValidation.totalBound a q input.length + 1) := by
    intro x
    rw [hBeq]
    cases x with
    | inl g => exact hglobCells g
    | inr k => simp
  have hUenv : ∀ x, (F.2 x).length ≤ AcceptedSource.envelope a q input.length :=
    AcceptedSource.stage_cells_le a q _ _ tb B F.2 _ hBX (by omega) hbody
  have hglobalU : ∀ g, F.2 (.inl g) = S g := by
    intro g
    rw [hglobalF g, hBeq]
    rfl
  -- phase A: staged first row, lifted
  have hA0 := BitMachineStackRun.run (frEmb q) (globalBank S)
    (SourceCSPFirstRowController.bodyProgram q a)
    (⟨some (SourceCSPFirstRowController.bodyStart (q := q) (a := a)),
      SourceCSPFirstRowController.bodyInitial, B⟩ :
      TM2.Cfg (fun _ : SourceCSPFirstRowController.Stack q => Bool)
        (SourceCSPFirstRowController.BodyLabel q a)
        SourceCSPFirstRowController.BodyControl) tb
  rw [hbody] at hA0
  have hbankB : bank (frEmb q) (globalBank S) B = globalBank S :=
    bank_eq_self _ _ _ (fun _ => rfl)
  have hA : ((advance (stageProgram a q))^[tb])
      (⟨some (SourceCSPFirstRowController.bodyStart (q := q) (a := a)),
        SourceCSPFirstRowController.bodyInitial, globalBank S⟩ :
        TM2.Cfg (fun _ : Stack q => Bool) _ _) =
      ⟨none, (SourceCSPFirstRowController.stageInitial, ((none, none), F.1)),
        stagedBank S F.2⟩ := by
    simpa only [stageProgram, stackCfg, hbankB, stagedBank] using hA0
  -- phase B: ambient generic prefix, lifted
  obtain ⟨tA, htA, hamb⟩ :=
    PrefixAmbientProgram.run a n F.2 hvertex hsaved0 hcount0
  have hamb' : ((advance (PrefixAmbientProgram.program a q))^[tA])
      (⟨some (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan),
        ambControl a q, initial F.2⟩ :
        TM2.Cfg (fun _ : PrefixAmbientCopy.Stack q => Bool) _ _) =
      ⟨none, ambControl a q, installed F.2 n a⟩ := hamb
  have hB0 := BitMachineStackRun.run (ambEmb q) (stagedBank S F.2)
    (PrefixAmbientProgram.program a q)
    (⟨some (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan),
      ambControl a q, initial F.2⟩ :
      TM2.Cfg (fun _ : PrefixAmbientCopy.Stack q => Bool) _ _) tA
  rw [hamb'] at hB0
  have hB : ((advance (ambientProgram a q))^[tA])
      (⟨some (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan),
        ambControl a q, stagedBank S F.2⟩ :
        TM2.Cfg (fun _ : Stack q => Bool) _ _) =
      ⟨none, ambControl a q, prefixedBank S F.2 n a⟩ := by
    simpa only [ambientProgram, stackCfg, stagedBank_amb, prefixedBank] using hB0
  -- phase C: row 0, clear, remaining rows; all premises derived
  have hge := hBound_ge hq hm rows input.length
  have htruth' : SourceCSPFirstSlotBridge.row (installedRaw F.2 n a) (.inr 2) =
      true :: List.ofFn (rows ⟨0, hm⟩).2 := by
    rw [installedRaw_row]; exact htruth
  have hquery' : ∀ j : Fin q, SourceCSPFirstSlotBridge.row (installedRaw F.2 n a) (.inl (j, 1)) =
      List.replicate ((rows ⟨0, hm⟩).1 j).val true := by
    intro j; rw [installedRaw_row]; exact hquery j
  have hvertex' : SourceCSPFirstSlotBridge.writer (installedRaw F.2 n a)
      SourceClauseRowWriterOperands.vertex = List.replicate n true := by
    rw [installedRaw_vertex]; exact hvertex
  have hindex' : SourceCSPFirstSlotBridge.writer (installedRaw F.2 n a)
      SourceClauseRowWriterOperands.rowIndex = [] := by
    rw [installedRaw_rowIndex]; exact hindex
  have hS' : ∀ x, ((installedRaw F.2 n a) (.inl x)).length ≤ hBound hq hm rows input.length := by
    intro x
    rw [installedRaw_left]
    exact (hUenv _).trans hge.1
  have hrow' : ∀ x, (SourceCSPFirstSlotBridge.row (installedRaw F.2 n a) x).length ≤
      hBound hq hm rows input.length := by
    intro x
    rw [installedRaw_row]
    exact (hUenv _).trans hge.1
  have hsaved' : ((EncodedCNF.clauseFields
      (SourceGenericAllRowLoop.rowClauses rows hq ⟨0, hm⟩)).reverse ++
        SourceCSPFirstSlotBridge.writer (installedRaw F.2 n a)
          SourceClauseRowWriterCleanup.savedCell).length ≤
      hBound hq hm rows input.length := by
    rw [installedRaw_saved]; exact hge.2.2.2.2.1
  have hout' : SourceCSPFirstSlotBridge.writer (installedRaw F.2 n a)
      SourceClauseRowWriterCleanup.outputCell = [] := by
    rw [installedRaw_output]; exact houtput0
  have houtput' : (SourceCSPFirstSlotBridge.writer (installedRaw F.2 n a)
      SourceClauseRowWriterCleanup.outputCell).length ≤
      hBound hq hm rows input.length := by
    rw [hout']; simp
  have hcount' : (List.replicate
      (SourceGenericAllRowLoop.rowClauses rows hq ⟨0, hm⟩).length true ++
        SourceCSPFirstSlotBridge.writer (installedRaw F.2 n a)
          SourceClauseRowWriterCleanup.countCell).length ≤
      hBound hq hm rows input.length := by
    rw [installedRaw_count]; exact hge.2.2.2.2.2
  have hheader' : (installedRaw F.2 n a) (.inl SourceCSPHeaderRowBridge.count) =
      List.replicate m true := by
    rw [installedRaw_left, hglobalU]; exact hcount
  have hcap' : (installedRaw F.2 n a) (.inl SourceCSPHeaderRowBridge.capSource) =
      List.replicate (n - 1) true := by
    rw [installedRaw_left, hglobalU]; exact hcap
  have hrestEq := AcceptedSource.physical_first_rest hm suffix rest rows hread hsuffix
  have hsource' : SourceCSPFirstSlotBridge.row (installedRaw F.2 n a) (.inr 0) =
      SourceCSPCodec.fnFields SourceCSPCodec.rowFields
        (SourceGenericAllRowLoop.remainingRows rows 0 (m - 1) (by omega)) := by
    rw [installedRaw_row, hsource]; exact hrestEq
  obtain ⟨t3, lastRow, ht3, hrun3, hlast⟩ :=
    SourceGenericFirstRowSuffix.first_then_remaining (H := hBound hq hm rows input.length)
      rows hq hn hm (installedRaw F.2 n a) htruth' hquery' hvertex' hindex' n
      (AcceptedSource.rows_query_width rows) (Nat.sub_le n 1)
      hge.2.1 hge.2.2.1 hge.2.2.2.1 hge.2.1
      hS' hrow' hsaved' houtput' hcount' hheader' hcap' hsource'
  have hSeq : (fun g => (installedRaw F.2 n a) (.inl g)) = S := by
    funext g
    rw [installedRaw_left, hglobalU]
  rw [hSeq, installedRaw_saved, hout', installedRaw_count] at hrun3
  have hC0 := BitMachineStackRun.run (fsbEmb q) (prefixedBank S F.2 n a)
    (SourceGenericFirstRowSuffix.callbackClearSuffixProgram (a := a) hq)
    (⟨some (BitMachineRawSequence.leftLabel
        (BitMachineRawSequence.leftLabel
          (BitMachineRawSequence.leftLabel (.clear 0)))),
      suffixStart (a := a) hq, SourceCSPFirstSlotBridge.extended (installedRaw F.2 n a)⟩ :
      TM2.Cfg (fun _ : SourceGenericAllRowLoop.Stack q => Bool) _ _) t3
  rw [show ((advance (SourceGenericFirstRowSuffix.callbackClearSuffixProgram
      (a := a) hq))^[t3])
      (⟨some (BitMachineRawSequence.leftLabel
        (BitMachineRawSequence.leftLabel
          (BitMachineRawSequence.leftLabel (.clear 0)))),
        suffixStart (a := a) hq, SourceCSPFirstSlotBridge.extended (installedRaw F.2 n a)⟩ :
        TM2.Cfg (fun _ : SourceGenericAllRowLoop.Stack q => Bool) _ _) = _
      from hrun3] at hC0
  have hC : ((advance (suffixProgram (a := a) hq))^[t3])
      (⟨some (BitMachineRawSequence.leftLabel
          (BitMachineRawSequence.leftLabel
            (BitMachineRawSequence.leftLabel (.clear 0)))),
        suffixStart (a := a) hq, prefixedBank S F.2 n a⟩ :
        TM2.Cfg (fun _ : Stack q => Bool) _ _) =
      ⟨none, suffixEnd (a := a) hq, finalBank hq hm rows S F.2 lastRow⟩ := by
    simpa only [suffixProgram, stackCfg, prefixedBank_fsb, finalBank,
      restClauses, firstClauses, List.append_assoc] using hC0
  -- sequencing
  obtain ⟨tT, htT, hT⟩ := BitMachineRawSequence.runs
    (ambientProgram a q) (suffixProgram (a := a) hq)
    (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan)
    (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel
        (BitMachineRawSequence.leftLabel (.clear 0))))
    (ambControl a q) (ambControl a q)
    (suffixStart (a := a) hq) (suffixEnd (a := a) hq)
    (stagedBank S F.2) (prefixedBank S F.2 n a)
    (finalBank hq hm rows S F.2 lastRow) tA t3 hB hC
  obtain ⟨T, hT', hR⟩ := BitMachineRawSequence.runs
    (stageProgram a q) (tailProgram (a := a) hq)
    (SourceCSPFirstRowController.bodyStart (q := q) (a := a))
    (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan))
    SourceCSPFirstRowController.bodyInitial
    (SourceCSPFirstRowController.stageInitial, ((none, none), F.1))
    (ambControl a q, suffixStart (a := a) hq)
    (ambControl a q, suffixEnd (a := a) hq)
    (globalBank S) (stagedBank S F.2) (finalBank hq hm rows S F.2 lastRow)
    tb tT hA hT
  have ht3' : t3 ≤ suffixClock hq hm rows F.2 input.length := by
    rw [installedRaw_saved, hout', installedRaw_count] at ht3
    exact ht3
  refine ⟨n, m, hm, suffix, rest, rows, F.2, lastRow, T,
    hn, hsize, hmL, hinput, hread, hsuffix, hrestEq, hcount, hcap,
    hglobalU, htruth, hquery, hsource, hvertex, hindex, hsaved0, houtput0,
    hcount0, hUenv, ?_, hR, hlast⟩
  omega

/-- The raw-input verdict controller with the segment-2 body: from the raw
input, the SAME fixed program validates, stages the first row, runs the
generic prefix and all rows. -/
theorem accepted_first_row_join {a q : Nat} (hq : 0 < q) (input : List Bool)
    (tg : Nat)
    (vr : SourceCSPRowLoopController.QueryControl ×
      SourceCSPRowLoopController.ResetControl)
    (S : SourceCSPGlobalDecisionProgram.Stack q → List Bool)
    (hacc : ((advance (SourceCSPGlobalDecisionProgram.program a q))^[tg])
      (SourceCSPGlobalDecisionProgram.initial a q input) =
        ⟨none, .row (vr, some true), S⟩) :
    ∃ (n m : Nat) (hm : 0 < m) (suffix : List Bool)
      (rows : Fin m → SourceCSPCodec.Row n a q)
      (U : SourceCSPFirstRowController.Stack q → List Bool)
      (lastRow : SourceCSPRowQueryFrame.Stack q → List Bool) (t : Nat),
      0 < n ∧ n ≤ q * m ∧ m ≤ input.length ∧
      input = SourceCSPHeaderParse.header n m a q ++ suffix ∧
      SourceCSPCodec.readFn (SourceCSPCodec.readRow n a q) m suffix =
        some (rows, []) ∧
      t ≤ SourceCSPGlobalTotalValidation.totalBound a q input.length + 1 + 1 +
          ((SourceCSPFirstRowController.stageBound suffix n +
            SourceCSPFirstRowController.rowBound a q n suffix + 1) +
          (PrefixAmbientProgram.cost n a q +
            suffixClock hq hm rows U input.length + 1) + 1) ∧
      ((advance (top a q (program (a := a) hq)
          (BitMachineRawSequence.leftLabel
            (SourceCSPFirstRowController.bodyStart (q := q) (a := a)))
          (SourceCSPFirstRowController.bodyInitial,
            (ambControl a q, suffixStart (a := a) hq))))^[t])
        (topInitial a q
          (SourceCSPFirstRowController.bodyInitial,
            (ambControl a q, suffixStart (a := a) hq)) input) =
        ⟨none, (SourceCSPSelectiveStage.globalInitialControl a q,
          (SourceCSPFirstRowController.bodyInitial,
            (ambControl a q, suffixEnd (a := a) hq))),
          finalBank hq hm rows S U lastRow⟩ := by
  obtain ⟨n, m, hm, suffix, rest, rows, U, lastRow, t, hn, hsize, hmL,
    hinput, hread, _, _, _, _, _, _, _, _, _, _, _, _, _, _, ht, hrun, _⟩ :=
    body_run hq input tg vr S hacc
  obtain ⟨tb0, _, _, _, _, htb0, hglob, _⟩ :=
    AcceptedSource.raw_accepted_source a q input tg vr S hacc
  obtain ⟨T, hT, hR⟩ := top_accepted_run (program (a := a) hq)
    (BitMachineRawSequence.leftLabel
      (SourceCSPFirstRowController.bodyStart (q := q) (a := a)))
    (SourceCSPFirstRowController.bodyInitial,
      (ambControl a q, suffixStart (a := a) hq))
    (SourceCSPFirstRowController.bodyInitial,
      (ambControl a q, suffixEnd (a := a) hq))
    input tb0 vr S hglob t _ hrun
  refine ⟨n, m, hm, suffix, rows, U, lastRow, T, hn, hsize, hmL, hinput,
    hread, ?_, hR⟩
  omega

#print axioms hBound_ge
#print axioms body_run
#print axioms accepted_first_row_join

end EthInapproximability.CurrentPaper.SourceGenericComposite.FirstRow
