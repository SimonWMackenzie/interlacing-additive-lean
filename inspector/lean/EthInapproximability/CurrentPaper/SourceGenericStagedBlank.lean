import EthInapproximability.CurrentPaper.SourceGenericFirstRowSuffix

namespace EthInapproximability.CurrentPaper.SourceGenericStagedBlank

open Turing BitMachineEncoding
open scoped Classical

/-- The original physical stage and row reader leave the three writer
accumulators empty. This strengthens the body theorem at its actual witness,
not by modifying an existential bank after the run. -/
theorem body_ready_blank {a q n m : Nat}
    (suffix : List Bool) (rows : Fin m → SourceCSPCodec.Row n a q)
    (hm : 0 < m) (hn : 0 < n)
    (B : SourceCSPFirstRowController.Stack q → List Bool)
    (hsaved : B SourceCSPSecondPassInput.savedSource = suffix)
    (hcap : B SourceCSPSecondPassInput.capSource =
      List.replicate (n - 1) true)
    (hblank : ∀ k : SourceClauseRowWriterOperands.Stack q,
      B (.inr k) = [])
    (hread : SourceCSPCodec.readFn (SourceCSPCodec.readRow n a q) m suffix =
      some (rows, [])) :
    ∃ (t : Nat) (F : SourceCSPStagedFirstRow.ReadControl ×
      (SourceCSPFirstRowController.Stack q → List Bool))
      (rest : List Bool),
      t ≤ SourceCSPFirstRowController.stageBound suffix n +
        SourceCSPFirstRowController.rowBound a q n suffix + 1 ∧
      ((advance (SourceCSPFirstRowController.bodyProgram q a))^[t])
        (⟨some (SourceCSPFirstRowController.bodyStart (q := q) (a := a)),
          SourceCSPFirstRowController.bodyInitial, B⟩ :
          TM2.Cfg (fun _ : SourceCSPFirstRowController.Stack q => Bool)
            (SourceCSPFirstRowController.BodyLabel q a)
            SourceCSPFirstRowController.BodyControl) =
        ⟨none,
          (SourceCSPFirstRowController.stageInitial,
            ((none, none), F.1)), F.2⟩ ∧
      suffix = SourceCSPCodec.rowFields (rows ⟨0, hm⟩) ++ rest ∧
      (∀ j : Fin q,
        SourceCSPFirstSlotBridge.row F.2 (.inl (j, 1)) =
          List.replicate ((rows ⟨0, hm⟩).1 j).val true) ∧
      SourceCSPFirstSlotBridge.row F.2 (.inr 2) =
        true :: List.ofFn (rows ⟨0, hm⟩).2 ∧
      SourceCSPFirstSlotBridge.row F.2 (.inr 0) = rest ∧
      (∀ g : SourceCSPGlobalDecisionProgram.Stack q,
        F.2 (.inl g) = B (.inl g)) ∧
      SourceCSPFirstSlotBridge.writer F.2
        SourceClauseRowWriterOperands.vertex = List.replicate n true ∧
      SourceCSPFirstSlotBridge.writer F.2
        SourceClauseRowWriterOperands.rowIndex = [] ∧
      SourceCSPFirstSlotBridge.writer F.2
        SourceClauseRowWriterCleanup.savedCell = [] ∧
      SourceCSPFirstSlotBridge.writer F.2
        SourceClauseRowWriterCleanup.outputCell = [] ∧
      SourceCSPFirstSlotBridge.writer F.2
        SourceClauseRowWriterCleanup.countCell = [] := by
  obtain ⟨ts, S1, hts, hstage, hglobal,
    hsource, hvertex, hblank1⟩ :=
    SourceCSPTotalSelectiveFrame.stage_input_full_frame
      q B suffix (List.replicate (n - 1) true)
      hsaved hcap hblank
  have hwriter := SourceCSPStagedFirstRow.staged_writer_eq_blank_bank
    q n suffix S1 hn hsource hvertex hblank1
  obtain ⟨tr, F, rest, htr, hrow, hsuffix, _hstatus,
    hunary, hsourceFinal, houtput, hframe⟩ :=
    SourceCSPStagedFirstRow.staged_first_row_run
      suffix rows S1 hn hm hwriter hread
  obtain ⟨t, ht, hrun⟩ := BitMachineRawSequence.runs
    (SourceCSPSecondPassInput.program (q := q))
    (SourceCSPStagedFirstRow.firstRowProgram q a)
    SourceCSPFirstRowController.stageStart
    (SourceCSPFirstRowController.rowStart (q := q) (a := a))
    SourceCSPFirstRowController.stageInitial
    SourceCSPFirstRowController.stageInitial
    SourceCSPFirstRowController.rowInitial ((none, none), F.1)
    B S1 F.2 ts tr hstage hrow
  have hnon (k : SourceClauseRowWriterOperands.Stack q)
      (hk : k = SourceClauseRowWriterOperands.vertex ∨
        k = SourceClauseRowWriterOperands.rowIndex ∨
        k = SourceClauseRowWriterCleanup.savedCell ∨
        k = SourceClauseRowWriterCleanup.outputCell ∨
        k = SourceClauseRowWriterCleanup.countCell) :
      ¬ ∃ x : SourceCSPRowQueryFrame.Stack q,
        SourceCSPStagedFirstRow.rowSlot x = (.inr k :
          SourceCSPFirstRowController.Stack q) := by
    rcases hk with h | h | h | h | h <;> subst k <;>
      rintro ⟨x, hx⟩ <;> cases hx
  have hcell (k : SourceClauseRowWriterOperands.Stack q)
      (hk : k = SourceClauseRowWriterOperands.vertex ∨
        k = SourceClauseRowWriterOperands.rowIndex ∨
        k = SourceClauseRowWriterCleanup.savedCell ∨
        k = SourceClauseRowWriterCleanup.outputCell ∨
        k = SourceClauseRowWriterCleanup.countCell) :
      SourceCSPFirstSlotBridge.writer F.2 k =
        SourceClauseRowWriterBlank.bank
          (SourceCSPRowQueryFrame.initial suffix []) n 0 [] [] [] k := by
    have hv := hframe (.inr k) (hnon k hk)
    have hs := congrFun hwriter k
    change F.2 (.inr k) = _
    rw [hv]
    exact hs
  refine ⟨t, F, rest, ?_, ?_, hsuffix, hunary,
    houtput, hsourceFinal, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold SourceCSPFirstRowController.stageBound
      SourceCSPFirstRowController.rowBound
    simp only [List.length_replicate] at hts
    omega
  · simpa only [SourceCSPFirstRowController.bodyProgram] using hrun
  · intro g
    have hnone : ¬ ∃ x : SourceCSPRowQueryFrame.Stack q,
        SourceCSPStagedFirstRow.rowSlot x =
          (.inl g : SourceCSPFirstRowController.Stack q) := by
      rintro ⟨x, hx⟩
      cases hx
    rw [hframe (.inl g) hnone, hglobal]
  · rw [hcell _ (Or.inl rfl)]
    exact SourceClauseRowWriterBlank.vertex _ n 0 [] [] []
  · rw [hcell _ (Or.inr (Or.inl rfl))]
    exact SourceClauseRowWriterBlank.row_index _ n 0 [] [] []
  · rw [hcell _ (Or.inr (Or.inr (Or.inl rfl)))]
    rfl
  · rw [hcell _ (Or.inr (Or.inr (Or.inr (Or.inl rfl))))]
    rfl
  · rw [hcell _ (Or.inr (Or.inr (Or.inr (Or.inr rfl))))]
    rfl

#print axioms body_ready_blank

/-- The accepted raw validator physically reaches a staged first-row bank
whose saved/output/count cells are still blank. This witness uses the same
input run as the generic first-row controller; no blank bank is postulated. -/
theorem accepted_ready_blank {a q n m : Nat}
    (input suffix : List Bool)
    (rows : Fin m → SourceCSPCodec.Row n a q)
    (tg : Nat)
    (vr : SourceCSPRowLoopController.QueryControl ×
      SourceCSPRowLoopController.ResetControl)
    (S : SourceCSPGlobalDecisionProgram.Stack q → List Bool)
    (hn : 0 < n) (hm : 0 < m)
    (hglobal :
      ((advance (SourceCSPGlobalDecisionProgram.program a q))^[tg])
        (SourceCSPGlobalDecisionProgram.initial a q input) =
          ⟨none, .row (vr, some true), S⟩)
    (hsaved : S SourceCSPGlobalDecisionProgram.savedSource = suffix)
    (hcap : S SourceCSPHeaderRowBridge.capSource =
      List.replicate (n - 1) true)
    (hread : SourceCSPCodec.readFn (SourceCSPCodec.readRow n a q) m suffix =
      some (rows, [])) :
    ∃ (t : Nat) (U : SourceCSPFirstRowController.Stack q → List Bool)
      (rest : List Bool) (v : SourceCSPFirstRowController.Control a q),
      t ≤ tg + 1 + SourceCSPFirstRowController.stageBound suffix n +
        SourceCSPFirstRowController.rowBound a q n suffix + 1 ∧
      ((advance (SourceCSPFirstRowController.program a q))^[t])
        (SourceCSPFirstRowController.initial a q input) =
          ⟨none, v, U⟩ ∧
      suffix = SourceCSPCodec.rowFields (rows ⟨0, hm⟩) ++ rest ∧
      (∀ j : Fin q,
        SourceCSPFirstSlotBridge.row U (.inl (j, 1)) =
          List.replicate ((rows ⟨0, hm⟩).1 j).val true) ∧
      SourceCSPFirstSlotBridge.row U (.inr 2) =
        true :: List.ofFn (rows ⟨0, hm⟩).2 ∧
      SourceCSPFirstSlotBridge.row U (.inr 0) = rest ∧
      (∀ g : SourceCSPGlobalDecisionProgram.Stack q,
        U (.inl g) = S g) ∧
      SourceCSPFirstSlotBridge.writer U
        SourceClauseRowWriterOperands.vertex = List.replicate n true ∧
      SourceCSPFirstSlotBridge.writer U
        SourceClauseRowWriterOperands.rowIndex = [] ∧
      SourceCSPFirstSlotBridge.writer U
        SourceClauseRowWriterCleanup.savedCell = [] ∧
      SourceCSPFirstSlotBridge.writer U
        SourceClauseRowWriterCleanup.outputCell = [] ∧
      SourceCSPFirstSlotBridge.writer U
        SourceClauseRowWriterCleanup.countCell = [] := by
  obtain ⟨u, B, hu, hglobalRun, hleft, hblank⟩ :=
    SourceCSPFirstRowController.global_handoff a q input tg
      (.row (vr, some true)) S hglobal
  have hsavedB : B SourceCSPSecondPassInput.savedSource = suffix := by
    change B (.inl SourceCSPGlobalDecisionProgram.savedSource) = suffix
    exact (hleft _).trans hsaved
  have hcapB : B SourceCSPSecondPassInput.capSource =
      List.replicate (n - 1) true := by
    change B (.inl SourceCSPHeaderRowBridge.capSource) = _
    exact (hleft _).trans hcap
  obtain ⟨tb, F, rest, htb, hbody, hsuffix,
    hunary, htruth, hsource, hglobalFinal,
    hvertexFinal, hindexFinal, hsavedFinal, houtputFinal, hcountFinal⟩ :=
    body_ready_blank suffix rows hm hn B hsavedB hcapB hblank hread
  let cb : TM2.Cfg (fun _ : SourceCSPFirstRowController.Stack q => Bool)
      (SourceCSPFirstRowController.BodyLabel q a)
      SourceCSPFirstRowController.BodyControl :=
    ⟨some (SourceCSPFirstRowController.bodyStart (q := q) (a := a)),
      SourceCSPFirstRowController.bodyInitial, B⟩
  have hbh :
      (((advance (SourceCSPFirstRowController.bodyProgram q a))^[tb]) cb).l =
        none := by
    rw [show cb = (⟨some (SourceCSPFirstRowController.bodyStart
      (q := q) (a := a)), SourceCSPFirstRowController.bodyInitial, B⟩ :
      TM2.Cfg (fun _ : SourceCSPFirstRowController.Stack q => Bool)
        (SourceCSPFirstRowController.BodyLabel q a)
        SourceCSPFirstRowController.BodyControl) by rfl, hbody]
  obtain ⟨vtime, hvtime, hinline⟩ := BitMachineInline.outputs
    BitMachineRawSequence.rightLabel
    (fun w => (SourceCSPSelectiveStage.globalInitialControl a q, w))
    Prod.snd (fun _ => rfl) none
    (SourceCSPFirstRowController.bodyProgram q a)
    (SourceCSPFirstRowController.program a q)
    (by intro l; rfl) cb tb hbh
  have hstart : BitMachineInline.cfg BitMachineRawSequence.rightLabel
      (fun w => (SourceCSPSelectiveStage.globalInitialControl a q, w))
      none cb =
      (⟨some (BitMachineRawSequence.rightLabel
          (SourceCSPFirstRowController.bodyStart (q := q) (a := a))),
        (SourceCSPSelectiveStage.globalInitialControl a q,
          SourceCSPFirstRowController.bodyInitial), B⟩ :
        TM2.Cfg (fun _ : SourceCSPFirstRowController.Stack q => Bool)
          (SourceCSPFirstRowController.Label a q)
          (SourceCSPFirstRowController.Control a q)) := rfl
  have hjoin :
      ((advance (SourceCSPFirstRowController.program a q))^[u + 1 + vtime])
        (SourceCSPFirstRowController.initial a q input) =
      ⟨none,
        (SourceCSPSelectiveStage.globalInitialControl a q,
          (SourceCSPFirstRowController.stageInitial,
            ((none, none), F.1))), F.2⟩ := by
    rw [show u + 1 + vtime = vtime + (u + 1) by omega,
      Function.iterate_add_apply,
      Function.iterate_succ_apply', hglobalRun,
      SourceCSPFirstRowController.handoff_accepted a q vr B,
      ← hstart, hinline,
      show cb = (⟨some (SourceCSPFirstRowController.bodyStart
        (q := q) (a := a)), SourceCSPFirstRowController.bodyInitial, B⟩ :
        TM2.Cfg (fun _ : SourceCSPFirstRowController.Stack q => Bool)
          (SourceCSPFirstRowController.BodyLabel q a)
          SourceCSPFirstRowController.BodyControl) by rfl,
      hbody]
    rfl
  refine ⟨u + 1 + vtime, F.2, rest,
    (SourceCSPSelectiveStage.globalInitialControl a q,
      (SourceCSPFirstRowController.stageInitial,
        ((none, none), F.1))), ?_, hjoin, hsuffix,
    hunary, htruth, hsource, ?_, hvertexFinal, hindexFinal,
    hsavedFinal, houtputFinal, hcountFinal⟩
  · omega
  · intro g
    exact (hglobalFinal g).trans (hleft g)

#print axioms accepted_ready_blank

end EthInapproximability.CurrentPaper.SourceGenericStagedBlank
