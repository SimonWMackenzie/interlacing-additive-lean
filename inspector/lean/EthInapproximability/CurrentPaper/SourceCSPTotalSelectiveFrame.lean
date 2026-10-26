import EthInapproximability.CurrentPaper.SourceCSPTotalSelective

/-! Physical bank frame for the accepted second-pass staging machine. -/

namespace EthInapproximability.CurrentPaper.SourceCSPTotalSelectiveFrame

open Turing BitMachineEncoding BitMachineStackEmbedding

/-- The staging machine reads the entire left/global bank without changing
any of it. On the right/writer bank it changes only the literal row-source
and vertex cells; every other writer cell remains blank. -/
theorem stage_input_full_frame (q : Nat)
    (before : SourceCSPSecondPassInput.Stack q → List Bool)
    (suffix cap : List Bool)
    (hsaved : before SourceCSPSecondPassInput.savedSource = suffix)
    (hcap : before SourceCSPSecondPassInput.capSource = cap)
    (hblank : ∀ k : SourceClauseRowWriterOperands.Stack q,
      before (.inr k) = []) :
    ∃ t S,
      t ≤ (2 * suffix.length + 2) + (2 * cap.length + 2) + 3 ∧
      ((advance (SourceCSPSecondPassInput.program (q := q)))^[t])
        (⟨some (.inl (.inl .scan)), ((none, none), ()), before⟩ :
          TM2.Cfg (fun _ : SourceCSPSecondPassInput.Stack q => Bool)
            SourceCSPSecondPassInput.Label
            SourceCSPSecondPassInput.Control) =
        ⟨none, ((none, none), ()), S⟩ ∧
      (∀ k : SourceCSPGlobalDecisionProgram.Stack q,
        S (.inl k) = before (.inl k)) ∧
      S SourceCSPSecondPassInput.writerSource = suffix ∧
      S SourceCSPSecondPassInput.writerVertex = true :: cap ∧
      (∀ k : SourceClauseRowWriterOperands.Stack q,
        (.inr k : SourceCSPSecondPassInput.Stack q) ≠
          SourceCSPSecondPassInput.writerSource →
        (.inr k : SourceCSPSecondPassInput.Stack q) ≠
          SourceCSPSecondPassInput.writerVertex →
        S (.inr k) = []) := by
  obtain ⟨ts, S1, hts, hrs, hs1, hsource1, hwork1, hother1⟩ :=
    SourceCSPSecondPassInput.source_copy q before suffix
      hsaved (hblank _) (hblank _)
  have hcap1 : S1 SourceCSPSecondPassInput.capSource = cap :=
    (hother1 SourceCSPSecondPassInput.capSource
      (by simp [SourceCSPSecondPassInput.capSource,
        SourceCSPSecondPassInput.savedSource,
        SourceCSPGlobalDecisionProgram.savedSource,
        SourceCSPHeaderRowBridge.capSource,
        SourceCSPHeaderRowBridge.scratch])
      (by simp [SourceCSPSecondPassInput.capSource,
        SourceCSPSecondPassInput.writerSource])
      (by simp [SourceCSPSecondPassInput.capSource,
        SourceCSPSecondPassInput.work])).trans hcap
  have hvertex1 : S1 SourceCSPSecondPassInput.writerVertex = [] :=
    (hother1 SourceCSPSecondPassInput.writerVertex
      (by simp [SourceCSPSecondPassInput.writerVertex,
        SourceCSPSecondPassInput.savedSource])
      (by simp [SourceCSPSecondPassInput.writerVertex,
        SourceCSPSecondPassInput.writerSource,
        SourceClauseRowWriterCleanup.rowCell,
        SourceClauseRowWriterOperands.vertex])
      (by simp [SourceCSPSecondPassInput.writerVertex,
        SourceCSPSecondPassInput.work,
        SourceClauseRowWriterOperands.vertex,
        SourceClauseRowWriterOperands.scratch])).trans (hblank _)
  obtain ⟨tv, S2, htv, hrv, hcap2, hvertex2, hwork2, hother2⟩ :=
    SourceCSPSecondPassInput.vertex_copy q S1 cap
      hcap1 hvertex1 hwork1
  have hsource2 : S2 SourceCSPSecondPassInput.writerSource = suffix :=
    (hother2 SourceCSPSecondPassInput.writerSource
      (by simp [SourceCSPSecondPassInput.writerSource,
        SourceCSPSecondPassInput.capSource])
      (by simp [SourceCSPSecondPassInput.writerSource,
        SourceCSPSecondPassInput.writerVertex,
        SourceClauseRowWriterCleanup.rowCell,
        SourceClauseRowWriterOperands.vertex])
      (by simp [SourceCSPSecondPassInput.writerSource,
        SourceCSPSecondPassInput.work,
        SourceClauseRowWriterCleanup.rowCell,
        SourceClauseRowWriterOperands.scratch])).trans hsource1
  let S3 := Function.update S2 SourceCSPSecondPassInput.writerVertex
    (true :: cap)
  have hpush : ((advance
      (SourceCSPSecondPassInput.addVertexProgram (q := q)))^[1])
      (⟨some (), (), S2⟩ :
        TM2.Cfg (fun _ : SourceCSPSecondPassInput.Stack q => Bool)
          Unit Unit) =
      ⟨none, (), S3⟩ := by
    simp [advance, TM2.step, TM2.stepAux,
      SourceCSPSecondPassInput.addVertexProgram,
      S3, hvertex2]
  obtain ⟨t12, ht12, hr12⟩ := BitMachineRawSequence.runs
    (SourceCSPSecondPassInput.sourceCopyProgram (q := q))
    (SourceCSPSecondPassInput.vertexCopyProgram (q := q))
    .scan .scan none none none none before S1 S2 ts tv hrs hrv
  obtain ⟨t, ht, hr⟩ := BitMachineRawSequence.runs
    (SourceCSPSecondPassInput.copyPairProgram (q := q))
    (SourceCSPSecondPassInput.addVertexProgram (q := q))
    (.inl .scan : SourceCSPSecondPassInput.CopyPairLabel)
    () (none, none) (none, none) () ()
    before S2 S3 t12 1
    (by simpa only [SourceCSPSecondPassInput.copyPairProgram] using hr12)
    hpush
  have hglobal1 : ∀ k : SourceCSPGlobalDecisionProgram.Stack q,
      S1 (.inl k) = before (.inl k) := by
    intro k
    by_cases hk : k = SourceCSPGlobalDecisionProgram.savedSource
    · subst k
      exact hs1.trans hsaved.symm
    · exact hother1 (.inl k)
        (by simpa [SourceCSPSecondPassInput.savedSource] using hk)
        (by simp [SourceCSPSecondPassInput.writerSource])
        (by simp [SourceCSPSecondPassInput.work])
  have hglobal2 : ∀ k : SourceCSPGlobalDecisionProgram.Stack q,
      S2 (.inl k) = before (.inl k) := by
    intro k
    by_cases hk : k = SourceCSPHeaderRowBridge.capSource
    · subst k
      exact hcap2.trans hcap.symm
    · exact (hother2 (.inl k)
        (by simpa [SourceCSPSecondPassInput.capSource] using hk)
        (by simp [SourceCSPSecondPassInput.writerVertex])
        (by simp [SourceCSPSecondPassInput.work])).trans (hglobal1 k)
  have hglobal3 : ∀ k : SourceCSPGlobalDecisionProgram.Stack q,
      S3 (.inl k) = before (.inl k) := by
    intro k
    simpa only [S3, Function.update_of_ne
      (by simp [SourceCSPSecondPassInput.writerVertex] :
        (.inl k : SourceCSPSecondPassInput.Stack q) ≠
          SourceCSPSecondPassInput.writerVertex)] using hglobal2 k
  have hwriter3 : ∀ k : SourceClauseRowWriterOperands.Stack q,
      (.inr k : SourceCSPSecondPassInput.Stack q) ≠
        SourceCSPSecondPassInput.writerSource →
      (.inr k : SourceCSPSecondPassInput.Stack q) ≠
        SourceCSPSecondPassInput.writerVertex →
      S3 (.inr k) = [] := by
    intro k hkSource hkVertex
    have hnotVertex : S3 (.inr k) = S2 (.inr k) := by
      simp [S3, Function.update_of_ne hkVertex]
    rw [hnotVertex]
    by_cases hkWork : (.inr k : SourceCSPSecondPassInput.Stack q) =
        SourceCSPSecondPassInput.work
    · rw [hkWork, hwork2]
    · have hS1 : S1 (.inr k) = [] :=
        (hother1 (.inr k)
          (by simp [SourceCSPSecondPassInput.savedSource])
          hkSource hkWork).trans (hblank k)
      exact (hother2 (.inr k)
        (by simp [SourceCSPSecondPassInput.capSource])
        hkVertex hkWork).trans hS1
  refine ⟨t, S3, ?_, ?_, hglobal3, ?_, ?_, hwriter3⟩
  · omega
  · simpa only [SourceCSPSecondPassInput.program] using hr
  · simpa [S3, SourceCSPSecondPassInput.writerVertex,
      SourceCSPSecondPassInput.writerSource,
      SourceClauseRowWriterCleanup.rowCell,
      SourceClauseRowWriterOperands.vertex] using hsource2
  · simp [S3]



/-- From an actual accepted global halt, the selective table physically
stages the saved suffix and cap while preserving the entire global bank.
Only the two intended writer cells become nonblank. -/
theorem accepted_terminal_full_frame (a q : Nat) (input : List Bool)
    (t : Nat) (S : SourceCSPGlobalDecisionProgram.Stack q → List Bool)
    (vr : SourceCSPRowLoopController.QueryControl ×
      SourceCSPRowLoopController.ResetControl)
    (suffix cap : List Bool)
    (hrun : ((advance (SourceCSPGlobalDecisionProgram.program a q))^[t])
      (SourceCSPGlobalDecisionProgram.initial a q input) =
        ⟨none, .row (vr, some true), S⟩)
    (hsaved : S SourceCSPGlobalDecisionProgram.savedSource = suffix)
    (hcap : S SourceCSPHeaderRowBridge.capSource = cap) :
    ∃ (u : Nat) (U : SourceCSPSelectiveStage.Stack q → List Bool),
      u ≤ t + 1 +
        ((2 * suffix.length + 2) + (2 * cap.length + 2) + 3) ∧
      ((advance (SourceCSPSelectiveStage.program a q))^[u])
        (SourceCSPSelectiveStage.initial a q input) =
          ⟨none, (SourceCSPSelectiveStage.globalInitialControl a q,
            SourceCSPSelectiveStage.stageInitialControl), U⟩ ∧
      (∀ k : SourceCSPGlobalDecisionProgram.Stack q,
        U (.inl k) = S k) ∧
      U SourceCSPSecondPassInput.writerSource = suffix ∧
      U SourceCSPSecondPassInput.writerVertex = true :: cap ∧
      (∀ k : SourceClauseRowWriterOperands.Stack q,
        (.inr k : SourceCSPSelectiveStage.Stack q) ≠
          SourceCSPSecondPassInput.writerSource →
        (.inr k : SourceCSPSelectiveStage.Stack q) ≠
          SourceCSPSecondPassInput.writerVertex →
        U (.inr k) = []) := by
  obtain ⟨ug, T, hug, hglobal, hleft, hblank⟩ :=
    SourceCSPSelectiveStage.lift_global_terminal a q input t
      (.row (vr, some true)) S hrun
  have hsavedT : T SourceCSPSecondPassInput.savedSource = suffix :=
    (hleft SourceCSPGlobalDecisionProgram.savedSource).trans hsaved
  have hcapT : T SourceCSPSecondPassInput.capSource = cap :=
    (hleft SourceCSPHeaderRowBridge.capSource).trans hcap
  obtain ⟨ts, U, hts, hrstage, hglobalStage, hsourceU,
    hvertexU, hwriterU⟩ :=
    stage_input_full_frame q T suffix cap hsavedT hcapT hblank
  have hhalt : (((advance (SourceCSPSecondPassInput.program (q := q)))^[ts])
      (⟨some SourceCSPSelectiveStage.stageInitialLabel,
        SourceCSPSelectiveStage.stageInitialControl, T⟩ :
        TM2.Cfg (fun _ : SourceCSPSelectiveStage.Stack q => Bool)
          SourceCSPSelectiveStage.StageLabel
          SourceCSPSelectiveStage.StageControl)).l = none := by
    rw [show SourceCSPSelectiveStage.stageInitialLabel =
      (.inl (.inl .scan) : SourceCSPSelectiveStage.StageLabel) by rfl]
    rw [show SourceCSPSelectiveStage.stageInitialControl =
      (((none, none), ()) : SourceCSPSelectiveStage.StageControl) by rfl]
    rw [hrstage]
  obtain ⟨us, hus, hstage⟩ := BitMachineInline.outputs
    BitMachineRawSequence.rightLabel
    (fun w => (SourceCSPSelectiveStage.globalInitialControl a q, w))
    Prod.snd (fun _ => rfl) none
    (SourceCSPSecondPassInput.program (q := q))
    (SourceCSPSelectiveStage.program a q)
    (fun _ => rfl)
    (⟨some SourceCSPSelectiveStage.stageInitialLabel,
      SourceCSPSelectiveStage.stageInitialControl, T⟩ :
      TM2.Cfg (fun _ : SourceCSPSelectiveStage.Stack q => Bool)
        SourceCSPSelectiveStage.StageLabel
        SourceCSPSelectiveStage.StageControl)
    ts hhalt
  have hrstage' : ((advance (SourceCSPSecondPassInput.program (q := q)))^[ts])
      (⟨some SourceCSPSelectiveStage.stageInitialLabel,
        SourceCSPSelectiveStage.stageInitialControl, T⟩ :
        TM2.Cfg (fun _ : SourceCSPSelectiveStage.Stack q => Bool)
          SourceCSPSelectiveStage.StageLabel
          SourceCSPSelectiveStage.StageControl) =
      ⟨none, SourceCSPSelectiveStage.stageInitialControl, U⟩ := hrstage
  rw [hrstage'] at hstage
  have hstageRun : ((advance (SourceCSPSelectiveStage.program a q))^[us])
      (⟨some (.inr (.inr SourceCSPSelectiveStage.stageInitialLabel)),
        (SourceCSPSelectiveStage.globalInitialControl a q,
          SourceCSPSelectiveStage.stageInitialControl), T⟩ :
        TM2.Cfg (fun _ : SourceCSPSelectiveStage.Stack q => Bool)
          (SourceCSPSelectiveStage.Label a q)
          (SourceCSPSelectiveStage.Control a q)) =
      ⟨none, (SourceCSPSelectiveStage.globalInitialControl a q,
        SourceCSPSelectiveStage.stageInitialControl), U⟩ := by
    simpa only [BitMachineInline.cfg, Option.map_none] using hstage
  have hdispatch := SourceCSPSelectiveStage.handoff_accept a q vr
    SourceCSPSelectiveStage.stageInitialControl T
  refine ⟨ug + 1 + us, U, ?_, ?_, ?_, hsourceU,
    hvertexU, hwriterU⟩
  · omega
  · rw [show ug + 1 + us = us + (1 + ug) by omega,
      Function.iterate_add_apply,
      Function.iterate_add_apply, hglobal]
    simp only [Function.iterate_one]
    rw [hdispatch]
    exact hstageRun
  · intro k
    exact (hglobalStage k).trans (hleft k)



/-- An already-established selective terminal run on accepted global data
must be the same terminal bank as the explicitly constructed framed run. -/
theorem accepted_any_run_full_frame (a q : Nat) (input : List Bool)
    (tg ts : Nat)
    (S : SourceCSPGlobalDecisionProgram.Stack q → List Bool)
    (vr : SourceCSPRowLoopController.QueryControl ×
      SourceCSPRowLoopController.ResetControl)
    (suffix cap : List Bool)
    (d : SourceCSPSelectiveStage.Control a q)
    (U : SourceCSPSelectiveStage.Stack q → List Bool)
    (hglobal : ((advance (SourceCSPGlobalDecisionProgram.program a q))^[tg])
      (SourceCSPGlobalDecisionProgram.initial a q input) =
        ⟨none, .row (vr, some true), S⟩)
    (hsaved : S SourceCSPGlobalDecisionProgram.savedSource = suffix)
    (hcap : S SourceCSPHeaderRowBridge.capSource = cap)
    (hselect : ((advance (SourceCSPSelectiveStage.program a q))^[ts])
      (SourceCSPSelectiveStage.initial a q input) =
        ⟨none, d, U⟩) :
    d = (SourceCSPSelectiveStage.globalInitialControl a q,
      SourceCSPSelectiveStage.stageInitialControl) ∧
    (∀ k : SourceCSPGlobalDecisionProgram.Stack q,
      U (.inl k) = S k) ∧
    U SourceCSPSecondPassInput.writerSource = suffix ∧
    U SourceCSPSecondPassInput.writerVertex = true :: cap ∧
    (∀ k : SourceClauseRowWriterOperands.Stack q,
      (.inr k : SourceCSPSelectiveStage.Stack q) ≠
        SourceCSPSecondPassInput.writerSource →
      (.inr k : SourceCSPSelectiveStage.Stack q) ≠
        SourceCSPSecondPassInput.writerVertex →
      U (.inr k) = []) := by
  obtain ⟨u, T, _, hrun, hleft, hsource, hvertex, hblank⟩ :=
    accepted_terminal_full_frame a q input tg S vr suffix cap
      hglobal hsaved hcap
  have heq := SourceCSPRowLoopTotalHaltCompare.halted_unique
    (SourceCSPSelectiveStage.program a q)
    (SourceCSPSelectiveStage.initial a q input)
    ts u (by rw [hselect]) (by rw [hrun])
  rw [hselect, hrun] at heq
  have hd : d = (SourceCSPSelectiveStage.globalInitialControl a q,
      SourceCSPSelectiveStage.stageInitialControl) :=
    congrArg (fun cfg => cfg.var) heq
  have hU : U = T := congrArg (fun cfg => cfg.stk) heq
  subst U
  exact ⟨hd, hleft, hsource, hvertex, hblank⟩

/-- On every raw input the selective machine preserves the complete global
bank, and leaves all writer cells other than the two staging destinations
blank. The reject/zero cases have those two cells blank as well in the
three-way theorem imported from `TotalSelective`. -/
theorem raw_total_selective_full_frame (a q : Nat) (input : List Bool) :
    ∃ tg ≤ SourceCSPGlobalTotalValidation.totalBound a q input.length + 1,
      ∃ (c : SourceCSPGlobalDecisionProgram.Control a q)
        (S : SourceCSPGlobalDecisionProgram.Stack q → List Bool),
        ((advance (SourceCSPGlobalDecisionProgram.program a q))^[tg])
          (SourceCSPGlobalDecisionProgram.initial a q input) =
            ⟨none, c, S⟩ ∧
        ∃ ts ≤ SourceCSPTotalSelectiveScratch.totalSelectiveBound
            a q input.length,
          ∃ (d : SourceCSPSelectiveStage.Control a q)
            (U : SourceCSPSelectiveStage.Stack q → List Bool),
            ((advance (SourceCSPSelectiveStage.program a q))^[ts])
              (SourceCSPSelectiveStage.initial a q input) =
                ⟨none, d, U⟩ ∧
            (∀ k : SourceCSPGlobalDecisionProgram.Stack q,
              U (.inl k) = S k) ∧
            (∀ k : SourceClauseRowWriterOperands.Stack q,
              (.inr k : SourceCSPSelectiveStage.Stack q) ≠
                SourceCSPSecondPassInput.writerSource →
              (.inr k : SourceCSPSelectiveStage.Stack q) ≠
                SourceCSPSecondPassInput.writerVertex →
              U (.inr k) = []) := by
  obtain ⟨tg, htg, c, S, hglobal, ts, hts, d, U, hselect,
    hcase⟩ := SourceCSPTotalSelectiveScratch.raw_total_selective a q input
  rcases hcase with hreje | hzero | hacc
  · obtain ⟨_, _, _, _, hleft, hblank⟩ := hreje
    refine ⟨tg, htg, c, S, hglobal, ts, hts, d, U,
      hselect, hleft, ?_⟩
    intro k _ _
    exact hblank k
  · obtain ⟨_, _, _, hleft, hblank⟩ := hzero
    refine ⟨tg, htg, c, S, hglobal, ts, hts, d, U,
      hselect, hleft, ?_⟩
    intro k _ _
    exact hblank k
  · obtain ⟨n, m, rest, rows, vr, hc, _, _, _, _, _, _,
      hsaved, hcap, _, _, _, _, _⟩ := hacc
    have hterminal :
        ((advance (SourceCSPGlobalDecisionProgram.program a q))^[tg])
          (SourceCSPGlobalDecisionProgram.initial a q input) =
            ⟨none, .row (vr, some true), S⟩ := by
      rw [hc] at hglobal
      exact hglobal
    obtain ⟨_, hleft, _, _, hblank⟩ :=
      accepted_any_run_full_frame a q input tg ts S vr rest
        (List.replicate (n - 1) true) d U
        hterminal hsaved hcap hselect
    exact ⟨tg, htg, c, S, hglobal, ts, hts, d, U,
      hselect, hleft, hblank⟩




end EthInapproximability.CurrentPaper.SourceCSPTotalSelectiveFrame
