import EthInapproximability.CurrentPaper.SourceCSPGlobalTotalValidation
import EthInapproximability.CurrentPaper.SourceCSPSelectiveStage

/-!
Total raw-input selective CSP validation and physical staging.
This module does not emit clauses.
-/

namespace EthInapproximability.CurrentPaper.SourceCSPTotalSelectiveScratch

open Turing BitMachineEncoding

private theorem positive_route_unique (a q : Nat) (input : List Bool)
    (t₁ t₂ : Nat) (v₁ v₂ : SourceCSPGuardOutputCombined.PrefixControl)
    (S₁ S₂ : SourceCSPInputFrame.Stack → List Bool)
    (hr₁ : ((advance (SourceCSPGuardOutputCombined.program a q))^[t₁])
      (SourceCSPGuardOutputCombined.initial a q input) =
        ⟨some .route, (v₁, none), S₁⟩)
    (hv₁ : v₁.2.2 = some .positive)
    (hr₂ : ((advance (SourceCSPGuardOutputCombined.program a q))^[t₂])
      (SourceCSPGuardOutputCombined.initial a q input) =
        ⟨some .route, (v₂, none), S₂⟩) :
    v₂.2.2 = some .positive := by
  let P := SourceCSPGuardOutputCombined.program a q
  let c := SourceCSPGuardOutputCombined.initial a q input
  have hpos : ((advance P)^[t₁ + 2]) c =
      ⟨none, (v₁, none), S₁⟩ := by
    rw [show t₁ + 2 = 2 + t₁ by omega, Function.iterate_add_apply, hr₁]
    exact SourceCSPGuardOutputCombined.route_positive a q v₁ S₁ hv₁
  cases hv₂ : v₂.2.2 with
  | none =>
      have hnone : SourceCSPGuardOutputCombined.routeRun a q 2 v₂ S₂ =
          ⟨none, (v₂, none), S₂⟩ := by
        simp [SourceCSPGuardOutputCombined.routeRun,
          Function.iterate_succ_apply', advance, TM2.step, TM2.stepAux,
          SourceCSPGuardOutputCombined.program, hv₂]
      have hlast : ((advance P)^[t₂ + 2]) c =
          ⟨none, (v₂, none), S₂⟩ := by
        rw [show t₂ + 2 = 2 + t₂ by omega, Function.iterate_add_apply, hr₂]
        exact hnone
      have heq := SourceCSPRowLoopTotalHaltCompare.halted_unique P c
        (t₁ + 2) (t₂ + 2)
        (by rw [hpos]) (by rw [hlast])
      have hv := congrArg (fun x => x.var.1.2.2) heq
      rw [hpos, hlast] at hv
      simp only at hv
      exact False.elim (by rw [hv₁, hv₂] at hv; cases hv)
  | some tag =>
      cases tag with
      | positive => rfl
      | reject =>
          obtain ⟨tr, T, _, hroute, _, _⟩ :=
            SourceCSPGuardOutputCombined.route_reject a q v₂ S₂ hv₂
          have hlast : ((advance P)^[t₂ + tr]) c =
              ⟨none, (SourceCSPGuardOutputCombined.rejectControl, none), T⟩ := by
            rw [show t₂ + tr = tr + t₂ by omega,
              Function.iterate_add_apply, hr₂]
            exact hroute
          have heq := SourceCSPRowLoopTotalHaltCompare.halted_unique P c
            (t₁ + 2) (t₂ + tr)
            (by rw [hpos]) (by rw [hlast])
          have hv := congrArg (fun x => x.var.1.2.2) heq
          rw [hpos, hlast] at hv
          simp [SourceCSPGuardOutputCombined.rejectControl, hv₁] at hv
      | zero =>
          obtain ⟨tr, T, _, hroute, _, _⟩ :=
            SourceCSPGuardOutputCombined.route_zero a q v₂ S₂ hv₂
          have hlast : ((advance P)^[t₂ + tr]) c =
              ⟨none, (SourceCSPGuardOutputCombined.zeroControl, none), T⟩ := by
            rw [show t₂ + tr = tr + t₂ by omega,
              Function.iterate_add_apply, hr₂]
            exact hroute
          have heq := SourceCSPRowLoopTotalHaltCompare.halted_unique P c
            (t₁ + 2) (t₂ + tr)
            (by rw [hpos]) (by rw [hlast])
          have hv := congrArg (fun x => x.var.1.2.2) heq
          rw [hpos, hlast] at hv
          simp [SourceCSPGuardOutputCombined.zeroControl, hv₁] at hv

/- The public total-validator theorem intentionally omits the finite-control
tag on its rejecting arm and the retained-bank contents on its accepting arm.
This refinement recovers them from the same physical branch lemmas, without
any clock estimate; the bounded public halt theorem supplies the clock below. -/
private theorem raw_refined_exists (a q : Nat) (input : List Bool) :
    ∃ (t : Nat) (c : SourceCSPGlobalDecisionProgram.Control a q)
      (S : SourceCSPGlobalDecisionProgram.Stack q → List Bool),
      ((advance (SourceCSPGlobalDecisionProgram.program a q))^[t])
        (SourceCSPGlobalDecisionProgram.initial a q input) =
          ⟨none, c, S⟩ ∧
      ((SourceCSPSelectiveStage.acceptedControl c = false ∧
          S SourceCSPGlobalDecisionProgram.outputSlot =
            SourceCSPRejectFormula.bits ∧
          S SourceCSPGlobalDecisionProgram.outputSlot ∉
            EncodedCNF.Language) ∨
       (c = .prefix (SourceCSPGuardOutputCombined.zeroControl, none) ∧
          S SourceCSPGlobalDecisionProgram.outputSlot = [false, false]) ∨
       (∃ (n m : Nat) (rest : List Bool)
          (rows : Fin m → SourceCSPCodec.Row n a q)
          (vr : SourceCSPRowLoopController.QueryControl ×
            SourceCSPRowLoopController.ResetControl),
          c = .row (vr, some true) ∧
          input = SourceCSPHeaderParse.header n m a q ++ rest ∧
          0 < n ∧ n ≤ q * m ∧ m ≤ input.length ∧
          SourceCSPCodec.readFn (SourceCSPCodec.readRow n a q) m rest =
            some (rows, []) ∧
          S SourceCSPGlobalDecisionProgram.savedSource = rest ∧
          S SourceCSPHeaderRowBridge.capSource =
            List.replicate (n - 1) true)) := by
  obtain ⟨tp, v, Sp, S₀, wa, wq, word, htp, hrp,
    htag, _, hreje, hzero⟩ :=
    SourceCSPGlobalDecisionProgram.raw_guarded_terminal a q input
  let tag := SourceCSPGuardDispatch.classify
    ((SourceCSPHeaderValidFlag.parserGood input &&
      decide (wq = q.bits) && decide (wa = a.bits)) &&
      decide (EncodedCommunication.bitsValue word ≤ input.length))
    (S₀ SourceCSPGuardDispatch.vertexSlot)
    (S₀ SourceCSPGuardDispatch.countSlot)
    (S₀ SourceCSPGuardDispatch.sourceSlot)
  have hv : v.2.2 = some tag := htag
  cases hcase : tag with
  | reject =>
      have hvreje : v.2.2 = some .reject := by simpa only [hcase] using hv
      obtain ⟨t, S, _, hrun, hout, hnlang⟩ := hreje hvreje
      refine ⟨t, .prefix
        (SourceCSPGuardOutputCombined.rejectControl, none),
        S, hrun, Or.inl ?_⟩
      exact ⟨rfl, hout, hnlang⟩
  | zero =>
      have hvzero : v.2.2 = some .zero := by simpa only [hcase] using hv
      obtain ⟨t, S, _, hrun, hout⟩ := hzero hvzero
      refine ⟨t, .prefix
        (SourceCSPGuardOutputCombined.zeroControl, none),
        S, hrun, Or.inr (Or.inl ?_)⟩
      exact ⟨rfl, hout⟩
  | positive =>
      have hvpos : v.2.2 = some .positive := by simpa only [hcase] using hv
      obtain ⟨tp₂, v₂, Sp₂, _, hrp₂, hpositive⟩ :=
        SourceCSPGlobalPositiveLiteral.positive_literal a q input
      have hv₂ := positive_route_unique a q input tp tp₂ v v₂
        Sp Sp₂ hrp hvpos hrp₂
      obtain ⟨n, m, tg, rest, Sg, _, hglobal, hinput,
        hnword, _, hrest, hm, hmL, hempty, hrowblank⟩ :=
        hpositive hv₂
      by_cases hcap : 0 < n ∧ n ≤ q * m
      · have hsuffixL :=
          (SourceCSPGlobalPositiveLiteral.canonical_header_word_bounds
            a q n m input rest hinput).2.2
        obtain ⟨tr, Sr, vr, b, _, hrr, hsem, hsaved, hcapbank⟩ :=
          SourceCSPGlobalPositiveRows.positive_rows_from_literal
            n m a q input.length rest (v₂, none) Sg
            hcap.1 hcap.2 hmL hsuffixL hv₂ hnword hm hrest
            hempty hrowblank
        have hrowrun :
            ((advance (SourceCSPGlobalDecisionProgram.program a q))^[tg + tr])
              (SourceCSPGlobalDecisionProgram.initial a q input) =
            ⟨some .afterRow, .row (vr, some b), Sr⟩ := by
          rw [show tg + tr = tr + tg by omega,
            Function.iterate_add_apply, hglobal]
          exact hrr
        cases b with
        | true =>
            obtain ⟨rows, hrows⟩ := hsem.mp rfl
            have hacc :
                ((advance (SourceCSPGlobalDecisionProgram.program a q))^[tg + tr + 1])
                  (SourceCSPGlobalDecisionProgram.initial a q input) =
                ⟨some .accept, .row (vr, some true), Sr⟩ := by
              rw [show tg + tr + 1 = 1 + (tg + tr) by omega,
                Function.iterate_add_apply, hrowrun]
              exact SourceCSPGlobalDecisionProgram.after_row_success a q vr Sr
            have hfinal :
                ((advance (SourceCSPGlobalDecisionProgram.program a q))^[tg + tr + 2])
                  (SourceCSPGlobalDecisionProgram.initial a q input) =
                ⟨none, .row (vr, some true), Sr⟩ := by
              rw [show tg + tr + 2 = 1 + (tg + tr + 1) by omega,
                Function.iterate_add_apply, hacc]
              exact SourceCSPGlobalTotalValidation.accept_one_step_halt a q vr Sr
            refine ⟨tg + tr + 2, .row (vr, some true), Sr,
              hfinal, Or.inr (Or.inr ?_)⟩
            exact ⟨n, m, rest, rows, vr, rfl, hinput,
              hcap.1, hcap.2, hmL, hrows, hsaved, hcapbank⟩
        | false =>
            obtain ⟨tw, T, _, hwriter, hout, _⟩ :=
              SourceCSPGlobalDecisionProgram.row_failure_reject a q vr Sr
            have hfinal :
                ((advance (SourceCSPGlobalDecisionProgram.program a q))^[tg + tr + tw])
                  (SourceCSPGlobalDecisionProgram.initial a q input) =
                ⟨none, .writer none, T⟩ := by
              rw [show tg + tr + tw = tw + (tg + tr) by omega,
                Function.iterate_add_apply, hrowrun]
              exact hwriter
            refine ⟨tg + tr + tw, .writer none, T,
              hfinal, Or.inl ?_⟩
            exact ⟨rfl, hout, by
              rw [hout]
              exact SourceCSPRejectFormula.bits_not_language⟩
      · obtain ⟨tc, Sc, cc, _, hcaprun, hbit⟩ :=
          SourceCSPGlobalCapFromLiteral.cap_from_literal a q n m
            (v₂, none) Sg hv₂ hnword hm hempty
        have hcapglobal :
            ((advance (SourceCSPGlobalDecisionProgram.program a q))^[tg + tc])
              (SourceCSPGlobalDecisionProgram.initial a q input) =
            ⟨some .capCheck, .cap cc, Sc⟩ := by
          rw [show tg + tc = tc + tg by omega,
            Function.iterate_add_apply, hglobal]
          exact hcaprun
        have hbad : (Sc SourceCSPHeaderRowBridge.capSource).head? ≠
            some true := by rw [hbit]; simp [hcap]
        obtain ⟨tw, T, _, hwriter, hout, _⟩ :=
          SourceCSPGlobalDecisionProgram.cap_failure_reject a q cc Sc hbad
        have hfinal :
            ((advance (SourceCSPGlobalDecisionProgram.program a q))^[tg + tc + tw])
              (SourceCSPGlobalDecisionProgram.initial a q input) =
            ⟨none, .writer none, T⟩ := by
          rw [show tg + tc + tw = tw + (tg + tc) by omega,
            Function.iterate_add_apply, hcapglobal]
          exact hwriter
        refine ⟨tg + tc + tw, .writer none, T,
          hfinal, Or.inl ?_⟩
        exact ⟨rfl, hout, by
          rw [hout]
          exact SourceCSPRejectFormula.bits_not_language⟩

/-- A uniform clock measured only in the original raw input length. -/
noncomputable def totalSelectiveBound (a q L : Nat) : Nat :=
  SourceCSPGlobalTotalValidation.totalBound a q L + 2 +
    ((2 * L + 2) + (2 * (q * L) + 2) + 3)

/-- The refined physical terminal state is available at the validator's
original-input-size clock. -/
private theorem raw_refined_bounded (a q : Nat) (input : List Bool) :
    ∃ t ≤ SourceCSPGlobalTotalValidation.totalBound a q input.length + 1,
      ∃ (c : SourceCSPGlobalDecisionProgram.Control a q)
        (S : SourceCSPGlobalDecisionProgram.Stack q → List Bool),
        ((advance (SourceCSPGlobalDecisionProgram.program a q))^[t])
          (SourceCSPGlobalDecisionProgram.initial a q input) =
            ⟨none, c, S⟩ ∧
        ((SourceCSPSelectiveStage.acceptedControl c = false ∧
            S SourceCSPGlobalDecisionProgram.outputSlot =
              SourceCSPRejectFormula.bits ∧
            S SourceCSPGlobalDecisionProgram.outputSlot ∉
              EncodedCNF.Language) ∨
         (c = .prefix (SourceCSPGuardOutputCombined.zeroControl, none) ∧
            S SourceCSPGlobalDecisionProgram.outputSlot = [false, false]) ∨
         (∃ (n m : Nat) (rest : List Bool)
            (rows : Fin m → SourceCSPCodec.Row n a q)
            (vr : SourceCSPRowLoopController.QueryControl ×
              SourceCSPRowLoopController.ResetControl),
            c = .row (vr, some true) ∧
            input = SourceCSPHeaderParse.header n m a q ++ rest ∧
            0 < n ∧ n ≤ q * m ∧ m ≤ input.length ∧
            SourceCSPCodec.readFn (SourceCSPCodec.readRow n a q) m rest =
              some (rows, []) ∧
            S SourceCSPGlobalDecisionProgram.savedSource = rest ∧
            S SourceCSPHeaderRowBridge.capSource =
              List.replicate (n - 1) true)) := by
  obtain ⟨tr, cr, Sr, hr, hcase⟩ :=
    raw_refined_exists a q input
  obtain ⟨tb, htb, cb, Sb, hb⟩ :=
    SourceCSPGlobalTotalValidation.raw_total_halts a q input
  have heq := SourceCSPRowLoopTotalHaltCompare.halted_unique
    (SourceCSPGlobalDecisionProgram.program a q)
    (SourceCSPGlobalDecisionProgram.initial a q input)
    (tb + 1) tr (by rw [hb]) (by rw [hr])
  refine ⟨tb + 1, by omega, cr, Sr, ?_, hcase⟩
  rw [hb, hr] at heq
  rw [hb]
  exact heq

private theorem accepted_terminal_stage (a q n : Nat)
    (input rest : List Bool) (t : Nat)
    (S : SourceCSPGlobalDecisionProgram.Stack q → List Bool)
    (vr : SourceCSPRowLoopController.QueryControl ×
      SourceCSPRowLoopController.ResetControl)
    (hrun : ((advance (SourceCSPGlobalDecisionProgram.program a q))^[t])
      (SourceCSPGlobalDecisionProgram.initial a q input) =
        ⟨none, .row (vr, some true), S⟩)
    (hsaved : S SourceCSPGlobalDecisionProgram.savedSource = rest)
    (hcap : S SourceCSPHeaderRowBridge.capSource =
      List.replicate (n - 1) true) :
    ∃ (time : Nat) (U : SourceCSPSelectiveStage.Stack q → List Bool),
      time ≤ t + 1 +
        ((2 * rest.length + 2) +
          (2 * (n - 1) + 2) + 3) ∧
      ((advance (SourceCSPSelectiveStage.program a q))^[time])
        (SourceCSPSelectiveStage.initial a q input) =
          ⟨none, (SourceCSPSelectiveStage.globalInitialControl a q,
            SourceCSPSelectiveStage.stageInitialControl), U⟩ ∧
      U SourceCSPSecondPassInput.savedSource = rest ∧
      U SourceCSPSecondPassInput.capSource =
        List.replicate (n - 1) true ∧
      U SourceCSPSecondPassInput.writerSource = rest ∧
      U SourceCSPSecondPassInput.writerVertex =
        true :: List.replicate (n - 1) true ∧
      U SourceCSPSecondPassInput.work = [] := by
  obtain ⟨ug, T, hug, hglobal, hleft, hblank⟩ :=
    SourceCSPSelectiveStage.lift_global_terminal a q input t
      (.row (vr, some true)) S hrun
  have hsavedT : T SourceCSPSecondPassInput.savedSource = rest :=
    (hleft SourceCSPGlobalDecisionProgram.savedSource).trans hsaved
  have hcapT : T SourceCSPSecondPassInput.capSource =
      List.replicate (n - 1) true :=
    (hleft SourceCSPHeaderRowBridge.capSource).trans hcap
  obtain ⟨ts, U, hts, hrstage, hsaveU, hcapU, hsourceU,
    hvertexU, hworkU⟩ :=
    SourceCSPSecondPassInput.stage_input q T rest
      (List.replicate (n - 1) true) hsavedT hcapT
      (hblank _) (hblank _) (hblank _)
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
  refine ⟨ug + 1 + us, U, ?_, ?_, hsaveU, hcapU,
    hsourceU, hvertexU, hworkU⟩
  · simp only [List.length_replicate] at hts
    omega
  · rw [show ug + 1 + us = us + (1 + ug) by omega,
      Function.iterate_add_apply,
      Function.iterate_add_apply, hglobal]
    simp only [Function.iterate_one]
    rw [hdispatch]
    exact hstageRun

/-- The one finite selective controller terminates on every raw bitstring:
it preserves a completed reject/zero result or physically stages a validated
positive row suffix. No clause emission is claimed. -/
theorem raw_total_selective (a q : Nat) (input : List Bool) :
    ∃ tg ≤ SourceCSPGlobalTotalValidation.totalBound a q input.length + 1,
      ∃ (c : SourceCSPGlobalDecisionProgram.Control a q)
        (S : SourceCSPGlobalDecisionProgram.Stack q → List Bool),
        ((advance (SourceCSPGlobalDecisionProgram.program a q))^[tg])
          (SourceCSPGlobalDecisionProgram.initial a q input) =
            ⟨none, c, S⟩ ∧
        ∃ ts ≤ totalSelectiveBound a q input.length,
          ∃ (d : SourceCSPSelectiveStage.Control a q)
            (U : SourceCSPSelectiveStage.Stack q → List Bool),
            ((advance (SourceCSPSelectiveStage.program a q))^[ts])
              (SourceCSPSelectiveStage.initial a q input) =
                ⟨none, d, U⟩ ∧
            ((SourceCSPSelectiveStage.acceptedControl c = false ∧
                d = (c, SourceCSPSelectiveStage.stageInitialControl) ∧
                S SourceCSPGlobalDecisionProgram.outputSlot =
                  SourceCSPRejectFormula.bits ∧
                S SourceCSPGlobalDecisionProgram.outputSlot ∉
                  EncodedCNF.Language ∧
                (∀ k : SourceCSPGlobalDecisionProgram.Stack q,
                  U (.inl k) = S k) ∧
                (∀ k : SourceClauseRowWriterOperands.Stack q,
                  U (.inr k) = [])) ∨
             (c = .prefix
                (SourceCSPGuardOutputCombined.zeroControl, none) ∧
                d = (c, SourceCSPSelectiveStage.stageInitialControl) ∧
                S SourceCSPGlobalDecisionProgram.outputSlot =
                  [false, false] ∧
                (∀ k : SourceCSPGlobalDecisionProgram.Stack q,
                  U (.inl k) = S k) ∧
                (∀ k : SourceClauseRowWriterOperands.Stack q,
                  U (.inr k) = [])) ∨
             (∃ (n m : Nat) (rest : List Bool)
                (rows : Fin m → SourceCSPCodec.Row n a q)
                (vr : SourceCSPRowLoopController.QueryControl ×
                  SourceCSPRowLoopController.ResetControl),
                c = .row (vr, some true) ∧
                d = (SourceCSPSelectiveStage.globalInitialControl a q,
                  SourceCSPSelectiveStage.stageInitialControl) ∧
                input = SourceCSPHeaderParse.header n m a q ++ rest ∧
                0 < n ∧ n ≤ q * m ∧ m ≤ input.length ∧
                SourceCSPCodec.readFn (SourceCSPCodec.readRow n a q) m rest =
                  some (rows, []) ∧
                S SourceCSPGlobalDecisionProgram.savedSource = rest ∧
                S SourceCSPHeaderRowBridge.capSource =
                  List.replicate (n - 1) true ∧
                U SourceCSPSecondPassInput.savedSource = rest ∧
                U SourceCSPSecondPassInput.capSource =
                  List.replicate (n - 1) true ∧
                U SourceCSPSecondPassInput.writerSource = rest ∧
                U SourceCSPSecondPassInput.writerVertex =
                  true :: List.replicate (n - 1) true ∧
                U SourceCSPSecondPassInput.work = [])) := by
  obtain ⟨tg, htg, c, S, hglobal, hcase⟩ :=
    raw_refined_bounded a q input
  rcases hcase with hreje | hzero | hacc
  · obtain ⟨hc, hout, hnlang⟩ := hreje
    obtain ⟨ts, U, hts, hrun, hleft, hblank⟩ :=
      SourceCSPSelectiveStage.nonaccepted_terminal a q input tg c S
        hglobal hc
    refine ⟨tg, htg, c, S, hglobal, ts, ?_,
      (c, SourceCSPSelectiveStage.stageInitialControl), U,
      hrun, Or.inl ?_⟩
    · unfold totalSelectiveBound
      omega
    · exact ⟨hc, rfl, hout, hnlang, hleft, hblank⟩
  · obtain ⟨hc, hout⟩ := hzero
    have hnot : SourceCSPSelectiveStage.acceptedControl c = false := by
      rw [hc]
      rfl
    obtain ⟨ts, U, hts, hrun, hleft, hblank⟩ :=
      SourceCSPSelectiveStage.nonaccepted_terminal a q input tg c S
        hglobal hnot
    refine ⟨tg, htg, c, S, hglobal, ts, ?_,
      (c, SourceCSPSelectiveStage.stageInitialControl), U,
      hrun, Or.inr (Or.inl ?_)⟩
    · unfold totalSelectiveBound
      omega
    · exact ⟨hc, rfl, hout, hleft, hblank⟩
  · obtain ⟨n, m, rest, rows, vr, hc, hinput,
      hn, hsize, hmL, hrows, hsaved, hcap⟩ := hacc
    have hterminal :
        ((advance (SourceCSPGlobalDecisionProgram.program a q))^[tg])
          (SourceCSPGlobalDecisionProgram.initial a q input) =
            ⟨none, .row (vr, some true), S⟩ := by
      rw [hc] at hglobal
      exact hglobal
    obtain ⟨ts, U, hts, hrun, hsaveU, hcapU,
      hsourceU, hvertexU, hworkU⟩ :=
      accepted_terminal_stage a q n input rest tg S vr
        hterminal hsaved hcap
    have hrestL : rest.length ≤ input.length :=
      (SourceCSPGlobalPositiveLiteral.canonical_header_word_bounds
        a q n m input rest hinput).2.2
    have hcapL : n - 1 ≤ q * input.length := by
      have hqm : q * m ≤ q * input.length :=
        Nat.mul_le_mul_left q hmL
      omega
    refine ⟨tg, htg, c, S, hglobal, ts, ?_,
      (SourceCSPSelectiveStage.globalInitialControl a q,
        SourceCSPSelectiveStage.stageInitialControl), U,
      hrun, Or.inr (Or.inr ?_)⟩
    · unfold totalSelectiveBound
      omega
    · exact ⟨n, m, rest, rows, vr, hc, rfl, hinput,
        hn, hsize, hmL, hrows, hsaved, hcap,
        hsaveU, hcapU, hsourceU, hvertexU, hworkU⟩



end EthInapproximability.CurrentPaper.SourceCSPTotalSelectiveScratch
