import EthInapproximability.CurrentPaper.SourceCSPSecondPassGlobalLift

/-!
# Verdict-selective staging after the physical CSP validator

The old two-stage sequence always entered the second pass. This instruction
table changes only its administrative handoff: the actual global validator's
finite-control accepted-row verdict enters the existing staging machine;
every other verdict halts without touching the writer bank.
-/

namespace EthInapproximability.CurrentPaper.SourceCSPSelectiveStage

open Turing BitMachineEncoding BitMachineStackEmbedding
open scoped Classical

abbrev Stack (q : Nat) := SourceCSPSecondPassInput.Stack q
abbrev GlobalLabel (a q : Nat) := SourceCSPGlobalDecisionProgram.Label a q
abbrev GlobalControl (a q : Nat) :=
  SourceCSPGlobalDecisionProgram.Control a q
abbrev StageLabel := SourceCSPSecondPassInput.Label
abbrev StageControl := SourceCSPSecondPassInput.Control
abbrev Label (a q : Nat) := BitMachineRawSequence.Label
  (GlobalLabel a q) StageLabel
abbrev Control (a q : Nat) := BitMachineRawSequence.Control
  (GlobalControl a q) StageControl

noncomputable instance (q : Nat) : DecidableEq (Stack q) := Classical.decEq _

def globalInitialControl (a q : Nat) : GlobalControl a q :=
  .prefix SourceCSPGuardOutputCombined.initialControl

def stageInitialLabel : StageLabel := .inl (.inl .scan)
def stageInitialControl : StageControl := ((none, none), ())

def acceptedControl {a q : Nat} : GlobalControl a q → Bool
  | .row (_, some true) => true
  | _ => false

def program (a q : Nat) : Label a q →
    TM2.Stmt (fun _ : Stack q => Bool) (Label a q) (Control a q)
  | .inr (.inl _) =>
      .branch (fun v => acceptedControl v.1)
        (.load (fun _ =>
          (globalInitialControl a q, stageInitialControl))
          (.goto (fun _ => .inr (.inr
            stageInitialLabel))))
        .halt
  | l => BitMachineRawSequence.program
      (SourceCSPSecondPassGlobalLift.globalProgram a q)
      (SourceCSPSecondPassInput.program (q := q))
      stageInitialLabel (globalInitialControl a q) stageInitialControl l

noncomputable def initial (a q : Nat) (input : List Bool) :
    TM2.Cfg (fun _ : Stack q => Bool) (Label a q) (Control a q) :=
  ⟨some (.inl (.prefix (.prefix (.inl
      (SourceCSPGuardDispatchSequence.headerStart a q))))),
    (globalInitialControl a q, stageInitialControl),
    (SourceCSPSecondPassGlobalLift.initial a q input).stk⟩

theorem acceptedControl_true (a q : Nat)
    (vr : SourceCSPRowLoopController.QueryControl ×
      SourceCSPRowLoopController.ResetControl) :
    acceptedControl (a := a) (q := q) (.row (vr, some true)) = true := rfl

theorem handoff_accept (a q : Nat)
    (vr : SourceCSPRowLoopController.QueryControl ×
      SourceCSPRowLoopController.ResetControl)
    (w : StageControl) (S : Stack q → List Bool) :
    advance (program a q)
      (⟨some (.inr (.inl ())), (.row (vr, some true), w), S⟩ :
        TM2.Cfg (fun _ : Stack q => Bool) (Label a q) (Control a q)) =
      ⟨some (.inr (.inr stageInitialLabel)),
        (globalInitialControl a q, stageInitialControl), S⟩ := rfl

theorem handoff_nonaccepted (a q : Nat)
    (c : GlobalControl a q) (w : StageControl)
    (S : Stack q → List Bool)
    (hc : acceptedControl c = false) :
    advance (program a q)
      (⟨some (.inr (.inl ())), (c, w), S⟩ :
        TM2.Cfg (fun _ : Stack q => Bool) (Label a q) (Control a q)) =
      ⟨none, (c, w), S⟩ := by
  simp [advance, TM2.step, TM2.stepAux, program, hc]

/-- Lift any actual complete global-validator run from the raw initial input
to this table's administrative handoff. The right writer bank is still blank. -/
theorem lift_global_terminal (a q : Nat) (input : List Bool)
    (t : Nat) (c : GlobalControl a q)
    (S : SourceCSPGlobalDecisionProgram.Stack q → List Bool)
    (hr : ((advance (SourceCSPGlobalDecisionProgram.program a q))^[t])
      (SourceCSPGlobalDecisionProgram.initial a q input) =
        (⟨none, c, S⟩ :
          TM2.Cfg (fun _ : SourceCSPGlobalDecisionProgram.Stack q => Bool)
            (SourceCSPGlobalDecisionProgram.Label a q)
            (GlobalControl a q))) :
    ∃ (u : Nat) (U : Stack q → List Bool),
      u ≤ t ∧
      ((advance (program a q))^[u]) (initial a q input) =
        (⟨some (.inr (.inl ())),
          (c, stageInitialControl), U⟩ :
          TM2.Cfg (fun _ : Stack q => Bool) (Label a q) (Control a q)) ∧
      (∀ k : SourceCSPGlobalDecisionProgram.Stack q, U (.inl k) = S k) ∧
      (∀ k : SourceClauseRowWriterOperands.Stack q, U (.inr k) = []) := by
  let localStart := SourceCSPGlobalDecisionProgram.initial a q input
  let foreign : Stack q → List Bool :=
    Sum.elim localStart.stk (SourceCSPSecondPassGlobalLift.blankWriter q)
  let localCfg := SourceCSPSecondPassGlobalLift.initial a q input
  have hlocal : ((advance
      (SourceCSPSecondPassGlobalLift.globalProgram a q))^[t]) localCfg =
      ⟨none, c,
        bank SourceCSPSecondPassInput.globalEmbedding foreign S⟩ := by
    rw [show localCfg =
      stackCfg SourceCSPSecondPassInput.globalEmbedding foreign localStart by rfl,
      SourceCSPSecondPassGlobalLift.run, hr]
    rfl
  have hhalt : (((advance
      (SourceCSPSecondPassGlobalLift.globalProgram a q))^[t]) localCfg).l =
      none := by rw [hlocal]
  obtain ⟨u, hu, hrun⟩ := BitMachineInline.outputs
    BitMachineRawSequence.leftLabel
    (fun v => (v, stageInitialControl))
    Prod.fst (fun _ => rfl) (some BitMachineRawSequence.handoff)
    (SourceCSPSecondPassGlobalLift.globalProgram a q) (program a q)
    (fun _ => rfl) localCfg t hhalt
  rw [hlocal] at hrun
  let U := bank SourceCSPSecondPassInput.globalEmbedding foreign S
  have hstart : BitMachineInline.cfg BitMachineRawSequence.leftLabel
      (fun v => (v, stageInitialControl))
      (some BitMachineRawSequence.handoff) localCfg = initial a q input := by
    simp only [BitMachineInline.cfg, initial, localCfg]
    rfl
  rw [hstart] at hrun
  refine ⟨u, U, hu, ?_, ?_, ?_⟩
  · simpa only [U, BitMachineInline.cfg, Option.map_none] using hrun
  · intro k
    exact bank_at SourceCSPSecondPassInput.globalEmbedding foreign S k
  · intro k
    change bank SourceCSPSecondPassInput.globalEmbedding foreign S (.inr k) = []
    rw [bank_outside]
    · rfl
    · rintro ⟨j, hj⟩
      cases hj

end EthInapproximability.CurrentPaper.SourceCSPSelectiveStage

namespace EthInapproximability.CurrentPaper.SourceCSPSelectiveStage

open Turing BitMachineEncoding BitMachineStackEmbedding

/-- Any actual nonaccepted terminal verdict halts at the selective handoff.
All global cells, including the already-written reject/zero output, survive;
the disjoint writer bank remains physically blank. -/
theorem nonaccepted_terminal (a q : Nat) (input : List Bool)
    (t : Nat) (c : GlobalControl a q)
    (S : SourceCSPGlobalDecisionProgram.Stack q → List Bool)
    (hr : ((advance (SourceCSPGlobalDecisionProgram.program a q))^[t])
      (SourceCSPGlobalDecisionProgram.initial a q input) =
        (⟨none, c, S⟩ :
          TM2.Cfg (fun _ : SourceCSPGlobalDecisionProgram.Stack q => Bool)
            (SourceCSPGlobalDecisionProgram.Label a q)
            (GlobalControl a q)))
    (hc : acceptedControl c = false) :
    ∃ (u : Nat) (U : Stack q → List Bool),
      u ≤ t + 1 ∧
      ((advance (program a q))^[u]) (initial a q input) =
        (⟨none, (c, stageInitialControl), U⟩ :
          TM2.Cfg (fun _ : Stack q => Bool) (Label a q) (Control a q)) ∧
      (∀ k : SourceCSPGlobalDecisionProgram.Stack q, U (.inl k) = S k) ∧
      (∀ k : SourceClauseRowWriterOperands.Stack q, U (.inr k) = []) := by
  obtain ⟨ug, U, hug, hglobal, hleft, hright⟩ :=
    lift_global_terminal a q input t c S hr
  refine ⟨ug + 1, U, by omega, ?_, hleft, hright⟩
  rw [show ug + 1 = 1 + ug by omega,
    Function.iterate_add_apply, hglobal]
  simpa only [Function.iterate_one] using
    handoff_nonaccepted a q c stageInitialControl U hc

theorem global_accept_two (a q : Nat)
    (vr : SourceCSPRowLoopController.QueryControl ×
      SourceCSPRowLoopController.ResetControl)
    (S : SourceCSPGlobalDecisionProgram.Stack q → List Bool) :
    ((advance (SourceCSPGlobalDecisionProgram.program a q))^[2])
      (⟨some .afterRow, .row (vr, some true), S⟩ :
        TM2.Cfg (fun _ : SourceCSPGlobalDecisionProgram.Stack q => Bool)
          (SourceCSPGlobalDecisionProgram.Label a q)
          (GlobalControl a q)) =
      ⟨none, .row (vr, some true), S⟩ := by
  rw [show 2 = 1 + 1 by omega, Function.iterate_add_apply]
  simp only [Function.iterate_one,
    SourceCSPGlobalDecisionProgram.after_row_success]
  rfl

/-- The actual global program has validated all rows on raw input. Only
its accepted finite-control verdict enters physical second-pass staging;
the staging machine copies the literal retained suffix and unary vertex cap
into a previously blank writer bank. No query or truth table is provided. -/
theorem accepted_stage_selective (a q n : Nat) (input suffix : List Bool)
    (t : Nat) (S : SourceCSPGlobalDecisionProgram.Stack q → List Bool)
    (vr : SourceCSPRowLoopController.QueryControl ×
      SourceCSPRowLoopController.ResetControl)
    (hrow : ((advance (SourceCSPGlobalDecisionProgram.program a q))^[t])
      (SourceCSPGlobalDecisionProgram.initial a q input) =
      ⟨some .afterRow, .row (vr, some true), S⟩)
    (hsaved : S SourceCSPGlobalDecisionProgram.savedSource = suffix)
    (hcap : S SourceCSPHeaderRowBridge.capSource =
      List.replicate (n - 1) true) :
    ∃ (time : Nat) (U : Stack q → List Bool),
      time ≤ t + 2 +
        ((2 * suffix.length + 2) +
          (2 * (n - 1) + 2) + 3) + 1 ∧
      ((advance (program a q))^[time]) (initial a q input) =
        (⟨none, (globalInitialControl a q, stageInitialControl), U⟩ :
          TM2.Cfg (fun _ : Stack q => Bool)
            (Label a q) (Control a q)) ∧
      U SourceCSPSecondPassInput.savedSource = suffix ∧
      U SourceCSPSecondPassInput.capSource =
        List.replicate (n - 1) true ∧
      U SourceCSPSecondPassInput.writerSource = suffix ∧
      U SourceCSPSecondPassInput.writerVertex =
        true :: List.replicate (n - 1) true ∧
      U SourceCSPSecondPassInput.work = [] := by
  have hterminal : ((advance
      (SourceCSPGlobalDecisionProgram.program a q))^[t + 2])
      (SourceCSPGlobalDecisionProgram.initial a q input) =
      ⟨none, .row (vr, some true), S⟩ := by
    rw [show t + 2 = 2 + t by omega,
      Function.iterate_add_apply, hrow]
    exact global_accept_two a q vr S
  obtain ⟨ug, T, hug, hglobal, hleft, hblank⟩ :=
    lift_global_terminal a q input (t + 2)
      (.row (vr, some true)) S hterminal
  have hsavedT : T SourceCSPSecondPassInput.savedSource = suffix :=
    (hleft SourceCSPGlobalDecisionProgram.savedSource).trans hsaved
  have hcapT : T SourceCSPSecondPassInput.capSource =
      List.replicate (n - 1) true :=
    (hleft SourceCSPHeaderRowBridge.capSource).trans hcap
  obtain ⟨ts, U, hts, hrstage, hsaveU, hcapU, hsourceU,
    hvertexU, hworkU⟩ :=
    SourceCSPSecondPassInput.stage_input q T suffix
      (List.replicate (n - 1) true) hsavedT hcapT
      (hblank _) (hblank _) (hblank _)
  have hhalt : (((advance (SourceCSPSecondPassInput.program (q := q)))^[ts])
      (⟨some stageInitialLabel, stageInitialControl, T⟩ :
        TM2.Cfg (fun _ : Stack q => Bool) StageLabel StageControl)).l =
      none := by
    rw [show stageInitialLabel = (.inl (.inl .scan) : StageLabel) by rfl]
    rw [show stageInitialControl = (((none, none), ()) : StageControl) by rfl]
    rw [hrstage]
  obtain ⟨us, hus, hstage⟩ := BitMachineInline.outputs
    BitMachineRawSequence.rightLabel
    (fun w => (globalInitialControl a q, w)) Prod.snd
    (fun _ => rfl) none
    (SourceCSPSecondPassInput.program (q := q)) (program a q)
    (fun _ => rfl)
    (⟨some stageInitialLabel, stageInitialControl, T⟩ :
      TM2.Cfg (fun _ : Stack q => Bool) StageLabel StageControl)
    ts hhalt
  have hrstage' : ((advance (SourceCSPSecondPassInput.program (q := q)))^[ts])
      (⟨some stageInitialLabel, stageInitialControl, T⟩ :
        TM2.Cfg (fun _ : Stack q => Bool) StageLabel StageControl) =
      ⟨none, stageInitialControl, U⟩ := hrstage
  rw [hrstage'] at hstage
  have hstageRun : ((advance (program a q))^[us])
      (⟨some (.inr (.inr stageInitialLabel)),
        (globalInitialControl a q, stageInitialControl), T⟩ :
          TM2.Cfg (fun _ : Stack q => Bool) (Label a q) (Control a q)) =
      ⟨none, (globalInitialControl a q, stageInitialControl), U⟩ := by
    simpa only [BitMachineInline.cfg, Option.map_none] using hstage
  have hdispatch := handoff_accept a q vr stageInitialControl T
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

end EthInapproximability.CurrentPaper.SourceCSPSelectiveStage

namespace EthInapproximability.CurrentPaper.SourceCSPSelectiveStage

open Turing BitMachineEncoding

def physicalRowBound (a q L : Nat) : Nat :=
  SourceCSPGuardDispatchSequence.bound a q L + 2 +
    SourceCSPGlobalCapFromLiteral.capBound q L L +
    (1 + 2 * L + 4 * (q * L) + 2 * L + 13) +
    (2 * L + 4) +
    SourceCSPRowLoopTotalPolynomial.loopCoefficient q (a ^ q) *
      (L + 1) ^ 3

/-- On an actual raw positive-tag input with a physically passing cap and
exact typed-row suffix, the selective program stages the literal suffix and
unary vertex word in the disjoint second-pass bank. -/
theorem raw_accepted_stage (a q : Nat) (input : List Bool) :
    ∃ (tp : Nat) (v : SourceCSPGuardOutputCombined.PrefixControl)
      (Sp : SourceCSPInputFrame.Stack → List Bool),
      tp ≤ SourceCSPGuardDispatchSequence.bound a q input.length ∧
      ((advance (SourceCSPGuardOutputCombined.program a q))^[tp])
        (SourceCSPGuardOutputCombined.initial a q input) =
          (⟨some .route, (v, none), Sp⟩ :
            TM2.Cfg (fun _ : SourceCSPInputFrame.Stack => Bool)
              (SourceCSPGuardOutputCombined.Label a q)
              SourceCSPGuardOutputCombined.Control) ∧
      (v.2.2 = some .positive →
        ∃ (n m : Nat) (rest : List Bool),
          input = SourceCSPHeaderParse.header n m a q ++ rest ∧
          (0 < n ∧ n ≤ q * m →
            (∃ rows : Fin m → SourceCSPCodec.Row n a q,
              SourceCSPCodec.readFn (SourceCSPCodec.readRow n a q) m rest =
                some (rows, [])) →
            ∃ (time : Nat) (U : Stack q → List Bool),
              time ≤ physicalRowBound a q input.length + 2 +
                ((2 * rest.length + 2) +
                  (2 * (n - 1) + 2) + 3) + 1 ∧
              ((advance (program a q))^[time]) (initial a q input) =
                (⟨none, (globalInitialControl a q, stageInitialControl), U⟩ :
                  TM2.Cfg (fun _ : Stack q => Bool)
                    (Label a q) (Control a q)) ∧
              U SourceCSPSecondPassInput.savedSource = rest ∧
              U SourceCSPSecondPassInput.capSource =
                List.replicate (n - 1) true ∧
              U SourceCSPSecondPassInput.writerSource = rest ∧
              U SourceCSPSecondPassInput.writerVertex =
                true :: List.replicate (n - 1) true ∧
              U SourceCSPSecondPassInput.work = [])) := by
  obtain ⟨tp, v, Sp, htp, hrp, hpositive⟩ :=
    SourceCSPGlobalPositiveRows.raw_positive_rows a q input
  refine ⟨tp, v, Sp, htp, hrp, ?_⟩
  intro hv
  obtain ⟨n, m, rest, hinput, hrows⟩ := hpositive hv
  refine ⟨n, m, rest, hinput, ?_⟩
  intro hn hgood
  obtain ⟨trow, S, vr, b, htrow, hrowrun, hsem, hsaved, hcap⟩ :=
    hrows hn
  have hb : b = true := hsem.mpr hgood
  subst b
  obtain ⟨time, U, htime, hrun, hsaveU, hcapU,
    hsourceU, hvertexU, hworkU⟩ :=
    accepted_stage_selective a q n input rest trow S vr
      hrowrun hsaved hcap
  refine ⟨time, U, ?_, hrun, hsaveU, hcapU,
    hsourceU, hvertexU, hworkU⟩
  dsimp only [physicalRowBound]
  omega

end EthInapproximability.CurrentPaper.SourceCSPSelectiveStage
