import EthInapproximability.CurrentPaper.SourceCSPStagedFirstRow
import EthInapproximability.CurrentPaper.SourceCSPValidatorPolynomial

/-! One raw-input controller with a verdict branch before staging. -/

namespace EthInapproximability.CurrentPaper.SourceCSPFirstRowController

open Turing BitMachineEncoding BitMachineInline BitMachineStackEmbedding

abbrev Stack (q : Nat) := SourceCSPSecondPassInput.Stack q
abbrev GlobalLabel (a q : Nat) := SourceCSPGlobalDecisionProgram.Label a q
abbrev GlobalControl (a q : Nat) := SourceCSPGlobalDecisionProgram.Control a q
abbrev BodyLabel (q a : Nat) :=
  BitMachineRawSequence.Label SourceCSPSecondPassInput.Label
    (SourceCSPStagedFirstRow.FirstLabel q a)
abbrev BodyControl := SourceCSPSecondPassInput.Control ×
  SourceCSPStagedFirstRow.FirstControl
abbrev Label (a q : Nat) :=
  BitMachineRawSequence.Label (GlobalLabel a q) (BodyLabel q a)
abbrev Control (a q : Nat) := GlobalControl a q × BodyControl

abbrev stageStart : SourceCSPSecondPassInput.Label := .inl (.inl .scan)
abbrev rowStart : SourceCSPStagedFirstRow.FirstLabel q a :=
  .inl (.inl .scan)
abbrev stageInitial : SourceCSPSecondPassInput.Control := ((none, none), ())
abbrev rowInitial : SourceCSPStagedFirstRow.FirstControl :=
  ((none, none), SourceCSPStagedFirstRow.readInitialControl)
abbrev bodyInitial : BodyControl := (stageInitial, rowInitial)
abbrev bodyStart : BodyLabel q a := .inl stageStart

def bodyProgram (q a : Nat) : BodyLabel q a →
    TM2.Stmt (fun _ : Stack q => Bool) (BodyLabel q a) BodyControl :=
  BitMachineRawSequence.program (SourceCSPSecondPassInput.program (q := q))
    (SourceCSPStagedFirstRow.firstRowProgram q a)
    (rowStart (q := q) (a := a)) stageInitial rowInitial

/-- The global verdict is tested while its original control is still live.
Reject and zero halt in place. Only acceptance enters stage-then-row. -/
def program (a q : Nat) : Label a q →
    TM2.Stmt (fun _ : Stack q => Bool) (Label a q) (Control a q)
  | .inl l => BitMachineInline.stmt BitMachineRawSequence.leftLabel
      (fun v => (v, bodyInitial)) Prod.fst
      (some BitMachineRawSequence.handoff)
      (SourceCSPSecondPassGlobalLift.globalProgram a q l)
  | .inr (.inl _) =>
      .branch (fun v => SourceCSPSelectiveStage.acceptedControl v.1)
        (.load (fun _ =>
          (SourceCSPSelectiveStage.globalInitialControl a q, bodyInitial))
          (.goto (fun _ => BitMachineRawSequence.rightLabel
            (bodyStart (q := q) (a := a)))))
        .halt
  | .inr (.inr l) => BitMachineInline.stmt BitMachineRawSequence.rightLabel
      (fun v => (SourceCSPSelectiveStage.globalInitialControl a q, v))
      Prod.snd none (bodyProgram q a l)

noncomputable def initial (a q : Nat) (input : List Bool) :
    TM2.Cfg (fun _ : Stack q => Bool) (Label a q) (Control a q) :=
  BitMachineInline.cfg BitMachineRawSequence.leftLabel
    (fun v => (v, bodyInitial))
    (some BitMachineRawSequence.handoff)
    (SourceCSPSecondPassGlobalLift.initial a q input)

/-- Every actual global halt reaches the new verdict instruction with
unchanged global cells and a blank writer bank. -/
theorem global_handoff (a q : Nat) (input : List Bool)
    (tg : Nat) (c : GlobalControl a q)
    (S : SourceCSPGlobalDecisionProgram.Stack q → List Bool)
    (hglobal : ((advance (SourceCSPGlobalDecisionProgram.program a q))^[tg])
      (SourceCSPGlobalDecisionProgram.initial a q input) =
        ⟨none, c, S⟩) :
    ∃ (u : Nat) (U : Stack q → List Bool),
      u ≤ tg ∧
      ((advance (program a q))^[u]) (initial a q input) =
        ⟨some BitMachineRawSequence.handoff, (c, bodyInitial), U⟩ ∧
      (∀ k : SourceCSPGlobalDecisionProgram.Stack q, U (.inl k) = S k) ∧
      (∀ k : SourceClauseRowWriterOperands.Stack q, U (.inr k) = []) := by
  let localStart := SourceCSPGlobalDecisionProgram.initial a q input
  let foreign : Stack q → List Bool :=
    Sum.elim localStart.stk (SourceCSPSecondPassGlobalLift.blankWriter q)
  let localCfg := SourceCSPSecondPassGlobalLift.initial a q input
  have hlocal : ((advance
      (SourceCSPSecondPassGlobalLift.globalProgram a q))^[tg]) localCfg =
      ⟨none, c,
        bank SourceCSPSecondPassInput.globalEmbedding foreign S⟩ := by
    rw [show localCfg =
      stackCfg SourceCSPSecondPassInput.globalEmbedding foreign localStart by rfl,
      SourceCSPSecondPassGlobalLift.run, hglobal]
    rfl
  have hhalt : (((advance
      (SourceCSPSecondPassGlobalLift.globalProgram a q))^[tg]) localCfg).l =
      none := by rw [hlocal]
  obtain ⟨u, hu, hrun⟩ := BitMachineInline.outputs
    BitMachineRawSequence.leftLabel
    (fun v => (v, bodyInitial)) Prod.fst (fun _ => rfl)
    (some BitMachineRawSequence.handoff)
    (SourceCSPSecondPassGlobalLift.globalProgram a q)
    (program a q) (fun _ => rfl) localCfg tg hhalt
  rw [hlocal] at hrun
  let U := bank SourceCSPSecondPassInput.globalEmbedding foreign S
  refine ⟨u, U, hu, ?_, ?_, ?_⟩
  · simpa only [initial, BitMachineInline.cfg, Option.map_none, U]
      using hrun
  · intro k
    exact bank_at SourceCSPSecondPassInput.globalEmbedding foreign S k
  · intro k
    change bank SourceCSPSecondPassInput.globalEmbedding foreign S (.inr k) = []
    rw [bank_outside]
    · rfl
    · rintro ⟨j, hj⟩
      cases hj

theorem handoff_nonaccepted (a q : Nat)
    (c : GlobalControl a q) (U : Stack q → List Bool)
    (hc : SourceCSPSelectiveStage.acceptedControl c = false) :
    advance (program a q)
      (⟨some BitMachineRawSequence.handoff, (c, bodyInitial), U⟩ :
        TM2.Cfg (fun _ : Stack q => Bool) (Label a q) (Control a q)) =
      ⟨none, (c, bodyInitial), U⟩ := by
  simp [advance, TM2.step, TM2.stepAux, program,
    BitMachineRawSequence.handoff, hc]

theorem handoff_accepted (a q : Nat)
    (vr : SourceCSPRowLoopController.QueryControl ×
      SourceCSPRowLoopController.ResetControl)
    (U : Stack q → List Bool) :
    advance (program a q)
      (⟨some BitMachineRawSequence.handoff,
        ((.row (vr, some true) : GlobalControl a q), bodyInitial), U⟩ :
        TM2.Cfg (fun _ : Stack q => Bool) (Label a q) (Control a q)) =
      ⟨some (BitMachineRawSequence.rightLabel
        (bodyStart (q := q) (a := a))),
        (SourceCSPSelectiveStage.globalInitialControl a q, bodyInitial), U⟩ := by
  rfl

def stageBound (suffix : List Bool) (n : Nat) : Nat :=
  (2 * suffix.length + 2) + (2 * (n - 1) + 2) + 3

def rowBound (a q n : Nat) (suffix : List Bool) : Nat :=
  2 * n + 5 + q * (2 * suffix.length + 4) +
    2 * a ^ q + 3 + q * (100 * (n + 1) ^ 2) + 2

/-- On an accepted, validated global bank, the body is one literal program:
physical suffix/vertex staging followed by the first typed-row machine. -/
theorem body_accepted_run {a q n m : Nat}
    (suffix : List Bool) (rows : Fin m → SourceCSPCodec.Row n a q)
    (hm : 0 < m) (hn : 0 < n) (B : Stack q → List Bool)
    (hsaved : B SourceCSPSecondPassInput.savedSource = suffix)
    (hcap : B SourceCSPSecondPassInput.capSource =
      List.replicate (n - 1) true)
    (hblank : ∀ k : SourceClauseRowWriterOperands.Stack q,
      B (.inr k) = [])
    (hread : SourceCSPCodec.readFn (SourceCSPCodec.readRow n a q) m suffix =
      some (rows, [])) :
    ∃ (t : Nat) (T : SourceCSPStagedFirstRow.ReadControl ×
      (Stack q → List Bool)) (rest : List Bool),
      t ≤ stageBound suffix n + rowBound a q n suffix + 1 ∧
      ((advance (bodyProgram q a))^[t])
        (⟨some (bodyStart (q := q) (a := a)), bodyInitial, B⟩ :
          TM2.Cfg (fun _ : Stack q => Bool) (BodyLabel q a) BodyControl) =
        ⟨none, (stageInitial, ((none, none), T.1)), T.2⟩ ∧
      suffix = SourceCSPCodec.rowFields (rows ⟨0, hm⟩) ++ rest ∧
      T.2 (SourceCSPStagedFirstRow.rowSlot (.inr 4)) = [true] ∧
      (∀ j : Fin q,
        T.2 (SourceCSPStagedFirstRow.rowSlot (.inl (j, 1))) =
          List.replicate ((rows ⟨0, hm⟩).1 j).val true) ∧
      T.2 (SourceCSPStagedFirstRow.rowSlot (.inr 0)) = rest ∧
      T.2 (SourceCSPStagedFirstRow.rowSlot (.inr 2)) =
        true :: List.ofFn (rows ⟨0, hm⟩).2 ∧
      (∀ g : SourceCSPGlobalDecisionProgram.Stack q,
        T.2 (.inl g) = B (.inl g)) := by
  obtain ⟨ts, S1, hts, hstage, hglobal,
    hsource, hvertex, hblank1⟩ :=
    SourceCSPTotalSelectiveFrame.stage_input_full_frame
      q B suffix (List.replicate (n - 1) true)
      hsaved hcap hblank
  have hwriter := SourceCSPStagedFirstRow.staged_writer_eq_blank_bank
    q n suffix S1 hn hsource hvertex hblank1
  obtain ⟨tr, T, rest, htr, hrow, hsuffix, hstatus,
    hunary, hsourceFinal, houtput, hframe⟩ :=
    SourceCSPStagedFirstRow.staged_first_row_run
      suffix rows S1 hn hm hwriter hread
  obtain ⟨t, ht, hrun⟩ := BitMachineRawSequence.runs
    (SourceCSPSecondPassInput.program (q := q))
    (SourceCSPStagedFirstRow.firstRowProgram q a)
    stageStart (rowStart (q := q) (a := a))
    stageInitial stageInitial rowInitial ((none, none), T.1)
    B S1 T.2 ts tr hstage hrow
  refine ⟨t, T, rest, ?_, ?_, hsuffix, hstatus,
    hunary, hsourceFinal, houtput, ?_⟩
  · unfold stageBound rowBound
    simp only [List.length_replicate] at hts
    omega
  · simpa only [bodyProgram] using hrun
  · intro g
    have hnon : ¬ ∃ x : SourceCSPRowQueryFrame.Stack q,
        SourceCSPStagedFirstRow.rowSlot x = (.inl g : Stack q) := by
      rintro ⟨x, hx⟩
      cases hx
    rw [hframe (.inl g) hnon, hglobal]

/-- Accepted global halt enters the staged first-row body in the same physical
controller. The final global bank is the validator's terminal bank. -/
theorem accepted_controller_run {a q n m : Nat} (input suffix : List Bool)
    (rows : Fin m → SourceCSPCodec.Row n a q)
    (tg : Nat)
    (vr : SourceCSPRowLoopController.QueryControl ×
      SourceCSPRowLoopController.ResetControl)
    (S : SourceCSPGlobalDecisionProgram.Stack q → List Bool)
    (hn : 0 < n) (hm : 0 < m)
    (hglobal : ((advance (SourceCSPGlobalDecisionProgram.program a q))^[tg])
      (SourceCSPGlobalDecisionProgram.initial a q input) =
        ⟨none, .row (vr, some true), S⟩)
    (hsaved : S SourceCSPGlobalDecisionProgram.savedSource = suffix)
    (hcap : S SourceCSPHeaderRowBridge.capSource =
      List.replicate (n - 1) true)
    (hread : SourceCSPCodec.readFn (SourceCSPCodec.readRow n a q) m suffix =
      some (rows, [])) :
    ∃ (t : Nat) (T : SourceCSPStagedFirstRow.ReadControl ×
      (Stack q → List Bool)) (rest : List Bool),
      t ≤ tg + 1 + stageBound suffix n + rowBound a q n suffix + 1 ∧
      ((advance (program a q))^[t]) (initial a q input) =
        ⟨none,
          (SourceCSPSelectiveStage.globalInitialControl a q,
            (stageInitial, ((none, none), T.1))), T.2⟩ ∧
      suffix = SourceCSPCodec.rowFields (rows ⟨0, hm⟩) ++ rest ∧
      T.2 (SourceCSPStagedFirstRow.rowSlot (.inr 4)) = [true] ∧
      (∀ j : Fin q,
        T.2 (SourceCSPStagedFirstRow.rowSlot (.inl (j, 1))) =
          List.replicate ((rows ⟨0, hm⟩).1 j).val true) ∧
      T.2 (SourceCSPStagedFirstRow.rowSlot (.inr 0)) = rest ∧
      T.2 (SourceCSPStagedFirstRow.rowSlot (.inr 2)) =
        true :: List.ofFn (rows ⟨0, hm⟩).2 ∧
      (∀ g : SourceCSPGlobalDecisionProgram.Stack q,
        T.2 (.inl g) = S g) := by
  obtain ⟨u, B, hu, hglobalRun, hleft, hblank⟩ :=
    global_handoff a q input tg (.row (vr, some true)) S hglobal
  have hsavedB : B SourceCSPSecondPassInput.savedSource = suffix := by
    change B (.inl SourceCSPGlobalDecisionProgram.savedSource) = suffix
    exact (hleft _).trans hsaved
  have hcapB : B SourceCSPSecondPassInput.capSource =
      List.replicate (n - 1) true := by
    change B (.inl SourceCSPHeaderRowBridge.capSource) = _
    exact (hleft _).trans hcap
  obtain ⟨tb, T, rest, htb, hbody, hsuffix, hstatus,
    hunary, hsource, houtput, hglobalFinal⟩ :=
    body_accepted_run suffix rows hm hn B hsavedB hcapB hblank hread
  let cb : TM2.Cfg (fun _ : Stack q => Bool) (BodyLabel q a) BodyControl :=
    ⟨some (bodyStart (q := q) (a := a)), bodyInitial, B⟩
  have hbh : (((advance (bodyProgram q a))^[tb]) cb).l = none := by
    rw [show cb = (⟨some (bodyStart (q := q) (a := a)),
      bodyInitial, B⟩ :
      TM2.Cfg (fun _ : Stack q => Bool) (BodyLabel q a) BodyControl) by rfl,
      hbody]
  obtain ⟨v, hv, hinline⟩ := BitMachineInline.outputs
    BitMachineRawSequence.rightLabel
    (fun w => (SourceCSPSelectiveStage.globalInitialControl a q, w))
    Prod.snd (fun _ => rfl) none (bodyProgram q a)
    (program a q) (by intro l; rfl) cb tb hbh
  have hstart : BitMachineInline.cfg BitMachineRawSequence.rightLabel
      (fun w => (SourceCSPSelectiveStage.globalInitialControl a q, w))
      none cb =
      (⟨some (BitMachineRawSequence.rightLabel
          (bodyStart (q := q) (a := a))),
        (SourceCSPSelectiveStage.globalInitialControl a q, bodyInitial), B⟩ :
        TM2.Cfg (fun _ : Stack q => Bool) (Label a q) (Control a q)) := rfl
  have hjoin : ((advance (program a q))^[u + 1 + v])
      (initial a q input) =
      ⟨none,
        (SourceCSPSelectiveStage.globalInitialControl a q,
          (stageInitial, ((none, none), T.1))), T.2⟩ := by
    rw [show u + 1 + v = v + (u + 1) by omega,
      Function.iterate_add_apply,
      Function.iterate_succ_apply', hglobalRun,
      handoff_accepted a q vr B, ← hstart, hinline,
      show cb = (⟨some (bodyStart (q := q) (a := a)),
        bodyInitial, B⟩ :
        TM2.Cfg (fun _ : Stack q => Bool) (BodyLabel q a) BodyControl) by rfl,
      hbody]
    rfl
  refine ⟨u + 1 + v, T, rest, ?_, hjoin, hsuffix,
    hstatus, hunary, hsource, houtput, ?_⟩
  · omega
  · intro g
    exact (hglobalFinal g).trans (hleft g)

/-- Nonaccepted global results halt at the verdict instruction. The writer
bank is still blank and every global cell, including output, is unchanged. -/
theorem nonaccepted_controller_run (a q : Nat) (input : List Bool)
    (tg : Nat) (c : GlobalControl a q)
    (S : SourceCSPGlobalDecisionProgram.Stack q → List Bool)
    (hglobal : ((advance (SourceCSPGlobalDecisionProgram.program a q))^[tg])
      (SourceCSPGlobalDecisionProgram.initial a q input) =
        ⟨none, c, S⟩)
    (hc : SourceCSPSelectiveStage.acceptedControl c = false) :
    ∃ (t : Nat) (U : Stack q → List Bool),
      t ≤ tg + 1 ∧
      ((advance (program a q))^[t]) (initial a q input) =
        ⟨none, (c, bodyInitial), U⟩ ∧
      (∀ g : SourceCSPGlobalDecisionProgram.Stack q,
        U (.inl g) = S g) ∧
      (∀ k : SourceClauseRowWriterOperands.Stack q,
        U (.inr k) = []) := by
  obtain ⟨u, U, hu, hrun, hleft, hblank⟩ :=
    global_handoff a q input tg c S hglobal
  refine ⟨u + 1, U, by omega, ?_, hleft, hblank⟩
  rw [Function.iterate_succ_apply', hrun,
    handoff_nonaccepted a q c U hc]

def uniformStageBound (q L : Nat) : Nat :=
  (2 * L + 2) + (2 * (q * L) + 2) + 3

def uniformRowBound (a q L : Nat) : Nat :=
  2 * (q * L) + 5 + q * (2 * L + 4) +
    2 * a ^ q + 3 + q * (100 * (q * L + 1) ^ 2) + 2

noncomputable def controllerBound (a q L : Nat) : Nat :=
  SourceCSPGlobalTotalValidation.totalBound a q L + 3 +
    uniformStageBound q L + uniformRowBound a q L

theorem bounds_le_uniform (a q n m L : Nat) (suffix : List Bool)
    (hsource : suffix.length ≤ L) (hsize : n ≤ q * m)
    (hmL : m ≤ L) :
    stageBound suffix n ≤ uniformStageBound q L ∧
      rowBound a q n suffix ≤ uniformRowBound a q L := by
  have hqm : q * m ≤ q * L := Nat.mul_le_mul_left q hmL
  have hnL : n ≤ q * L := hsize.trans hqm
  have hcapL : n - 1 ≤ q * L := by omega
  have hsource2 : 2 * suffix.length ≤ 2 * L :=
    Nat.mul_le_mul_left 2 hsource
  have hquery : q * (2 * suffix.length + 4) ≤ q * (2 * L + 4) :=
    Nat.mul_le_mul_left q (by omega)
  have hsquare : (n + 1) ^ 2 ≤ (q * L + 1) ^ 2 :=
    Nat.pow_le_pow_left (by omega) 2
  have hweighted : q * (100 * (n + 1) ^ 2) ≤
      q * (100 * (q * L + 1) ^ 2) :=
    Nat.mul_le_mul_left q (Nat.mul_le_mul_left 100 hsquare)
  constructor
  · unfold stageBound uniformStageBound
    omega
  · unfold rowBound uniformRowBound
    omega

/-- A single raw-input machine terminates on every bit list. Reject and zero
branches retain the exact validator output and blank writer bank; acceptance
physically stages and parses the first typed row. No parsed-data or success
certificate is supplied to this theorem. -/
theorem raw_total_first_row (a q : Nat) (input : List Bool) :
    ∃ (tg : Nat) (c : GlobalControl a q)
      (S : SourceCSPGlobalDecisionProgram.Stack q → List Bool)
      (t : Nat) (v : Control a q) (U : Stack q → List Bool),
      tg ≤ SourceCSPGlobalTotalValidation.totalBound a q input.length + 1 ∧
      ((advance (SourceCSPGlobalDecisionProgram.program a q))^[tg])
        (SourceCSPGlobalDecisionProgram.initial a q input) =
          ⟨none, c, S⟩ ∧
      t ≤ controllerBound a q input.length ∧
      ((advance (program a q))^[t]) (initial a q input) =
        ⟨none, v, U⟩ ∧
      (∀ g : SourceCSPGlobalDecisionProgram.Stack q,
        U (.inl g) = S g) ∧
      ((SourceCSPSelectiveStage.acceptedControl c = false ∧
          S SourceCSPGlobalDecisionProgram.outputSlot =
            SourceCSPRejectFormula.bits ∧
          U (.inl SourceCSPGlobalDecisionProgram.outputSlot) =
            SourceCSPRejectFormula.bits ∧
          S SourceCSPGlobalDecisionProgram.outputSlot ∉
            EncodedCNF.Language ∧
          (∀ k : SourceClauseRowWriterOperands.Stack q,
            U (.inr k) = [])) ∨
       (c = .prefix (SourceCSPGuardOutputCombined.zeroControl, none) ∧
          U (.inl SourceCSPGlobalDecisionProgram.outputSlot) =
            [false, false] ∧
          (∀ k : SourceClauseRowWriterOperands.Stack q,
            U (.inr k) = [])) ∨
       (∃ (n m : Nat) (hm : 0 < m) (suffix rest : List Bool)
          (rows : Fin m → SourceCSPCodec.Row n a q)
          (vr : SourceCSPRowLoopController.QueryControl ×
            SourceCSPRowLoopController.ResetControl),
          0 < n ∧ n ≤ q * m ∧ m ≤ input.length ∧
          input = SourceCSPHeaderParse.header n m a q ++ suffix ∧
          SourceCSPCodec.readFn (SourceCSPCodec.readRow n a q) m suffix =
            some (rows, []) ∧
          c = .row (vr, some true) ∧
          v.1 = SourceCSPSelectiveStage.globalInitialControl a q ∧
          v.2.1 = stageInitial ∧ v.2.2.1 = (none, none) ∧
          suffix = SourceCSPCodec.rowFields (rows ⟨0, hm⟩) ++ rest ∧
          U (SourceCSPStagedFirstRow.rowSlot (.inr 4)) = [true] ∧
          (∀ j : Fin q,
            U (SourceCSPStagedFirstRow.rowSlot (.inl (j, 1))) =
              List.replicate ((rows ⟨0, hm⟩).1 j).val true) ∧
          U (SourceCSPStagedFirstRow.rowSlot (.inr 0)) = rest ∧
          U (SourceCSPStagedFirstRow.rowSlot (.inr 2)) =
            true :: List.ofFn (rows ⟨0, hm⟩).2)) := by
  obtain ⟨tg, htg, c, S, hglobal, ts, hts, d, W,
    hselect, hcase⟩ :=
    SourceCSPTotalSelectiveScratch.raw_total_selective a q input
  rcases hcase with hreje | hzero | hacc
  · obtain ⟨hc, _, hout, hnlang, _, _⟩ := hreje
    obtain ⟨t, U, ht, hrun, hleft, hblank⟩ :=
      nonaccepted_controller_run a q input tg c S hglobal hc
    refine ⟨tg, c, S, t, (c, bodyInitial), U,
      htg, hglobal, ?_, hrun, hleft, Or.inl ?_⟩
    · unfold controllerBound
      omega
    · exact ⟨hc, hout, (hleft _).trans hout, hnlang, hblank⟩
  · obtain ⟨hc, _, hout, _, _⟩ := hzero
    have hnot : SourceCSPSelectiveStage.acceptedControl c = false := by
      rw [hc]
      rfl
    obtain ⟨t, U, ht, hrun, hleft, hblank⟩ :=
      nonaccepted_controller_run a q input tg c S hglobal hnot
    refine ⟨tg, c, S, t, (c, bodyInitial), U,
      htg, hglobal, ?_, hrun, hleft, Or.inr (Or.inl ?_)⟩
    · unfold controllerBound
      omega
    · exact ⟨hc, (hleft _).trans hout, hblank⟩
  · obtain ⟨n, m, suffix, rows, vr, hc, _, hinput,
      hn, hsize, hmL, hread, hsaved, hcap,
      _, _, _, _, _⟩ := hacc
    have hm : 0 < m := by
      by_contra hnot
      have hm0 : m = 0 := Nat.eq_zero_of_not_pos hnot
      subst m
      simp at hsize
      omega
    have hterminal :
        ((advance (SourceCSPGlobalDecisionProgram.program a q))^[tg])
          (SourceCSPGlobalDecisionProgram.initial a q input) =
          ⟨none, .row (vr, some true), S⟩ := by
      rw [hc] at hglobal
      exact hglobal
    obtain ⟨t, T, rest, ht, hrun, hsuffix,
      hstatus, hunary, hsource, houtput, hleft⟩ :=
      accepted_controller_run input suffix rows tg vr S hn hm
        hterminal hsaved hcap hread
    have hsuffixL : suffix.length ≤ input.length := by
      have hlen := congrArg List.length hinput
      simp only [List.length_append] at hlen
      omega
    obtain ⟨hstageL, hrowL⟩ :=
      bounds_le_uniform a q n m input.length suffix
        hsuffixL hsize hmL
    refine ⟨tg, c, S, t,
      (SourceCSPSelectiveStage.globalInitialControl a q,
        (stageInitial, ((none, none), T.1))), T.2,
      htg, hglobal, ?_, hrun, hleft, Or.inr (Or.inr ?_)⟩
    · unfold controllerBound
      omega
    · refine ⟨n, m, hm, suffix, rest, rows, vr,
        hn, hsize, hmL, hinput, hread, hc,
        rfl, rfl, rfl, hsuffix, hstatus,
        hunary, hsource, houtput⟩

noncomputable def cubicCoefficient (a q : Nat) : Nat :=
  SourceCSPValidatorPolynomial.majorantCoefficient a q +
    25 + 12 * q + 2 * a ^ q + 100 * q * (q + 1) ^ 2

/-- The actual all-raw first-row controller has a fixed-parameter cubic
transition bound in the original bit-list length. This is not an all-row or
clause-writer bound. -/
theorem controllerBound_le_cubic (a q L : Nat) :
    controllerBound a q L ≤ cubicCoefficient a q * (L + 1) ^ 3 := by
  let X := L + 1
  let C := SourceCSPValidatorPolynomial.majorantCoefficient a q
  have hval := SourceCSPValidatorPolynomial.totalBound_le_cubic a q L
  change SourceCSPGlobalTotalValidation.totalBound a q L + 1 ≤
    C * X ^ 3 at hval
  have hX : 1 ≤ X := by dsimp [X]; omega
  have hX2 : X ≤ X ^ 2 := by nlinarith
  have hX3 : X ^ 2 ≤ X ^ 3 := by
    calc
      X ^ 2 = X ^ 2 * 1 := by omega
      _ ≤ X ^ 2 * X := Nat.mul_le_mul_left _ hX
      _ = X ^ 3 := by ring
  have hL : L ≤ X ^ 3 := by
    calc
      L ≤ X := by dsimp [X]; omega
      _ ≤ X ^ 2 := hX2
      _ ≤ X ^ 3 := hX3
  have h1 : 1 ≤ X ^ 3 := hX.trans (hX2.trans hX3)
  have hqLX : q * L + 1 ≤ (q + 1) * X := by
    dsimp [X]
    nlinarith
  have hqSquare : (q * L + 1) ^ 2 ≤
      (q + 1) ^ 2 * X ^ 3 := by
    calc
      (q * L + 1) ^ 2 ≤ ((q + 1) * X) ^ 2 :=
        Nat.pow_le_pow_left hqLX 2
      _ = (q + 1) ^ 2 * X ^ 2 := by ring
      _ ≤ (q + 1) ^ 2 * X ^ 3 :=
        Nat.mul_le_mul_left _ hX3
  have hlinear := Nat.mul_le_mul_left (6 * q + 2) hL
  have hconstant := Nat.mul_le_mul_left (2 * a ^ q + 19 + 4 * q) h1
  have hsquare := Nat.mul_le_mul_left (100 * q) hqSquare
  have hlinbound : uniformStageBound q L + uniformRowBound a q L =
      (6 * q + 2) * L + (2 * a ^ q + 17 + 4 * q) +
        100 * q * (q * L + 1) ^ 2 := by
    dsimp [uniformStageBound, uniformRowBound]
    ring
  have hextra : 2 + uniformStageBound q L + uniformRowBound a q L ≤
      (25 + 12 * q + 2 * a ^ q + 100 * q * (q + 1) ^ 2) * X ^ 3 := by
    rw [show 2 + uniformStageBound q L + uniformRowBound a q L =
      2 + (uniformStageBound q L + uniformRowBound a q L) by omega,
      hlinbound]
    have htwo := Nat.mul_le_mul_left 2 h1
    nlinarith only [hlinear, hconstant, hsquare, htwo]
  have hsum := Nat.add_le_add hval hextra
  calc
    controllerBound a q L =
        (SourceCSPGlobalTotalValidation.totalBound a q L + 1) +
        (2 + uniformStageBound q L + uniformRowBound a q L) := by
      dsimp [controllerBound]
      omega
    _ ≤ C * X ^ 3 +
        (25 + 12 * q + 2 * a ^ q + 100 * q * (q + 1) ^ 2) * X ^ 3 := hsum
    _ = cubicCoefficient a q * (L + 1) ^ 3 := by
      dsimp [cubicCoefficient, C, X]
      ring

theorem raw_total_first_row_halts_cubic (a q : Nat) (input : List Bool) :
    ∃ t ≤ cubicCoefficient a q * (input.length + 1) ^ 3,
      ∃ (v : Control a q) (U : Stack q → List Bool),
        ((advance (program a q))^[t]) (initial a q input) =
          ⟨none, v, U⟩ := by
  obtain ⟨_, _, _, t, v, U, _, _, ht, hrun, _, _⟩ :=
    raw_total_first_row a q input
  exact ⟨t, ht.trans (controllerBound_le_cubic a q input.length),
    v, U, hrun⟩


end EthInapproximability.CurrentPaper.SourceCSPFirstRowController
