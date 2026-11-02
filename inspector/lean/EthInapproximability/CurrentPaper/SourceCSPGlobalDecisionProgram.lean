import EthInapproximability.CurrentPaper.SourceCSPGuardOutputCombined
import EthInapproximability.CurrentPaper.SourceCSPPositiveRowTotalBridge

/-!
# One raw CSP controller through header, cap, and corrected rows

This finite instruction table inlines the existing all-raw guarded header
and reject/zero writers, then conditionally runs the positive vertex cap,
literal row-bank preparation, and corrected all-input row loop. Failure at
either positive check writes the same fixed rejecting 3CNF. A successful
positive row parse currently halts at an acceptance tag, before clause
emission; no CSP-to-3CNF converter conclusion is claimed here.
-/

namespace EthInapproximability.CurrentPaper.SourceCSPGlobalDecisionProgram

open Turing BitMachineEncoding BitMachineStackEmbedding

abbrev Stack (q : Nat) := SourceCSPHeaderRowBridge.Stack q
abbrev PrefixLabel (a q : Nat) := SourceCSPGuardOutputCombined.Label a q
abbrev CapLabel (q : Nat) := BitMachineRawSequence.Label Unit
  (SourceCSPPositiveCapEntry.CapLabel q)
abbrev PrepareLabel := SourceCSPHeaderRowBridge.Label5
abbrev RowLabel (a q : Nat) := SourceCSPRowLoopController.Label q (a ^ q)

inductive Label (a q : Nat) where
  | prefix (l : PrefixLabel a q)
  | afterPrefix
  | cap (l : CapLabel q)
  | capCheck
  | prepare (l : PrepareLabel)
  | rowHandoff
  | row (l : RowLabel a q)
  | afterRow
  | rejectWriter (l : SourceCSPRejectWriter.Label)
  | accept
  | rowCopy (l : BitMachineCopy.Label)
  | rowBegin

def labelCode {a q : Nat} : Label a q →
    (PrefixLabel a q ⊕ (Unit ⊕ (CapLabel q ⊕ (Unit ⊕
      (PrepareLabel ⊕ (Unit ⊕ (RowLabel a q ⊕ (Unit ⊕
        (SourceCSPRejectWriter.Label ⊕ Unit))))))))) ⊕
      (BitMachineCopy.Label ⊕ Unit)
  | .prefix l => .inl (.inl l)
  | .afterPrefix => .inl (.inr (.inl ()))
  | .cap l => .inl (.inr (.inr (.inl l)))
  | .capCheck => .inl (.inr (.inr (.inr (.inl ()))))
  | .prepare l => .inl (.inr (.inr (.inr (.inr (.inl l)))))
  | .rowHandoff => .inl (.inr (.inr (.inr (.inr (.inr (.inl ()))))))
  | .row l => .inl (.inr (.inr (.inr (.inr (.inr (.inr (.inl l)))))))
  | .afterRow => .inl (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl ()))))))))
  | .rejectWriter l => .inl (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl l)))))))))
  | .accept => .inl (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr ())))))))))
  | .rowCopy l => .inr (.inl l)
  | .rowBegin => .inr (.inr ())

instance (a q : Nat) : Finite (Label a q) :=
  Finite.of_injective labelCode (by
    intro x y h
    cases x <;> cases y <;> simp [labelCode] at h <;> simp_all)

noncomputable instance (a q : Nat) : Fintype (Label a q) :=
  Fintype.ofFinite _

inductive Control (a q : Nat) where
  | prefix (v : SourceCSPGuardOutputCombined.Control)
  | cap (v : Unit × SourceCSPPositiveCapEntry.CapControl)
  | capStatus (b : Option Bool)
  | prepare (v : SourceCSPHeaderRowBridge.Control5)
  | row (v : SourceCSPRowLoopController.Control)
  | rowCopy (v : Option Bool)
  | writer (v : Option Bool)
  | done

def inputEmbedding {q : Nat} : SourceCSPInputFrame.Stack ↪ Stack q where
  toFun k := .inl (.inl k)
  inj' := by intro x y h; exact Sum.inl.inj (Sum.inl.inj h)

def capEmbedding {q : Nat} : SourceCSPBudgetFrame.Stack ↪ Stack q :=
  SourceCSPHeaderRowBridge.headerEmbedding

def savedSource {q : Nat} : Stack q :=
  SourceCSPHeaderRowBridge.scratch

def copyWork {q : Nat} : Stack q := .inr (.inr 2)

def retentionEmbedding {q : Nat} : Fin 3 ↪ Stack q where
  toFun k := if k = 0 then SourceCSPHeaderRowBridge.source else
    if k = 1 then savedSource else copyWork
  inj' := by
    intro x y h
    fin_cases x <;> fin_cases y <;>
      simp [SourceCSPHeaderRowBridge.source,
        SourceCSPHeaderRowBridge.scratch, savedSource, copyWork] at h <;>
      simp_all

def initial (a q : Nat) (input : List Bool) :
    TM2.Cfg (fun _ : Stack q => Bool) (Label a q) (Control a q) :=
  ⟨some (.prefix (.prefix (.inl
      (SourceCSPGuardDispatchSequence.headerStart a q)))),
    .prefix SourceCSPGuardOutputCombined.initialControl,
    SourceCSPHeaderRowBridge.initial input⟩

def capInitial : Unit × SourceCSPPositiveCapEntry.CapControl :=
  ((), (((none, none), (((none, none), (none, false)), none))))

def program (a q : Nat) : Label a q →
    TM2.Stmt (fun _ : Stack q => Bool) (Label a q) (Control a q)
  | .prefix l =>
      stmt inputEmbedding Label.prefix Control.prefix
        (fun x => match x with
          | Control.prefix v => v
          | _ => SourceCSPGuardOutputCombined.initialControl)
        (some .afterPrefix)
        (SourceCSPGuardOutputCombined.program a q l)
  | .afterPrefix =>
      .branch (fun v => match v with
        | .prefix w => w.1.2.2 == some .positive
        | _ => false)
        (.load (fun _ => .cap capInitial)
          (.goto (fun _ => .cap (.inl SourceCSPPositiveCapEntry.start))))
        .halt
  | .cap l =>
      stmt capEmbedding Label.cap Control.cap
        (fun x => match x with
          | Control.cap v => v
          | _ => capInitial)
        (some .capCheck) (SourceCSPPositiveCapEntry.program q l)
  | .capCheck =>
      .peek SourceCSPHeaderRowBridge.capSource
        (fun _ b => .capStatus b)
        (.branch (fun v => match v with
          | .capStatus (some true) => true
          | _ => false)
          (.load (fun _ => .prepare SourceCSPHeaderRowBridge.prepareStart)
            (.goto (fun _ => .prepare
              (.inl (.inl (.inl (.inl .scan)))))))
          (.load (fun _ => .writer none)
            (.goto (fun _ => .rejectWriter .clear))))
  | .prepare l =>
      BitMachineInline.stmt Label.prepare Control.prepare
        (fun x => match x with
          | Control.prepare v => v
          | _ => SourceCSPHeaderRowBridge.prepareStart)
        (some .rowHandoff)
        (SourceCSPHeaderRowBridge.prepareProgram l)
  | .rowHandoff =>
      .load (fun _ => .rowCopy none)
        (.goto (fun _ => .rowCopy .scan))
  | .rowCopy l =>
      stmt retentionEmbedding Label.rowCopy Control.rowCopy
        (fun x => match x with
          | .rowCopy v => v
          | _ => none)
        (some .rowBegin) (BitMachineCopy.program l)
  | .rowBegin =>
      .load (fun _ => .row SourceCSPRowLoopController.initialControl)
        (.goto (fun _ => .row
          (SourceCSPRowLoopController.adminLabel .check)))
  | .row l =>
      stmt SourceCSPHeaderRowBridge.rowEmbedding Label.row Control.row
        (fun x => match x with
          | Control.row v => v
          | _ => SourceCSPRowLoopController.initialControl)
        (some .afterRow)
        (SourceCSPRowLoopTotalController.program q (a ^ q) l)
  | .afterRow =>
      .branch (fun v => match v with
        | .row w => w.2 == some true
        | _ => false)
        (.goto (fun _ => .accept))
        (.load (fun _ => .writer none)
          (.goto (fun _ => .rejectWriter .clear)))
  | .rejectWriter l =>
      stmt inputEmbedding Label.rejectWriter Control.writer
        (fun x => match x with
          | Control.writer v => v
          | _ => none)
        none (SourceCSPRejectWriterFrame.program l)
  | .accept => .halt

/-- On every raw bitstring, the shared-bank global program runs the complete
guarded header and literal reject/zero writer prefix to its administrative
handoff. All input stacks are physically embedded; no parser result is
inserted off-line. -/
theorem all_input_prefix (a q : Nat) (input : List Bool) :
    ∃ (t : Nat) (c : SourceCSPGuardOutputCombined.Control)
      (T : SourceCSPInputFrame.Stack → List Bool)
      (S : Stack q → List Bool),
      t ≤ SourceCSPGuardOutputCombined.polyBound a q input.length ∧
      ((advance (program a q))^[t]) (initial a q input) =
        (⟨some .afterPrefix, .prefix c, S⟩ :
          TM2.Cfg (fun _ : Stack q => Bool)
            (Label a q) (Control a q)) ∧
      (∀ k : SourceCSPInputFrame.Stack,
        S (inputEmbedding k) = T k) := by
  obtain ⟨tc, T, c, _, htc, hrc, _, _⟩ :=
    SourceCSPGuardOutputCombined.all_input_polynomial a q input
  let localCfg := SourceCSPGuardOutputCombined.initial a q input
  have hhalt : (((advance
      (SourceCSPGuardOutputCombined.program a q))^[tc])
      localCfg).l = none := by
    simpa only [localCfg] using congrArg (fun x => x.l) hrc
  let before := SourceCSPHeaderRowBridge.initial (q := q) input
  let read : Control a q → SourceCSPGuardOutputCombined.Control :=
    fun x => match x with
      | .prefix v => v
      | _ => SourceCSPGuardOutputCombined.initialControl
  have hleft : Function.LeftInverse read Control.prefix := by
    intro v
    rfl
  obtain ⟨t, ht, hr⟩ := outputs
    (inputEmbedding (q := q)) before Label.prefix Control.prefix
    read hleft (some .afterPrefix)
    (SourceCSPGuardOutputCombined.program a q) (program a q)
    (fun _ => rfl) localCfg tc hhalt
  have hstart : BitMachineStackEmbedding.cfg
      (inputEmbedding (q := q)) before Label.prefix Control.prefix
      (some .afterPrefix) localCfg = initial a q input := by
    simp only [BitMachineStackEmbedding.cfg, stackCfg,
      BitMachineInline.cfg, localCfg, initial,
      SourceCSPGuardOutputCombined.initial, before]
    congr 1
    apply bank_eq_self
    intro k
    rfl
  rw [hrc, hstart] at hr
  let S := bank (inputEmbedding (q := q)) before T
  refine ⟨t, c, T, S, ht.trans htc, ?_, ?_⟩
  · simpa only [S, BitMachineStackEmbedding.cfg, stackCfg,
      BitMachineInline.cfg, id_eq, Option.map_none] using hr
  · intro k
    exact bank_at (inputEmbedding (q := q)) before T k

theorem after_prefix_positive (a q : Nat)
    (v : SourceCSPGuardOutputCombined.Control)
    (S : Stack q → List Bool)
    (hv : v.1.2.2 = some .positive) :
    advance (program a q)
      (⟨some .afterPrefix, .prefix v, S⟩ :
        TM2.Cfg (fun _ : Stack q => Bool)
          (Label a q) (Control a q)) =
      ⟨some (.cap (.inl SourceCSPPositiveCapEntry.start)),
        .cap capInitial, S⟩ := by
  simp [advance, TM2.step, TM2.stepAux, program, hv]

theorem after_prefix_nonpositive (a q : Nat)
    (v : SourceCSPGuardOutputCombined.Control)
    (S : Stack q → List Bool)
    (hv : v.1.2.2 ≠ some .positive) :
    advance (program a q)
      (⟨some .afterPrefix, .prefix v, S⟩ :
        TM2.Cfg (fun _ : Stack q => Bool)
          (Label a q) (Control a q)) =
      ⟨none, .prefix v, S⟩ := by
  have hbeq : (v.1.2.2 == some SourceCSPGuardDispatch.Outcome.positive) =
      false := by
    apply Bool.eq_false_iff.mpr
    intro h
    exact hv (by simpa using h)
  simp [advance, TM2.step, TM2.stepAux, program, hbeq]

/-- A terminating cap run on the actual header bank is lifted into the
single global instruction table, with every cap-bank cell preserved exactly
at the administrative cap-status handoff. -/
theorem cap_lift (a q : Nat) (before : Stack q → List Bool)
    (t : Nat) (v : Unit × SourceCSPPositiveCapEntry.CapControl)
    (T : SourceCSPBudgetFrame.Stack → List Bool)
    (hr : ((advance (SourceCSPPositiveCapEntry.program q))^[t])
      (⟨some (.inl SourceCSPPositiveCapEntry.start), capInitial,
        fun k => before (capEmbedding k)⟩ :
          TM2.Cfg (fun _ : SourceCSPBudgetFrame.Stack => Bool)
            (CapLabel q) (Unit × SourceCSPPositiveCapEntry.CapControl)) =
      ⟨none, v, T⟩) :
    ∃ u S, u ≤ t ∧
      ((advance (program a q))^[u])
        (⟨some (.cap (.inl SourceCSPPositiveCapEntry.start)),
          .cap capInitial, before⟩ :
          TM2.Cfg (fun _ : Stack q => Bool) (Label a q) (Control a q)) =
        ⟨some .capCheck, .cap v, S⟩ ∧
      (∀ k : SourceCSPBudgetFrame.Stack, S (capEmbedding k) = T k) ∧
      (∀ k : Stack q, (¬ ∃ j, capEmbedding j = k) → S k = before k) := by
  let read : Control a q → Unit × SourceCSPPositiveCapEntry.CapControl :=
    fun x => match x with
      | .cap v => v
      | _ => capInitial
  have hleft : Function.LeftInverse read Control.cap := by
    intro v
    rfl
  let localCfg : TM2.Cfg (fun _ : SourceCSPBudgetFrame.Stack => Bool)
      (CapLabel q) (Unit × SourceCSPPositiveCapEntry.CapControl) :=
    ⟨some (.inl SourceCSPPositiveCapEntry.start), capInitial,
      fun k => before (capEmbedding k)⟩
  have hhalt : (((advance (SourceCSPPositiveCapEntry.program q))^[t])
      localCfg).l = none := by
    simpa only [localCfg] using congrArg (fun x => x.l) hr
  obtain ⟨u, hu, hlift⟩ := outputs
    (capEmbedding (q := q)) before Label.cap Control.cap
    read hleft (some .capCheck)
    (SourceCSPPositiveCapEntry.program q) (program a q)
    (fun _ => rfl) localCfg t hhalt
  rw [hr] at hlift
  let S := bank (capEmbedding (q := q)) before T
  have hstart : BitMachineStackEmbedding.cfg
      (capEmbedding (q := q)) before Label.cap Control.cap
      (some .capCheck) localCfg =
      (⟨some (.cap (.inl SourceCSPPositiveCapEntry.start)),
        .cap capInitial, before⟩ :
        TM2.Cfg (fun _ : Stack q => Bool) (Label a q) (Control a q)) := by
    simp only [BitMachineStackEmbedding.cfg, stackCfg,
      BitMachineInline.cfg, localCfg]
    congr 1
    apply bank_eq_self
    intro k
    rfl
  rw [hstart] at hlift
  refine ⟨u, S, hu, ?_, ?_, ?_⟩
  · simpa only [S, BitMachineStackEmbedding.cfg, stackCfg,
      BitMachineInline.cfg, id_eq, Option.map_none] using hlift
  · intro k
    exact bank_at (capEmbedding (q := q)) before T k
  · intro k hk
    exact bank_outside (capEmbedding (q := q)) before T k hk

theorem cap_check_good (a q : Nat)
    (v : Unit × SourceCSPPositiveCapEntry.CapControl)
    (S : Stack q → List Bool) (tail : List Bool)
    (hcap : S SourceCSPHeaderRowBridge.capSource = true :: tail) :
    advance (program a q)
      (⟨some .capCheck, .cap v, S⟩ :
        TM2.Cfg (fun _ : Stack q => Bool) (Label a q) (Control a q)) =
      ⟨some (.prepare (.inl (.inl (.inl (.inl .scan))))),
        .prepare SourceCSPHeaderRowBridge.prepareStart, S⟩ := by
  simp [advance, TM2.step, TM2.stepAux, program, hcap]

theorem cap_check_bad (a q : Nat)
    (v : Unit × SourceCSPPositiveCapEntry.CapControl)
    (S : Stack q → List Bool)
    (hcap : (S SourceCSPHeaderRowBridge.capSource).head? ≠ some true) :
    advance (program a q)
      (⟨some .capCheck, .cap v, S⟩ :
        TM2.Cfg (fun _ : Stack q => Bool) (Label a q) (Control a q)) =
      ⟨some (.rejectWriter .clear), .writer none, S⟩ := by
  cases hx : (S SourceCSPHeaderRowBridge.capSource).head? with
  | none => simp [advance, TM2.step, TM2.stepAux, program, hx]
  | some b =>
      cases b with
      | false => simp [advance, TM2.step, TM2.stepAux, program, hx]
      | true => exact False.elim (hcap hx)

theorem after_row_success (a q : Nat)
    (v : SourceCSPRowLoopController.QueryControl ×
      SourceCSPRowLoopController.ResetControl)
    (S : Stack q → List Bool) :
    advance (program a q)
      (⟨some .afterRow, .row (v, some true), S⟩ :
        TM2.Cfg (fun _ : Stack q => Bool) (Label a q) (Control a q)) =
      ⟨some .accept, .row (v, some true), S⟩ := by
  rfl

theorem after_row_failure (a q : Nat)
    (v : SourceCSPRowLoopController.QueryControl ×
      SourceCSPRowLoopController.ResetControl)
    (S : Stack q → List Bool) :
    advance (program a q)
      (⟨some .afterRow, .row (v, some false), S⟩ :
        TM2.Cfg (fun _ : Stack q => Bool) (Label a q) (Control a q)) =
      ⟨some (.rejectWriter .clear), .writer none, S⟩ := by
  rfl

end EthInapproximability.CurrentPaper.SourceCSPGlobalDecisionProgram
