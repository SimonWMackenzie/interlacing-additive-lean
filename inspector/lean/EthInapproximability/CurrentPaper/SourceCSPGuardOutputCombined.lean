import EthInapproximability.CurrentPaper.SourceCSPGuardDispatchPreserve
import EthInapproximability.CurrentPaper.SourceCSPGuardOutputRouter
import EthInapproximability.CurrentPaper.SourceCSPZeroWriter
import EthInapproximability.CurrentPaper.BitMachineStackGrowth

/-!
# Raw CSP prefix with retained branch outcome and literal output arms

This instruction table inlines the all-input guard-and-dispatch machine and
retains its finite-control outcome at the handoff. The zero and rejecting
arms write literal canonical CNF bits; the positive arm remains a handoff to
the cap, corrected row loop, and clause writer.
-/

namespace EthInapproximability.CurrentPaper.SourceCSPGuardOutputCombined

open Turing BitMachineEncoding BitMachineInline

abbrev Stack := SourceCSPInputFrame.Stack
abbrev PrefixLabel (a q : Nat) :=
  BitMachineRawSequence.Label
    (SourceCSPGuardDispatchSequence.HeaderLabel a q)
    SourceCSPGuardDispatch.Label
abbrev PrefixControl :=
  SourceCSPGuardDispatchSequence.HeaderControl ×
    SourceCSPGuardDispatch.Control
abbrev Control := PrefixControl × Option Bool

inductive Label (a q : Nat) where
  | prefix (l : PrefixLabel a q)
  | route | rejectWriter (l : SourceCSPRejectWriter.Label)
  | zeroWriter (l : SourceCSPZeroWriter.Label) | positive

def labelCode {a q : Nat} : Label a q →
    PrefixLabel a q ⊕ (Unit ⊕
      (SourceCSPRejectWriter.Label ⊕
        (SourceCSPZeroWriter.Label ⊕ Unit)))
  | .prefix l => .inl l
  | .route => .inr (.inl ())
  | .rejectWriter l => .inr (.inr (.inl l))
  | .zeroWriter l => .inr (.inr (.inr (.inl l)))
  | .positive => .inr (.inr (.inr (.inr ())))

instance (a q : Nat) : Finite (Label a q) :=
  Finite.of_injective labelCode (by
    intro x y h
    cases x <;> cases y <;> simp [labelCode] at h <;> simp_all)

noncomputable instance (a q : Nat) : Fintype (Label a q) :=
  Fintype.ofFinite _

def initialControl : Control :=
  ((SourceCSPGuardDispatchSequence.headerInitial,
    SourceCSPGuardDispatch.initialControl), none)

def rejectControl : PrefixControl :=
  (SourceCSPGuardDispatchSequence.headerInitial,
    ((none, none, none), some .reject))

def zeroControl : PrefixControl :=
  (SourceCSPGuardDispatchSequence.headerInitial,
    ((none, none, none), some .zero))

def program (a q : Nat) : Label a q →
    TM2.Stmt (fun _ : Stack => Bool) (Label a q) Control
  | .prefix l =>
      stmt Label.prefix (fun v => (v, none)) Prod.fst (some .route)
        (SourceCSPGuardDispatchSequence.program a q l)
  | .route =>
      .branch (fun v => v.1.2.2 == some .reject)
        (.load (fun _ => (rejectControl, none))
          (.goto (fun _ => .rejectWriter .clear)))
        (.branch (fun v => v.1.2.2 == some .zero)
          (.load (fun _ => (zeroControl, none))
            (.goto (fun _ => .zeroWriter .clear)))
          (.goto (fun _ => .positive)))
  | .rejectWriter l =>
      stmt Label.rejectWriter (fun w => (rejectControl, w)) Prod.snd none
        (SourceCSPRejectWriterFrame.program l)
  | .zeroWriter l =>
      stmt Label.zeroWriter (fun w => (zeroControl, w)) Prod.snd none
        (SourceCSPZeroWriterFrame.program l)
  | .positive => .halt

def initial (a q : Nat) (input : List Bool) :
    TM2.Cfg (fun _ : Stack => Bool) (Label a q) Control :=
  ⟨some (.prefix (.inl (SourceCSPGuardDispatchSequence.headerStart a q))),
    initialControl, SourceCSPInputFrame.initial input⟩

/-- The actual raw prefix reaches this controller's route label with its
outcome still in control. It uses no offline branch computation. -/
theorem all_input_prefix (a q : Nat) (input : List Bool) :
    ∃ (t : Nat) (v : PrefixControl)
      (S S₀ : Stack → List Bool) (wa wq word : List Bool),
      t ≤ SourceCSPGuardDispatchSequence.bound a q input.length ∧
      ((advance (program a q))^[t]) (initial a q input) =
        (⟨some .route, (v, none), S⟩ :
          TM2.Cfg (fun _ : Stack => Bool) (Label a q) Control) ∧
      v.2.2 = some (SourceCSPGuardDispatch.classify
        ((SourceCSPHeaderValidFlag.parserGood input &&
          decide (wq = q.bits) && decide (wa = a.bits)) &&
          decide (EncodedCommunication.bitsValue word ≤ input.length))
        (S₀ SourceCSPGuardDispatch.vertexSlot)
        (S₀ SourceCSPGuardDispatch.countSlot)
        (S₀ SourceCSPGuardDispatch.sourceSlot)) := by
  obtain ⟨tp, Sp, S₀, vp, wa, wq, word, htp, hrp, htag⟩ :=
    SourceCSPGuardDispatchSequence.all_input a q input
  let localCfg : TM2.Cfg (fun _ : Stack => Bool) (PrefixLabel a q)
      PrefixControl :=
    ⟨some (.inl (SourceCSPGuardDispatchSequence.headerStart a q)),
      (SourceCSPGuardDispatchSequence.headerInitial,
        SourceCSPGuardDispatch.initialControl),
      SourceCSPInputFrame.initial input⟩
  have hhalt : (((advance (SourceCSPGuardDispatchSequence.program a q))^[tp])
      localCfg).l = none := by
    simpa only [localCfg] using congrArg (fun c => c.l) hrp
  obtain ⟨t, ht, hr⟩ := BitMachineInline.outputs Label.prefix
    (fun v => (v, none)) Prod.fst (fun _ => rfl) (some .route)
    (SourceCSPGuardDispatchSequence.program a q) (program a q)
    (fun _ => rfl) localCfg tp hhalt
  rw [hrp] at hr
  refine ⟨t, (SourceCSPGuardDispatchSequence.headerInitial, vp),
    Sp, S₀, wa, wq, word, ht.trans htp, ?_, htag⟩
  simpa only [initial, initialControl, localCfg,
    BitMachineInline.cfg, Option.map_none] using hr

def routeRun (a q t : Nat) (v : PrefixControl)
    (S : Stack → List Bool) :=
  ((advance (program a q))^[t])
    (⟨some .route, (v, none), S⟩ :
      TM2.Cfg (fun _ : Stack => Bool) (Label a q) Control)

theorem route_reject (a q : Nat) (v : PrefixControl)
    (S : Stack → List Bool)
    (hv : v.2.2 = some .reject) :
    ∃ t T, t ≤ (S SourceCSPRejectWriterFrame.outputSlot).length + 4 ∧
      routeRun a q t v S =
        (⟨none, (rejectControl, none), T⟩ :
          TM2.Cfg (fun _ : Stack => Bool) (Label a q) Control) ∧
      T SourceCSPRejectWriterFrame.outputSlot =
        SourceCSPRejectFormula.bits ∧
      (∀ k : Stack, k ≠ SourceCSPRejectWriterFrame.outputSlot →
        T k = S k) := by
  obtain ⟨tw, Tw, htw, hrw, hout, hforeign⟩ :=
    SourceCSPRejectWriterFrame.reject_run S
  have hhalt : (((advance SourceCSPRejectWriterFrame.program)^[tw])
      (⟨some .clear, none, S⟩ :
        TM2.Cfg (fun _ : Stack => Bool)
          SourceCSPRejectWriter.Label (Option Bool))).l = none := by
    rw [hrw]
  obtain ⟨u, hu, hru⟩ := BitMachineInline.outputs
    Label.rejectWriter (fun w => (rejectControl, w)) Prod.snd
    (fun _ => rfl) none SourceCSPRejectWriterFrame.program
    (program a q) (fun _ => rfl)
    (⟨some .clear, none, S⟩ :
      TM2.Cfg (fun _ : Stack => Bool)
        SourceCSPRejectWriter.Label (Option Bool)) tw hhalt
  rw [hrw] at hru
  have hroute : advance (program a q)
      (⟨some .route, (v, none), S⟩ :
        TM2.Cfg (fun _ : Stack => Bool) (Label a q) Control) =
      ⟨some (.rejectWriter .clear), (rejectControl, none), S⟩ := by
    simp [advance, TM2.step, TM2.stepAux, program, hv]
  have htw' : tw ≤
      (S SourceCSPRejectWriterFrame.outputSlot).length + 3 := htw
  refine ⟨u + 1, Tw, by omega, ?_, hout, hforeign⟩
  change ((advance (program a q))^[u + 1]) _ = _
  rw [Function.iterate_succ_apply, hroute]
  simpa only [BitMachineInline.cfg, id_eq, Option.map_none] using hru

theorem route_zero (a q : Nat) (v : PrefixControl)
    (S : Stack → List Bool)
    (hv : v.2.2 = some .zero) :
    ∃ t T, t ≤ (S SourceCSPZeroWriterFrame.outputSlot).length + 4 ∧
      routeRun a q t v S =
        (⟨none, (zeroControl, none), T⟩ :
          TM2.Cfg (fun _ : Stack => Bool) (Label a q) Control) ∧
      T SourceCSPZeroWriterFrame.outputSlot = [false, false] ∧
      (∀ k : Stack, k ≠ SourceCSPZeroWriterFrame.outputSlot →
        T k = S k) := by
  obtain ⟨tw, Tw, htw, hrw, hout, hforeign⟩ :=
    SourceCSPZeroWriterFrame.zero_run S
  have hhalt : (((advance SourceCSPZeroWriterFrame.program)^[tw])
      (⟨some .clear, none, S⟩ :
        TM2.Cfg (fun _ : Stack => Bool)
          SourceCSPZeroWriter.Label (Option Bool))).l = none := by
    rw [hrw]
  obtain ⟨u, hu, hru⟩ := BitMachineInline.outputs
    Label.zeroWriter (fun w => (zeroControl, w)) Prod.snd
    (fun _ => rfl) none SourceCSPZeroWriterFrame.program
    (program a q) (fun _ => rfl)
    (⟨some .clear, none, S⟩ :
      TM2.Cfg (fun _ : Stack => Bool)
        SourceCSPZeroWriter.Label (Option Bool)) tw hhalt
  rw [hrw] at hru
  have hroute : advance (program a q)
      (⟨some .route, (v, none), S⟩ :
        TM2.Cfg (fun _ : Stack => Bool) (Label a q) Control) =
      ⟨some (.zeroWriter .clear), (zeroControl, none), S⟩ := by
    have hnot : (some SourceCSPGuardDispatch.Outcome.zero ==
        some SourceCSPGuardDispatch.Outcome.reject) = false := by decide
    simp [advance, TM2.step, TM2.stepAux, program, hv, hnot]
  have htw' : tw ≤
      (S SourceCSPZeroWriterFrame.outputSlot).length + 3 := htw
  refine ⟨u + 1, Tw, by omega, ?_, hout, hforeign⟩
  change ((advance (program a q))^[u + 1]) _ = _
  rw [Function.iterate_succ_apply, hroute]
  simpa only [BitMachineInline.cfg, id_eq, Option.map_none] using hru

theorem route_positive (a q : Nat) (v : PrefixControl)
    (S : Stack → List Bool) (hv : v.2.2 = some .positive) :
    routeRun a q 2 v S =
      (⟨none, (v, none), S⟩ :
        TM2.Cfg (fun _ : Stack => Bool) (Label a q) Control) := by
  have hr : (some SourceCSPGuardDispatch.Outcome.positive ==
      some SourceCSPGuardDispatch.Outcome.reject) = false := by decide
  have hz : (some SourceCSPGuardDispatch.Outcome.positive ==
      some SourceCSPGuardDispatch.Outcome.zero) = false := by decide
  simp [routeRun, Function.iterate_succ_apply', advance, TM2.step,
    TM2.stepAux, program, hv, hr, hz]

/-- Every raw bitstring reaches a literal terminal branch on this one finite
instruction table. Reject and zero produce their exact canonical CNF words.
The displayed bound still contains the intermediate output-cell length;
the separate global polynomial bound must charge that growth explicitly. -/
theorem all_input_branches (a q : Nat) (input : List Bool) :
    ∃ (tp t : Nat) (Sp T : Stack → List Bool)
      (v : PrefixControl) (tag : SourceCSPGuardDispatch.Outcome)
      (c : Control),
      tp ≤ SourceCSPGuardDispatchSequence.bound a q input.length ∧
      ((advance (program a q))^[tp]) (initial a q input) =
        (⟨some .route, (v, none), Sp⟩ :
          TM2.Cfg (fun _ : Stack => Bool) (Label a q) Control) ∧
      v.2.2 = some tag ∧
      t ≤ tp + (Sp SourceCSPRejectWriterFrame.outputSlot).length + 4 ∧
      ((advance (program a q))^[t]) (initial a q input) =
        (⟨none, c, T⟩ :
          TM2.Cfg (fun _ : Stack => Bool) (Label a q) Control) ∧
      (tag = .reject →
        T SourceCSPRejectWriterFrame.outputSlot =
          SourceCSPRejectFormula.bits) ∧
      (tag = .zero →
        T SourceCSPRejectWriterFrame.outputSlot = [false, false]) ∧
      (tag = .positive → T = Sp) := by
  obtain ⟨tp, v, Sp, S₀, wa, wq, word, htp, hrp, htag⟩ :=
    all_input_prefix a q input
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
      obtain ⟨tr, Tr, htr, hrr, hout, _⟩ :=
        route_reject a q v Sp (by simpa only [hcase] using hv)
      refine ⟨tp, tp + tr, Sp, Tr, v, .reject,
        (rejectControl, none), htp, hrp,
        by simpa only [hcase] using hv, by omega, ?_, ?_⟩
      · rw [show tp + tr = tr + tp by omega,
          Function.iterate_add_apply, hrp]
        exact hrr
      · simp [hout]
  | zero =>
      obtain ⟨tr, Tr, htr, hrr, hout, _⟩ :=
        route_zero a q v Sp (by simpa only [hcase] using hv)
      have htr' : tr ≤
          (Sp SourceCSPRejectWriterFrame.outputSlot).length + 4 := htr
      have hout' : Tr SourceCSPRejectWriterFrame.outputSlot =
          [false, false] := hout
      refine ⟨tp, tp + tr, Sp, Tr, v, .zero,
        (zeroControl, none), htp, hrp,
        by simpa only [hcase] using hv, by omega, ?_, ?_⟩
      · rw [show tp + tr = tr + tp by omega,
          Function.iterate_add_apply, hrp]
        exact hrr
      · simp [hout']
  | positive =>
      have hrr := route_positive a q v Sp
        (by simpa only [hcase] using hv)
      refine ⟨tp, tp + 2, Sp, Sp, v, .positive,
        (v, none), htp, hrp,
        by simpa only [hcase] using hv, by omega, ?_, ?_⟩
      · rw [show tp + 2 = 2 + tp by omega,
          Function.iterate_add_apply, hrp]
        exact hrr
      · simp

noncomputable def polyBound (a q L : Nat) : Nat :=
  (1 + BitMachineStackGrowth.perStep (program a q)) *
    SourceCSPGuardDispatchSequence.bound a q L + 4

/-- Uniform fixed-parameter polynomial transition bound on every raw input.
The intermediate count/output cell is charged by its syntactic push growth;
no inference from eventual output size to runtime is made. -/
theorem all_input_polynomial (a q : Nat) (input : List Bool) :
    ∃ (t : Nat) (T : Stack → List Bool) (c : Control)
      (tag : SourceCSPGuardDispatch.Outcome),
      t ≤ polyBound a q input.length ∧
      ((advance (program a q))^[t]) (initial a q input) =
        (⟨none, c, T⟩ :
          TM2.Cfg (fun _ : Stack => Bool) (Label a q) Control) ∧
      (tag = .reject →
        T SourceCSPRejectWriterFrame.outputSlot =
          SourceCSPRejectFormula.bits) ∧
      (tag = .zero →
        T SourceCSPRejectWriterFrame.outputSlot = [false, false]) := by
  obtain ⟨tp, t, Sp, T, v, tag, c, htp, hprefix,
    htag, ht, hrun, hreje, hzero, _⟩ :=
    all_input_branches a q input
  have hgrowth := BitMachineStackGrowth.run_growth
    (program a q) (initial a q input) tp
    SourceCSPRejectWriterFrame.outputSlot
  rw [hprefix] at hgrowth
  have hblank : (initial a q input).stk
      SourceCSPRejectWriterFrame.outputSlot = [] := by
    rfl
  rw [hblank] at hgrowth
  simp only [List.length_nil, Nat.zero_add] at hgrowth
  refine ⟨t, T, c, tag, ?_, hrun, hreje, hzero⟩
  unfold polyBound
  have hmul := Nat.mul_le_mul_left
    (1 + BitMachineStackGrowth.perStep (program a q)) htp
  simp only [add_mul, one_mul] at hmul ⊢
  omega

end EthInapproximability.CurrentPaper.SourceCSPGuardOutputCombined
