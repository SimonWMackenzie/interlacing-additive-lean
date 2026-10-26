import EthInapproximability.CurrentPaper.SourceGenericPrefixAmbientProgram
import EthInapproximability.CurrentPaper.SourceGenericStagedBlank

/-!
# Common bank and raw-input verdict controller for the generic converter

Paper B, locked v8 Section 6 (`thm:paper-sparse-gap-source`) and Appendix B;
CP-SOURCE-EFFECTIVE, arbitrary fixed alphabet `a`.

One physical bank `Stack q` hosts every phase of the generic converter: the
first-slot/row-loop bank (global validator cells, writer cells and the two
truth-frame cells), the generic prefix side work bank, and one scratch cell.

`top a q body b₀ w₀` is the raw-input controller shape of the admitted
`SourceCSPFirstRowController.program`: it runs the actual global validator
`SourceCSPGlobalDecisionProgram.program a q` (lifted to this bank), tests the
verdict while the validator control is still live, halts in place on reject
and zero, and on acceptance enters the fixed body. The lemmas below hold for
every body; they supply no body result.
-/

namespace EthInapproximability.CurrentPaper.SourceGenericComposite

open Turing BitMachineEncoding BitMachineStackEmbedding
open scoped Classical

abbrev Stack (q : Nat) :=
  (SourceCSPFirstSlotBridge.Stack q ⊕
    SourceGenericPrefixMachine.PrefixCopy.Stack) ⊕ Fin 1

/-- First-row-controller cells inside the first-slot bank (the same map as
`SourceCSPFirstSlotBridge.extended`). -/
def frToFsb (q : Nat) :
    SourceCSPFirstRowController.Stack q ↪ SourceCSPFirstSlotBridge.Stack q where
  toFun
    | .inl g => .inl g
    | .inr k => .inr (.inl k)
  inj' := by
    intro x y h
    cases x <;> cases y <;> simp_all

def fsbEmb (q : Nat) : SourceCSPFirstSlotBridge.Stack q ↪ Stack q :=
  Function.Embedding.inl.trans Function.Embedding.inl

def frEmb (q : Nat) : SourceCSPFirstRowController.Stack q ↪ Stack q :=
  (frToFsb q).trans (fsbEmb q)

def globalEmb (q : Nat) : SourceCSPGlobalDecisionProgram.Stack q ↪ Stack q :=
  (Function.Embedding.inl :
    SourceCSPGlobalDecisionProgram.Stack q ↪
      SourceCSPFirstRowController.Stack q).trans (frEmb q)

def ambMap (q : Nat) :
    SourceGenericPrefixMachine.PrefixAmbientCopy.Stack q → Stack q
  | .inl (.inl x) => .inl (.inl (frToFsb q x))
  | .inl (.inr w) => .inl (.inr w)
  | .inr s => .inr s

def ambEmb (q : Nat) :
    SourceGenericPrefixMachine.PrefixAmbientCopy.Stack q ↪ Stack q where
  toFun := ambMap q
  inj' := by
    intro x y h
    rcases x with (x | w) | s <;> rcases y with (y | w') | s' <;>
      simp only [ambMap, Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq] at h
    · rw [(frToFsb q).injective h]
    · rw [h]
    · rw [h]

theorem ambEmb_raw (q : Nat) (x : SourceCSPFirstRowController.Stack q) :
    ambEmb q (SourceGenericPrefixMachine.PrefixAmbientCopy.rawEmbedding q x) =
      frEmb q x := rfl

theorem ambEmb_work (q : Nat) (w : SourceGenericPrefixMachine.PrefixCopy.Stack) :
    ambEmb q (SourceGenericPrefixMachine.PrefixAmbientCopy.workEmbedding q w) =
      .inl (.inr w) := rfl

theorem ambEmb_scratch (q : Nat) :
    ambEmb q (SourceGenericPrefixMachine.PrefixAmbientCopy.scratch q) =
      .inr 0 := rfl

/-- Projection of a bank to its first-row-controller cells. -/
def frPart {q : Nat} (W : Stack q → List Bool) :
    SourceCSPFirstRowController.Stack q → List Bool :=
  fun x => W (frEmb q x)

/-- Projection of a bank to its first-slot/row-loop cells. -/
def fsbPart {q : Nat} (W : Stack q → List Bool) :
    SourceCSPFirstSlotBridge.Stack q → List Bool :=
  fun x => W (fsbEmb q x)

/-- A bank is *side-blank* when every cell outside the first-row-controller
cells is empty (prefix side work, scratch, and the two truth-frame cells). -/
def SideBlank {q : Nat} (W : Stack q → List Bool) : Prop :=
  ∀ y, (¬ ∃ x, frEmb q x = y) → W y = []

theorem globalBank_sideBlank {q : Nat}
    (S : SourceCSPGlobalDecisionProgram.Stack q → List Bool) :
    SideBlank (bank (globalEmb q) (fun _ => []) S) := by
  intro y hy
  rw [bank_outside]
  rintro ⟨g, rfl⟩
  exact hy ⟨.inl g, rfl⟩

theorem globalBank_fr {q : Nat}
    (S : SourceCSPGlobalDecisionProgram.Stack q → List Bool) :
    frPart (bank (globalEmb q) (fun _ => []) S) =
      Sum.elim S (fun _ => []) := by
  funext x
  cases x with
  | inl g => exact bank_at (globalEmb q) (fun _ => []) S g
  | inr k =>
      change bank (globalEmb q) (fun _ => []) S (frEmb q (.inr k)) = []
      rw [bank_outside]
      rintro ⟨g, hg⟩
      cases hg

theorem sideBlank_frLift {q : Nat} (W : Stack q → List Bool)
    (hW : SideBlank W) (U : SourceCSPFirstRowController.Stack q → List Bool) :
    SideBlank (bank (frEmb q) W U) := by
  intro y hy
  rw [bank_outside _ _ _ y hy]
  exact hW y hy

/-! ## The raw-input verdict controller shape -/

section Top

variable (a q : Nat) {LB VB : Type}

abbrev TopLabel (LB : Type) :=
  BitMachineRawSequence.Label (SourceCSPGlobalDecisionProgram.Label a q) LB

abbrev TopControl (VB : Type) :=
  SourceCSPGlobalDecisionProgram.Control a q × VB

noncomputable def globalLift :
    SourceCSPGlobalDecisionProgram.Label a q →
      TM2.Stmt (fun _ : Stack q => Bool)
        (SourceCSPGlobalDecisionProgram.Label a q)
        (SourceCSPGlobalDecisionProgram.Control a q) :=
  fun l => stackStmt (globalEmb q) (SourceCSPGlobalDecisionProgram.program a q l)

noncomputable def top
    (body : LB → TM2.Stmt (fun _ : Stack q => Bool) LB VB) (b₀ : LB) (w₀ : VB) :
    TopLabel a q LB →
      TM2.Stmt (fun _ : Stack q => Bool) (TopLabel a q LB) (TopControl a q VB)
  | .inl l => BitMachineInline.stmt BitMachineRawSequence.leftLabel
      (fun v => (v, w₀)) Prod.fst (some BitMachineRawSequence.handoff)
      (globalLift a q l)
  | .inr (.inl _) =>
      .branch (fun v => SourceCSPSelectiveStage.acceptedControl v.1)
        (.load (fun _ => (SourceCSPSelectiveStage.globalInitialControl a q, w₀))
          (.goto (fun _ => BitMachineRawSequence.rightLabel b₀)))
        .halt
  | .inr (.inr l) => BitMachineInline.stmt BitMachineRawSequence.rightLabel
      (fun v => (SourceCSPSelectiveStage.globalInitialControl a q, v))
      Prod.snd none (body l)

/-- Raw input in the validator's own initial bank; every other cell empty. -/
noncomputable def topInitial (w₀ : VB) (input : List Bool) :
    TM2.Cfg (fun _ : Stack q => Bool) (TopLabel a q LB) (TopControl a q VB) :=
  BitMachineInline.cfg BitMachineRawSequence.leftLabel
    (fun v => (v, w₀)) (some BitMachineRawSequence.handoff)
    (stackCfg (globalEmb q) (fun _ => [])
      (SourceCSPGlobalDecisionProgram.initial a q input))

variable {a q}

theorem top_global_handoff
    (body : LB → TM2.Stmt (fun _ : Stack q => Bool) LB VB) (b₀ : LB) (w₀ : VB)
    (input : List Bool) (tg : Nat)
    (c : SourceCSPGlobalDecisionProgram.Control a q)
    (S : SourceCSPGlobalDecisionProgram.Stack q → List Bool)
    (hglobal : ((advance (SourceCSPGlobalDecisionProgram.program a q))^[tg])
      (SourceCSPGlobalDecisionProgram.initial a q input) = ⟨none, c, S⟩) :
    ∃ u ≤ tg,
      ((advance (top a q body b₀ w₀))^[u]) (topInitial a q w₀ input) =
        ⟨some BitMachineRawSequence.handoff, (c, w₀),
          bank (globalEmb q) (fun _ => []) S⟩ := by
  have hl := BitMachineStackRun.run (globalEmb q) (fun _ => [])
    (SourceCSPGlobalDecisionProgram.program a q)
    (SourceCSPGlobalDecisionProgram.initial a q input) tg
  rw [hglobal] at hl
  have hhalt : (((advance (globalLift a q))^[tg])
      (stackCfg (globalEmb q) (fun _ => [])
        (SourceCSPGlobalDecisionProgram.initial a q input))).l = none := by
    rw [show globalLift a q = fun l => stackStmt (globalEmb q)
      (SourceCSPGlobalDecisionProgram.program a q l) from rfl, hl]
    rfl
  obtain ⟨u, hu, hrun⟩ := BitMachineInline.outputs
    BitMachineRawSequence.leftLabel (fun v => (v, w₀)) Prod.fst
    (fun _ => rfl) (some BitMachineRawSequence.handoff)
    (globalLift a q) (top a q body b₀ w₀) (fun _ => rfl)
    (stackCfg (globalEmb q) (fun _ => [])
      (SourceCSPGlobalDecisionProgram.initial a q input)) tg hhalt
  refine ⟨u, hu, ?_⟩
  rw [show globalLift a q = fun l => stackStmt (globalEmb q)
      (SourceCSPGlobalDecisionProgram.program a q l) from rfl, hl] at hrun
  exact hrun

theorem top_handoff_nonaccepted
    (body : LB → TM2.Stmt (fun _ : Stack q => Bool) LB VB) (b₀ : LB) (w₀ : VB)
    (c : SourceCSPGlobalDecisionProgram.Control a q) (W : Stack q → List Bool)
    (hc : SourceCSPSelectiveStage.acceptedControl c = false) :
    advance (top a q body b₀ w₀)
      (⟨some BitMachineRawSequence.handoff, (c, w₀), W⟩ :
        TM2.Cfg (fun _ : Stack q => Bool) (TopLabel a q LB) (TopControl a q VB)) =
      ⟨none, (c, w₀), W⟩ := by
  simp [advance, TM2.step, TM2.stepAux, top, BitMachineRawSequence.handoff, hc]

theorem top_handoff_accepted
    (body : LB → TM2.Stmt (fun _ : Stack q => Bool) LB VB) (b₀ : LB) (w₀ : VB)
    (vr : SourceCSPRowLoopController.QueryControl ×
      SourceCSPRowLoopController.ResetControl)
    (W : Stack q → List Bool) :
    advance (top a q body b₀ w₀)
      (⟨some BitMachineRawSequence.handoff,
        ((.row (vr, some true) : SourceCSPGlobalDecisionProgram.Control a q), w₀), W⟩ :
        TM2.Cfg (fun _ : Stack q => Bool) (TopLabel a q LB) (TopControl a q VB)) =
      ⟨some (BitMachineRawSequence.rightLabel b₀),
        (SourceCSPSelectiveStage.globalInitialControl a q, w₀), W⟩ := rfl

/-- Reject and zero: the controller halts in place one step after the
validator's halt, with the validator's terminal bank and every other cell
empty. -/
theorem top_nonaccepted_run
    (body : LB → TM2.Stmt (fun _ : Stack q => Bool) LB VB) (b₀ : LB) (w₀ : VB)
    (input : List Bool) (tg : Nat)
    (c : SourceCSPGlobalDecisionProgram.Control a q)
    (S : SourceCSPGlobalDecisionProgram.Stack q → List Bool)
    (hglobal : ((advance (SourceCSPGlobalDecisionProgram.program a q))^[tg])
      (SourceCSPGlobalDecisionProgram.initial a q input) = ⟨none, c, S⟩)
    (hc : SourceCSPSelectiveStage.acceptedControl c = false) :
    ∃ t ≤ tg + 1,
      ((advance (top a q body b₀ w₀))^[t]) (topInitial a q w₀ input) =
        ⟨none, (c, w₀), bank (globalEmb q) (fun _ => []) S⟩ := by
  obtain ⟨u, hu, hrun⟩ := top_global_handoff body b₀ w₀ input tg c S hglobal
  refine ⟨u + 1, by omega, ?_⟩
  rw [Function.iterate_succ_apply', hrun,
    top_handoff_nonaccepted body b₀ w₀ c _ hc]

/-- Acceptance: the SAME controller continues from the validator's terminal
bank into the body; any actual body run from that bank is inlined. -/
theorem top_accepted_run
    (body : LB → TM2.Stmt (fun _ : Stack q => Bool) LB VB) (b₀ : LB) (w₀ w₁ : VB)
    (input : List Bool) (tg : Nat)
    (vr : SourceCSPRowLoopController.QueryControl ×
      SourceCSPRowLoopController.ResetControl)
    (S : SourceCSPGlobalDecisionProgram.Stack q → List Bool)
    (hglobal : ((advance (SourceCSPGlobalDecisionProgram.program a q))^[tg])
      (SourceCSPGlobalDecisionProgram.initial a q input) =
        ⟨none, .row (vr, some true), S⟩)
    (tb : Nat) (W' : Stack q → List Bool)
    (hbody : ((advance body)^[tb])
      (⟨some b₀, w₀, bank (globalEmb q) (fun _ => []) S⟩ :
        TM2.Cfg (fun _ : Stack q => Bool) LB VB) = ⟨none, w₁, W'⟩) :
    ∃ t ≤ tg + 1 + tb,
      ((advance (top a q body b₀ w₀))^[t]) (topInitial a q w₀ input) =
        ⟨none, (SourceCSPSelectiveStage.globalInitialControl a q, w₁), W'⟩ := by
  obtain ⟨u, hu, hrun⟩ := top_global_handoff body b₀ w₀ input tg _ S hglobal
  let cb : TM2.Cfg (fun _ : Stack q => Bool) LB VB :=
    ⟨some b₀, w₀, bank (globalEmb q) (fun _ => []) S⟩
  have hbh : (((advance body)^[tb]) cb).l = none := by
    change (((advance body)^[tb])
      (⟨some b₀, w₀, bank (globalEmb q) (fun _ => []) S⟩ :
        TM2.Cfg (fun _ : Stack q => Bool) LB VB)).l = none
    rw [hbody]
  obtain ⟨v, hv, hinline⟩ := BitMachineInline.outputs
    BitMachineRawSequence.rightLabel
    (fun w => (SourceCSPSelectiveStage.globalInitialControl a q, w))
    Prod.snd (fun _ => rfl) none body (top a q body b₀ w₀)
    (fun _ => rfl) cb tb hbh
  refine ⟨v + (u + 1), by omega, ?_⟩
  rw [Function.iterate_add_apply, Function.iterate_succ_apply', hrun,
    top_handoff_accepted body b₀ w₀ vr]
  have hstart : BitMachineInline.cfg BitMachineRawSequence.rightLabel
      (fun w => (SourceCSPSelectiveStage.globalInitialControl a q, w))
      none cb =
      (⟨some (BitMachineRawSequence.rightLabel b₀),
        (SourceCSPSelectiveStage.globalInitialControl a q, w₀),
        bank (globalEmb q) (fun _ => []) S⟩ :
        TM2.Cfg (fun _ : Stack q => Bool) (TopLabel a q LB) (TopControl a q VB)) :=
    rfl
  rw [← hstart, hinline]
  change BitMachineInline.cfg BitMachineRawSequence.rightLabel
      (fun w => (SourceCSPSelectiveStage.globalInitialControl a q, w)) none
      (((advance body)^[tb])
        (⟨some b₀, w₀, bank (globalEmb q) (fun _ => []) S⟩ :
          TM2.Cfg (fun _ : Stack q => Bool) LB VB)) = _
  rw [hbody]
  rfl

end Top

#print axioms globalBank_sideBlank
#print axioms globalBank_fr
#print axioms top_global_handoff
#print axioms top_handoff_nonaccepted
#print axioms top_nonaccepted_run
#print axioms top_accepted_run

end EthInapproximability.CurrentPaper.SourceGenericComposite
