import EthInapproximability.CurrentPaper.SourceGenericPayloadIdentity

/-!
# Converter bank, generic copy/clear subroutines and verdict controller

Paper B, locked v8 Section 6 and Appendix B; CP-SOURCE-EFFECTIVE, arbitrary
fixed alphabet `a`.

`CStack q` extends the segment-2 bank by fresh cells: the complete bank of
the admitted `SourceClauseCountFinalize` machine (counter and finalizer) and
three header/scratch cells. `topC` is the raw-input verdict controller shape
of `SourceCSPFirstRowController.program` on this bank (the same definition as
`SourceGenericComposite.top`, with the validator lifted into `CStack q`).
-/

namespace EthInapproximability.CurrentPaper.SourceGenericComposite.Converter

open Turing BitMachineEncoding BitMachineStackEmbedding
open scoped Classical

abbrev Extra := SourceClauseCountFinalize.Stack ⊕ Fin 3

abbrev CStack (q : Nat) := SourceGenericComposite.Stack q ⊕ Extra

def mainEmb (q : Nat) : SourceGenericComposite.Stack q ↪ CStack q :=
  Function.Embedding.inl

def globalEmbC (q : Nat) : SourceCSPGlobalDecisionProgram.Stack q ↪ CStack q :=
  (globalEmb q).trans (mainEmb q)

/-! ## Named cells -/

def outCell (q : Nat) : CStack q :=
  globalEmbC q SourceCSPGlobalDecisionProgram.outputSlot
def countGCell (q : Nat) : CStack q :=
  globalEmbC q SourceCSPHeaderRowBridge.count
def vertexCell (q : Nat) : CStack q :=
  mainEmb q (fsbEmb q (.inr (.inl SourceClauseRowWriterOperands.vertex)))
def savedCellC (q : Nat) : CStack q :=
  mainEmb q (fsbEmb q (.inr (.inl SourceClauseRowWriterCleanup.savedCell)))
def countCellC (q : Nat) : CStack q :=
  mainEmb q (fsbEmb q (.inr (.inl SourceClauseRowWriterCleanup.countCell)))
def h0 (q : Nat) : CStack q := .inr (.inr 0)
def h1 (q : Nat) : CStack q := .inr (.inr 1)
def scr (q : Nat) : CStack q := .inr (.inr 2)

/-- The finalizer's cells: its output cell is the validator's output slot;
all others are fresh. -/
noncomputable def finMap (q : Nat) (k : SourceClauseCountFinalize.Stack) : CStack q :=
  if k = .inl 3 then outCell q else .inr (.inl k)

noncomputable def finEmb (q : Nat) : SourceClauseCountFinalize.Stack ↪ CStack q where
  toFun := finMap q
  inj' := by
    intro x y h
    by_cases hx : x = .inl 3 <;> by_cases hy : y = .inl 3
    · rw [hx, hy]
    · simp [finMap, hx, hy, outCell, globalEmbC, mainEmb] at h
    · simp [finMap, hx, hy, outCell, globalEmbC, mainEmb] at h
    · simpa [finMap, hx, hy] using h

theorem finEmb_out (q : Nat) : finEmb q (.inl 3) = outCell q := by
  simp [finEmb, finMap]

theorem finEmb_other (q : Nat) (k : SourceClauseCountFinalize.Stack)
    (hk : k ≠ .inl 3) : finEmb q k = .inr (.inl k) := by
  simp [finEmb, finMap, hk]

def fin0 (q : Nat) : CStack q := .inr (.inl (.inl 0))
def fin1 (q : Nat) : CStack q := .inr (.inl (.inl 1))
def fuel (q : Nat) : CStack q := .inr (.inl (.inr (.inr 0)))

/-- Header scanner cells: two consumed unary inputs, then the finalizer's
variable-count cell. -/
def hdrEmb (q : Nat) : Fin 3 ↪ CStack q where
  toFun k := if k = 0 then h0 q else if k = 1 then h1 q else fin0 q
  inj' := by
    intro x y h
    fin_cases x <;> fin_cases y <;> simp_all [h0, h1, fin0]

/-! ## Generic three-cell copy and one-cell clear -/

section Generic

variable {J : Type} [DecidableEq J]

noncomputable def copySlots (src dst tmp : J)
    (hs : src ≠ dst) (hx : src ≠ tmp) (hy : dst ≠ tmp) : Fin 3 ↪ J where
  toFun
    | 0 => src
    | 1 => dst
    | 2 => tmp
  inj' := by
    intro i j h
    fin_cases i <;> fin_cases j <;>
      simp_all [Ne.symm hy]

noncomputable def copyProgram (src dst tmp : J)
    (hs : src ≠ dst) (hx : src ≠ tmp) (hy : dst ≠ tmp) :=
  fun l => stackStmt (copySlots src dst tmp hs hx hy) (BitMachineCopy.program l)

theorem copy_run (src dst tmp : J)
    (hs : src ≠ dst) (hx : src ≠ tmp) (hy : dst ≠ tmp)
    (B : J → List Bool) (word : List Bool)
    (hsrc : B src = word) (hdst : B dst = []) (hw : B tmp = []) :
    ((advance (copyProgram src dst tmp hs hx hy))^[2*word.length+2])
      (⟨some .scan, none, B⟩ : TM2.Cfg (fun _ : J => Bool) _ _) =
      ⟨none, none, Function.update B dst word⟩ := by
  let C := BitMachineCopy.cfg (some .scan) none word [] []
  have hbank : bank (copySlots src dst tmp hs hx hy) B C.stk = B := by
    apply bank_eq_self
    intro i
    fin_cases i
    · exact hsrc.symm
    · exact hdst.symm
    · exact hw.symm
  have hc : ((advance BitMachineCopy.program)^[2*word.length+2]) C =
      BitMachineCopy.cfg none none word word [] := by
    simpa [C, BitMachineCopy.run] using
      BitMachineCopy.run_correct none word []
  have he := BitMachineStackRun.run (copySlots src dst tmp hs hx hy) B
    BitMachineCopy.program C (2*word.length+2)
  rw [hc] at he
  have hf : (BitMachineCopy.cfg none none word word []).stk =
      Function.update C.stk 1 word := by
    funext i
    fin_cases i <;> rfl
  simp only [stackCfg, hf, bank_update, hbank] at he
  simpa only [copyProgram, copySlots] using he

def clearProgram (cell : J) :
    Fin 2 → TM2.Stmt (fun _ : J => Bool) (Fin 2) (Unit × Option Bool)
  | 0 => BitMachineClearBank.clearStep cell 0 1
  | 1 => .halt

theorem clear_run (cell : J) (B : J → List Bool) :
    ((advance (clearProgram cell))^[(B cell).length + 2])
      (⟨some 0, ((), none), B⟩ :
        TM2.Cfg (fun _ : J => Bool) (Fin 2) (Unit × Option Bool)) =
      ⟨none, ((), none), Function.update B cell []⟩ := by
  have h := BitMachineClearBank.clear_one_run
    (clearProgram cell) cell 0 1 rfl () B
  rw [show (B cell).length + 2 = (B cell).length + 1 + 1 by omega,
    Function.iterate_succ_apply', h]
  rfl

end Generic

/-! ## Verdict controller on the converter bank -/

section Top

variable (a q : Nat) {LB VB : Type}

abbrev TopLabel (LB : Type) :=
  BitMachineRawSequence.Label (SourceCSPGlobalDecisionProgram.Label a q) LB

abbrev TopControl (VB : Type) :=
  SourceCSPGlobalDecisionProgram.Control a q × VB

noncomputable def globalLift :
    SourceCSPGlobalDecisionProgram.Label a q →
      TM2.Stmt (fun _ : CStack q => Bool)
        (SourceCSPGlobalDecisionProgram.Label a q)
        (SourceCSPGlobalDecisionProgram.Control a q) :=
  fun l => stackStmt (globalEmbC q) (SourceCSPGlobalDecisionProgram.program a q l)

noncomputable def topC
    (body : LB → TM2.Stmt (fun _ : CStack q => Bool) LB VB) (b₀ : LB) (w₀ : VB) :
    TopLabel a q LB →
      TM2.Stmt (fun _ : CStack q => Bool) (TopLabel a q LB) (TopControl a q VB)
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

/-- Raw input in the validator's initial bank; every other cell empty. -/
noncomputable def topCInitial (w₀ : VB) (input : List Bool) :
    TM2.Cfg (fun _ : CStack q => Bool) (TopLabel a q LB) (TopControl a q VB) :=
  BitMachineInline.cfg BitMachineRawSequence.leftLabel
    (fun v => (v, w₀)) (some BitMachineRawSequence.handoff)
    (stackCfg (globalEmbC q) (fun _ => [])
      (SourceCSPGlobalDecisionProgram.initial a q input))

variable {a q}

theorem topC_global_handoff
    (body : LB → TM2.Stmt (fun _ : CStack q => Bool) LB VB) (b₀ : LB) (w₀ : VB)
    (input : List Bool) (tg : Nat)
    (c : SourceCSPGlobalDecisionProgram.Control a q)
    (S : SourceCSPGlobalDecisionProgram.Stack q → List Bool)
    (hglobal : ((advance (SourceCSPGlobalDecisionProgram.program a q))^[tg])
      (SourceCSPGlobalDecisionProgram.initial a q input) = ⟨none, c, S⟩) :
    ∃ u ≤ tg,
      ((advance (topC a q body b₀ w₀))^[u]) (topCInitial a q w₀ input) =
        ⟨some BitMachineRawSequence.handoff, (c, w₀),
          bank (globalEmbC q) (fun _ => []) S⟩ := by
  have hl := BitMachineStackRun.run (globalEmbC q) (fun _ => [])
    (SourceCSPGlobalDecisionProgram.program a q)
    (SourceCSPGlobalDecisionProgram.initial a q input) tg
  rw [hglobal] at hl
  have hhalt : (((advance (globalLift a q))^[tg])
      (stackCfg (globalEmbC q) (fun _ => [])
        (SourceCSPGlobalDecisionProgram.initial a q input))).l = none := by
    rw [show globalLift a q = fun l => stackStmt (globalEmbC q)
      (SourceCSPGlobalDecisionProgram.program a q l) from rfl, hl]
    rfl
  obtain ⟨u, hu, hrun⟩ := BitMachineInline.outputs
    BitMachineRawSequence.leftLabel (fun v => (v, w₀)) Prod.fst
    (fun _ => rfl) (some BitMachineRawSequence.handoff)
    (globalLift a q) (topC a q body b₀ w₀) (fun _ => rfl)
    (stackCfg (globalEmbC q) (fun _ => [])
      (SourceCSPGlobalDecisionProgram.initial a q input)) tg hhalt
  refine ⟨u, hu, ?_⟩
  rw [show globalLift a q = fun l => stackStmt (globalEmbC q)
      (SourceCSPGlobalDecisionProgram.program a q l) from rfl, hl] at hrun
  exact hrun

theorem topC_handoff_nonaccepted
    (body : LB → TM2.Stmt (fun _ : CStack q => Bool) LB VB) (b₀ : LB) (w₀ : VB)
    (c : SourceCSPGlobalDecisionProgram.Control a q) (W : CStack q → List Bool)
    (hc : SourceCSPSelectiveStage.acceptedControl c = false) :
    advance (topC a q body b₀ w₀)
      (⟨some BitMachineRawSequence.handoff, (c, w₀), W⟩ :
        TM2.Cfg (fun _ : CStack q => Bool) (TopLabel a q LB) (TopControl a q VB)) =
      ⟨none, (c, w₀), W⟩ := by
  simp [advance, TM2.step, TM2.stepAux, topC, BitMachineRawSequence.handoff, hc]

theorem topC_handoff_accepted
    (body : LB → TM2.Stmt (fun _ : CStack q => Bool) LB VB) (b₀ : LB) (w₀ : VB)
    (vr : SourceCSPRowLoopController.QueryControl ×
      SourceCSPRowLoopController.ResetControl)
    (W : CStack q → List Bool) :
    advance (topC a q body b₀ w₀)
      (⟨some BitMachineRawSequence.handoff,
        ((.row (vr, some true) : SourceCSPGlobalDecisionProgram.Control a q), w₀), W⟩ :
        TM2.Cfg (fun _ : CStack q => Bool) (TopLabel a q LB) (TopControl a q VB)) =
      ⟨some (BitMachineRawSequence.rightLabel b₀),
        (SourceCSPSelectiveStage.globalInitialControl a q, w₀), W⟩ := rfl

theorem topC_nonaccepted_run
    (body : LB → TM2.Stmt (fun _ : CStack q => Bool) LB VB) (b₀ : LB) (w₀ : VB)
    (input : List Bool) (tg : Nat)
    (c : SourceCSPGlobalDecisionProgram.Control a q)
    (S : SourceCSPGlobalDecisionProgram.Stack q → List Bool)
    (hglobal : ((advance (SourceCSPGlobalDecisionProgram.program a q))^[tg])
      (SourceCSPGlobalDecisionProgram.initial a q input) = ⟨none, c, S⟩)
    (hc : SourceCSPSelectiveStage.acceptedControl c = false) :
    ∃ t ≤ tg + 1,
      ((advance (topC a q body b₀ w₀))^[t]) (topCInitial a q w₀ input) =
        ⟨none, (c, w₀), bank (globalEmbC q) (fun _ => []) S⟩ := by
  obtain ⟨u, hu, hrun⟩ := topC_global_handoff body b₀ w₀ input tg c S hglobal
  refine ⟨u + 1, by omega, ?_⟩
  rw [Function.iterate_succ_apply', hrun,
    topC_handoff_nonaccepted body b₀ w₀ c _ hc]

theorem topC_accepted_run
    (body : LB → TM2.Stmt (fun _ : CStack q => Bool) LB VB) (b₀ : LB) (w₀ w₁ : VB)
    (input : List Bool) (tg : Nat)
    (vr : SourceCSPRowLoopController.QueryControl ×
      SourceCSPRowLoopController.ResetControl)
    (S : SourceCSPGlobalDecisionProgram.Stack q → List Bool)
    (hglobal : ((advance (SourceCSPGlobalDecisionProgram.program a q))^[tg])
      (SourceCSPGlobalDecisionProgram.initial a q input) =
        ⟨none, .row (vr, some true), S⟩)
    (tb : Nat) (W' : CStack q → List Bool)
    (hbody : ((advance body)^[tb])
      (⟨some b₀, w₀, bank (globalEmbC q) (fun _ => []) S⟩ :
        TM2.Cfg (fun _ : CStack q => Bool) LB VB) = ⟨none, w₁, W'⟩) :
    ∃ t ≤ tg + 1 + tb,
      ((advance (topC a q body b₀ w₀))^[t]) (topCInitial a q w₀ input) =
        ⟨none, (SourceCSPSelectiveStage.globalInitialControl a q, w₁), W'⟩ := by
  obtain ⟨u, hu, hrun⟩ := topC_global_handoff body b₀ w₀ input tg _ S hglobal
  let cb : TM2.Cfg (fun _ : CStack q => Bool) LB VB :=
    ⟨some b₀, w₀, bank (globalEmbC q) (fun _ => []) S⟩
  have hbh : (((advance body)^[tb]) cb).l = none := by
    change (((advance body)^[tb])
      (⟨some b₀, w₀, bank (globalEmbC q) (fun _ => []) S⟩ :
        TM2.Cfg (fun _ : CStack q => Bool) LB VB)).l = none
    rw [hbody]
  obtain ⟨v, hv, hinline⟩ := BitMachineInline.outputs
    BitMachineRawSequence.rightLabel
    (fun w => (SourceCSPSelectiveStage.globalInitialControl a q, w))
    Prod.snd (fun _ => rfl) none body (topC a q body b₀ w₀)
    (fun _ => rfl) cb tb hbh
  refine ⟨v + (u + 1), by omega, ?_⟩
  rw [Function.iterate_add_apply, Function.iterate_succ_apply', hrun,
    topC_handoff_accepted body b₀ w₀ vr]
  have hstart : BitMachineInline.cfg BitMachineRawSequence.rightLabel
      (fun w => (SourceCSPSelectiveStage.globalInitialControl a q, w))
      none cb =
      (⟨some (BitMachineRawSequence.rightLabel b₀),
        (SourceCSPSelectiveStage.globalInitialControl a q, w₀),
        bank (globalEmbC q) (fun _ => []) S⟩ :
        TM2.Cfg (fun _ : CStack q => Bool) (TopLabel a q LB) (TopControl a q VB)) :=
    rfl
  rw [← hstart, hinline]
  change BitMachineInline.cfg BitMachineRawSequence.rightLabel
      (fun w => (SourceCSPSelectiveStage.globalInitialControl a q, w)) none
      (((advance body)^[tb])
        (⟨some b₀, w₀, bank (globalEmbC q) (fun _ => []) S⟩ :
          TM2.Cfg (fun _ : CStack q => Bool) LB VB)) = _
  rw [hbody]
  rfl

end Top

/-- The converter's start bank is the segment-2 start bank with every fresh
cell empty. -/
theorem globalBankC_eq {q : Nat}
    (S : SourceCSPGlobalDecisionProgram.Stack q → List Bool) :
    bank (globalEmbC q) (fun _ => []) S =
      bank (mainEmb q) (fun _ => []) (FirstRow.globalBank S) := by
  funext y
  rcases y with x | e
  · rw [show (Sum.inl x : CStack q) = mainEmb q x from rfl, bank_at]
    unfold FirstRow.globalBank
    by_cases h : ∃ g, globalEmb q g = x
    · obtain ⟨g, rfl⟩ := h
      rw [bank_at]
      exact bank_at (globalEmbC q) (fun _ => []) S g
    · rw [bank_outside _ _ _ _ h, bank_outside]
      rintro ⟨g, hg⟩
      exact h ⟨g, Sum.inl.inj hg⟩
  · rw [bank_outside, bank_outside]
    · rintro ⟨x, hx⟩; cases hx
    · rintro ⟨g, hg⟩; cases hg

#print axioms finEmb
#print axioms copy_run
#print axioms clear_run
#print axioms topC_nonaccepted_run
#print axioms topC_accepted_run
#print axioms globalBankC_eq

end EthInapproximability.CurrentPaper.SourceGenericComposite.Converter
