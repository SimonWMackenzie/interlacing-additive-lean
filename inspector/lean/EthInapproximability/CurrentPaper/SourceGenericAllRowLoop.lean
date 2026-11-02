import EthInapproximability.CurrentPaper.SourceGenericRowBridge
import EthInapproximability.CurrentPaper.SourceCSPAllRowLoop

/-! The physical remaining-row counter and the same-bank row callback. -/

namespace EthInapproximability.CurrentPaper.SourceGenericAllRowLoop

open Turing BitMachineEncoding BitMachineStackEmbedding
open scoped Classical

abbrev Stack (q : Nat) := SourceCSPNextRowBridge.Stack q

def headerCount {q : Nat} : Stack q :=
  .inl SourceCSPHeaderRowBridge.count

def remainingCount {q : Nat} : Stack q :=
  .inl SourceCSPHeaderRowBridge.loopCount

def copyScratch {q : Nat} : Stack q := .inr (.inr 0)

def countCopySlots {q : Nat} : Fin 3 ↪ Stack q where
  toFun := ![headerCount, remainingCount, copyScratch]
  inj' := by
    intro x y h
    fin_cases x <;> fin_cases y <;>
      simp [headerCount, remainingCount, copyScratch,
        SourceCSPHeaderRowBridge.count,
        SourceCSPHeaderRowBridge.loopCount] at h ⊢

def countCopyProgram {q : Nat} :=
  fun l => stackStmt (countCopySlots (q := q)) (BitMachineCopy.program l)

noncomputable def copiedCount {q : Nat} (B : Stack q → List Bool)
    (m : Nat) : Stack q → List Bool :=
  Function.update B remainingCount (List.replicate m true)

theorem count_copy_run {q m : Nat} (B : Stack q → List Bool)
    (hheader : B headerCount = List.replicate m true)
    (hremaining : B remainingCount = [])
    (hscratch : B copyScratch = []) :
    ((advance (countCopyProgram (q := q)))^[2 * m + 2])
      (⟨some .scan, none, B⟩ :
        TM2.Cfg (fun _ : Stack q => Bool)
          BitMachineCopy.Label (Option Bool)) =
      ⟨none, none, copiedCount B m⟩ := by
  let C := BitMachineCopy.cfg (some .scan) none
    (List.replicate m true) [] []
  have hbank : bank countCopySlots B C.stk = B := by
    apply bank_eq_self
    intro i
    fin_cases i
    · exact hheader.symm
    · exact hremaining.symm
    · exact hscratch.symm
  have hc : ((advance BitMachineCopy.program)^[2 * m + 2]) C =
      BitMachineCopy.cfg none none (List.replicate m true)
        (List.replicate m true) [] := by
    simpa only [BitMachineCopy.run, List.length_replicate,
      List.append_nil, C] using
        BitMachineCopy.run_correct none (List.replicate m true) []
  have hrun := BitMachineStackRun.run (countCopySlots (q := q)) B
    BitMachineCopy.program C (2 * m + 2)
  rw [hc] at hrun
  have hf : (BitMachineCopy.cfg none none (List.replicate m true)
      (List.replicate m true) []).stk =
      Function.update C.stk 1 (List.replicate m true) := by
    funext i
    fin_cases i <;> rfl
  simp only [stackCfg, hf, bank_update, hbank] at hrun
  simpa only [countCopyProgram, copiedCount, countCopySlots,
    remainingCount] using hrun

def countPopProgram {q : Nat} : Unit →
    TM2.Stmt (fun _ : Stack q => Bool) Unit (Option Bool)
  | () => .pop remainingCount (fun _ b => b) .halt

noncomputable def decremented {q : Nat}
    (B : Stack q → List Bool) (k : Nat) : Stack q → List Bool :=
  Function.update B remainingCount (List.replicate k true)

theorem count_pop_positive {q k : Nat} (B : Stack q → List Bool)
    (hcount : B remainingCount = List.replicate (k + 1) true) :
    advance (countPopProgram (q := q))
      (⟨some (), none, B⟩ :
        TM2.Cfg (fun _ : Stack q => Bool) Unit (Option Bool)) =
      ⟨none, some true, decremented B k⟩ := by
  change B (.inl SourceCSPHeaderRowBridge.loopCount) =
    List.replicate (k + 1) true at hcount
  simp [advance, TM2.step, TM2.stepAux, countPopProgram,
    remainingCount, hcount, decremented, List.replicate_succ]

theorem count_pop_zero {q : Nat} (B : Stack q → List Bool)
    (hcount : B remainingCount = []) :
    advance (countPopProgram (q := q))
      (⟨some (), none, B⟩ :
        TM2.Cfg (fun _ : Stack q => Bool) Unit (Option Bool)) =
      ⟨none, none, B⟩ := by
  change B (.inl SourceCSPHeaderRowBridge.loopCount) = [] at hcount
  simp [advance, TM2.step, TM2.stepAux, countPopProgram,
    remainingCount, hcount]

theorem copy_then_initial_pop {q m : Nat} (B : Stack q → List Bool)
    (hm : 0 < m)
    (hheader : B headerCount = List.replicate m true)
    (hremaining : B remainingCount = [])
    (hscratch : B copyScratch = []) :
    ∃ k, m = k + 1 ∧
      ((advance (countCopyProgram (q := q)))^[2 * m + 2])
        (⟨some .scan, none, B⟩ :
          TM2.Cfg (fun _ : Stack q => Bool)
            BitMachineCopy.Label (Option Bool)) =
        ⟨none, none, copiedCount B m⟩ ∧
      advance (countPopProgram (q := q))
        (⟨some (), none, copiedCount B m⟩ :
          TM2.Cfg (fun _ : Stack q => Bool) Unit (Option Bool)) =
        ⟨none, some true, decremented (copiedCount B m) k⟩ := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
  refine ⟨k, rfl, count_copy_run B hheader hremaining hscratch, ?_⟩
  apply count_pop_positive
  simp [copiedCount, remainingCount]

noncomputable def rowPairCircuit {a q : Nat} (hq : 0 < q) :
    SourceClauseCallback.Circuit (Stack q) := by
  let C := SourceClauseGenericAllSlots.allCircuit (a := a) hq
  letI : Finite C.Label := C.labelsFinite
  letI : Finite C.Control := C.controlFinite
  exact SourceClauseCallback.Circuit.of (SourceGenericRowBridge.rowPairProgram (a := a) hq)
    (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel
        (BitMachineRawSequence.leftLabel
          (BitMachineRawSequence.leftLabel 0))))
    ((((((), none), none), SourceCSPNextRowBridge.parseControlStart),
      ((), ((), none))),
      C.initial)

inductive Label {a q : Nat} (hq : 0 < q) where
  | copy (l : BitMachineCopy.Label)
  | firstPop
  | check
  | take
  | row (l : (rowPairCircuit (a := a) hq).Label)
  | eof
  | accept
  | reject

inductive Control {a q : Nat} (hq : 0 < q) where
  | copy (v : Option Bool)
  | idle (v : Option Bool)
  | row (v : (rowPairCircuit (a := a) hq).Control)
  | done (v : Bool)

def labelCode {a q : Nat} (hq : 0 < q) : Label (a := a) hq →
    BitMachineCopy.Label ⊕ ((rowPairCircuit (a := a) hq).Label ⊕ Fin 6)
  | .copy l => .inl l
  | .firstPop => .inr (.inr 0)
  | .check => .inr (.inr 1)
  | .take => .inr (.inr 2)
  | .row l => .inr (.inl l)
  | .eof => .inr (.inr 3)
  | .accept => .inr (.inr 4)
  | .reject => .inr (.inr 5)

instance {a q : Nat} (hq : 0 < q) : Finite (Label (a := a) hq) := by
  letI : Finite (rowPairCircuit (a := a) hq).Label :=
    (rowPairCircuit (a := a) hq).labelsFinite
  exact Finite.of_injective (labelCode hq) (by
    intro x y h
    cases x <;> cases y <;> simp [labelCode] at h <;> simp_all)

def controlCode {a q : Nat} (hq : 0 < q) : Control (a := a) hq →
    Option Bool ⊕ (Option Bool ⊕ ((rowPairCircuit (a := a) hq).Control ⊕ Bool))
  | .copy v => .inl v
  | .idle v => .inr (.inl v)
  | .row v => .inr (.inr (.inl v))
  | .done v => .inr (.inr (.inr v))

instance {a q : Nat} (hq : 0 < q) : Finite (Control (a := a) hq) := by
  letI : Finite (rowPairCircuit (a := a) hq).Control :=
    (rowPairCircuit (a := a) hq).controlFinite
  exact Finite.of_injective (controlCode hq) (by
    intro x y h
    cases x <;> cases y <;> simp [controlCode] at h <;> simp_all)

noncomputable def rowControl {a q : Nat} (hq : 0 < q)
    (v : (rowPairCircuit (a := a) hq).Control) : Control (a := a) hq := .row v

noncomputable def rowControlGet {a q : Nat} (hq : 0 < q)
    (v : Control (a := a) hq) : (rowPairCircuit (a := a) hq).Control :=
  match v with
  | .row w => w
  | _ => (rowPairCircuit (a := a) hq).initial

def copyControl {a q : Nat} (hq : 0 < q)
    (v : Option Bool) : Control (a := a) hq := .copy v

def copyControlGet {a q : Nat} (hq : 0 < q)
    (v : Control (a := a) hq) : Option Bool :=
  match v with
  | .copy w => w
  | _ => none

def rowSource {q : Nat} : Stack q :=
  SourceCSPNextRowBridge.rowEmbedding (.inr 0)

noncomputable def program {a q : Nat} (hq : 0 < q) :
    Label (a := a) hq → TM2.Stmt (fun _ : Stack q => Bool)
      (Label (a := a) hq) (Control (a := a) hq)
  | .copy l => BitMachineInline.stmt (Label.copy) (copyControl (a := a) hq)
      (copyControlGet hq) (some .firstPop)
      (countCopyProgram l)
  | .firstPop => .pop remainingCount (fun _ b => .idle b)
      (.branch (fun v => match v with
        | .idle (some true) => true
        | _ => false)
        (.goto (fun _ => .check))
        (.goto (fun _ => .reject)))
  | .check => .peek remainingCount (fun _ b => .idle b)
      (.branch (fun v => match v with
        | .idle (some _) => true
        | _ => false)
        (.goto (fun _ => .take))
        (.goto (fun _ => .eof)))
  | .take => .pop remainingCount (fun _ b => .idle b)
      (.branch (fun v => match v with
        | .idle (some true) => true
        | _ => false)
        (.load (fun _ => .row (rowPairCircuit (a := a) hq).initial)
          (.goto (fun _ => .row (rowPairCircuit (a := a) hq).start)))
        (.goto (fun _ => .reject)))
  | .row l => BitMachineInline.stmt (Label.row) (rowControl (a := a) hq)
      (rowControlGet hq) (some .check)
      ((rowPairCircuit (a := a) hq).program l)
  | .eof => .peek rowSource (fun _ b => .idle b)
      (.branch (fun v => match v with
        | .idle (some _) => true
        | _ => false)
        (.goto (fun _ => .reject))
        (.goto (fun _ => .accept)))
  | .accept => .load (fun _ => .done true) .halt
  | .reject => .load (fun _ => .done false) .halt

theorem first_pop_positive {a q k : Nat} (hq : 0 < q)
    (B : Stack q → List Bool)
    (hcount : B remainingCount = List.replicate (k + 1) true) :
    advance (program (a := a) hq)
      (⟨some .firstPop, .copy none, B⟩ :
        TM2.Cfg (fun _ : Stack q => Bool) (Label (a := a) hq) (Control (a := a) hq)) =
      ⟨some .check, .idle (some true), decremented B k⟩ := by
  change B (.inl SourceCSPHeaderRowBridge.loopCount) =
    List.replicate (k + 1) true at hcount
  simp [advance, TM2.step, TM2.stepAux, program,
    remainingCount, hcount, decremented, List.replicate_succ]

theorem check_positive {a q k : Nat} (hq : 0 < q)
    (v : Control (a := a) hq)
    (B : Stack q → List Bool)
    (hcount : B remainingCount = List.replicate (k + 1) true) :
    advance (program (a := a) hq)
      (⟨some .check, v, B⟩ :
        TM2.Cfg (fun _ : Stack q => Bool) (Label (a := a) hq) (Control (a := a) hq)) =
      ⟨some .take, .idle (some true), B⟩ := by
  change B (.inl SourceCSPHeaderRowBridge.loopCount) =
    List.replicate (k + 1) true at hcount
  simp [advance, TM2.step, TM2.stepAux, program,
    remainingCount, hcount, List.replicate_succ]

theorem check_zero {a q : Nat} (hq : 0 < q)
    (v : Control (a := a) hq)
    (B : Stack q → List Bool)
    (hcount : B remainingCount = []) :
    advance (program (a := a) hq)
      (⟨some .check, v, B⟩ :
        TM2.Cfg (fun _ : Stack q => Bool) (Label (a := a) hq) (Control (a := a) hq)) =
      ⟨some .eof, .idle none, B⟩ := by
  change B (.inl SourceCSPHeaderRowBridge.loopCount) = [] at hcount
  simp [advance, TM2.step, TM2.stepAux, program,
    remainingCount, hcount]

theorem take_positive {a q k : Nat} (hq : 0 < q)
    (B : Stack q → List Bool)
    (hcount : B remainingCount = List.replicate (k + 1) true) :
    advance (program (a := a) hq)
      (⟨some .take, .idle (some true), B⟩ :
        TM2.Cfg (fun _ : Stack q => Bool) (Label (a := a) hq) (Control (a := a) hq)) =
      ⟨some (.row (rowPairCircuit (a := a) hq).start),
        .row (rowPairCircuit (a := a) hq).initial, decremented B k⟩ := by
  change B (.inl SourceCSPHeaderRowBridge.loopCount) =
    List.replicate (k + 1) true at hcount
  simp [advance, TM2.step, TM2.stepAux, program,
    remainingCount, hcount, decremented, List.replicate_succ]

theorem eof_empty {a q : Nat} (hq : 0 < q)
    (B : Stack q → List Bool)
    (hsource : B rowSource = []) :
    advance (program (a := a) hq)
      (⟨some .eof, .idle none, B⟩ :
        TM2.Cfg (fun _ : Stack q => Bool) (Label (a := a) hq) (Control (a := a) hq)) =
      ⟨some .accept, .idle none, B⟩ := by
  change B (SourceCSPNextRowBridge.rowEmbedding (.inr 0)) = [] at hsource
  simp [advance, TM2.step, TM2.stepAux, program,
    rowSource, hsource]

theorem accept_step {a q : Nat} (hq : 0 < q)
    (B : Stack q → List Bool) :
    advance (program (a := a) hq)
      (⟨some .accept, .idle none, B⟩ :
        TM2.Cfg (fun _ : Stack q => Bool) (Label (a := a) hq) (Control (a := a) hq)) =
      ⟨none, .done true, B⟩ := by
  rfl

theorem copy_handoff {a q m : Nat} (hq : 0 < q)
    (B : Stack q → List Bool)
    (hheader : B headerCount = List.replicate m true)
    (hremaining : B remainingCount = [])
    (hscratch : B copyScratch = []) :
    ∃ t ≤ 2 * m + 2,
      ((advance (program (a := a) hq))^[t])
        (⟨some (.copy .scan), .copy none, B⟩ :
          TM2.Cfg (fun _ : Stack q => Bool) (Label (a := a) hq) (Control (a := a) hq)) =
        ⟨some .firstPop, .copy none, copiedCount B m⟩ := by
  have hc := count_copy_run B hheader hremaining hscratch
  have hh : (((advance (countCopyProgram (q := q)))^[2 * m + 2])
      (⟨some .scan, none, B⟩ :
        TM2.Cfg (fun _ : Stack q => Bool)
          BitMachineCopy.Label (Option Bool))).l = none := by
    rw [hc]
  obtain ⟨t, ht, hrun⟩ := BitMachineInline.outputs
    Label.copy (copyControl (a := a) hq) (copyControlGet hq)
    (by intro v; rfl) (some Label.firstPop)
    (countCopyProgram (q := q)) (program (a := a) hq) (by intro l; rfl)
    (⟨some .scan, none, B⟩ :
      TM2.Cfg (fun _ : Stack q => Bool)
        BitMachineCopy.Label (Option Bool))
    (2 * m + 2) hh
  rw [hc] at hrun
  refine ⟨t, ht, ?_⟩
  simpa only [BitMachineInline.cfg, copyControl] using hrun

theorem row_handoff {a q : Nat} (hq : 0 < q)
    (B T : Stack q → List Bool) (t : Nat)
    (hrun : ((advance (rowPairCircuit (a := a) hq).program)^[t])
      (⟨some (rowPairCircuit (a := a) hq).start,
        (rowPairCircuit (a := a) hq).initial, B⟩ :
        TM2.Cfg (fun _ : Stack q => Bool)
          (rowPairCircuit (a := a) hq).Label (rowPairCircuit (a := a) hq).Control) =
      ⟨none, (rowPairCircuit (a := a) hq).initial, T⟩) :
    ∃ u ≤ t,
      ((advance (program (a := a) hq))^[u])
        (⟨some (.row (rowPairCircuit (a := a) hq).start),
          .row (rowPairCircuit (a := a) hq).initial, B⟩ :
          TM2.Cfg (fun _ : Stack q => Bool) (Label (a := a) hq) (Control (a := a) hq)) =
        ⟨some .check, .row (rowPairCircuit (a := a) hq).initial, T⟩ := by
  let C := rowPairCircuit (a := a) hq
  have hh : (((advance C.program)^[t])
      (⟨some C.start, C.initial, B⟩ :
        TM2.Cfg (fun _ : Stack q => Bool) C.Label C.Control)).l = none := by
    rw [hrun]
  obtain ⟨u, hu, he⟩ := BitMachineInline.outputs
    Label.row (rowControl (a := a) hq) (rowControlGet hq)
    (by intro v; rfl) (some Label.check)
    C.program (program (a := a) hq) (by intro l; rfl)
    (⟨some C.start, C.initial, B⟩ :
      TM2.Cfg (fun _ : Stack q => Bool) C.Label C.Control) t hh
  rw [hrun] at he
  refine ⟨u, hu, ?_⟩
  simpa only [BitMachineInline.cfg, rowControl] using he

def remainingRows {n M a q : Nat}
    (rows : Fin M → SourceCSPCodec.Row n a q)
    (r k : Nat) (h : r + 1 + k ≤ M) :
    Fin k → SourceCSPCodec.Row n a q :=
  fun j => rows ⟨r + 1 + j.val, by omega⟩

noncomputable def rowClauses {n M a q : Nat}
    (rows : Fin M → SourceCSPCodec.Row n a q)
    (hq : 0 < q) (i : Fin M) : List EncodedCNF.Clause :=
  (List.ofFn fun z : Fin (a ^ q) =>
    SourceGenericOrder.rowChain
      (SourceCSPCodec.fromRows n M a q rows).system hq i z).flatten

noncomputable def suffixClauses {n M a q : Nat}
    (rows : Fin M → SourceCSPCodec.Row n a q)
    (hq : 0 < q) (r k : Nat) (h : r + 1 + k ≤ M) :
    List EncodedCNF.Clause :=
  (List.ofFn (fun j : Fin k =>
    rowClauses rows hq ⟨r + 1 + j.val, by omega⟩)).flatten

private theorem clauseFields_append (xs ys : List EncodedCNF.Clause) :
    EncodedCNF.clauseFields (xs ++ ys) =
      EncodedCNF.clauseFields xs ++ EncodedCNF.clauseFields ys := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.cons_append,
      EncodedCNF.clauseFields, ih, List.append_assoc]

theorem remainingRows_head {n M a q k r : Nat}
    (rows : Fin M → SourceCSPCodec.Row n a q)
    (h : r + 1 + (k + 1) ≤ M) :
    remainingRows rows r (k + 1) h 0 =
      rows ⟨r + 1, by omega⟩ := rfl

theorem remainingRows_tail {n M a q k r : Nat}
    (rows : Fin M → SourceCSPCodec.Row n a q)
    (h : r + 1 + (k + 1) ≤ M) :
    (fun j : Fin k => remainingRows rows r (k + 1) h j.succ) =
      remainingRows rows (r + 1) k (by omega) := by
  funext j
  apply congrArg rows
  apply Fin.ext
  dsimp [remainingRows]
  omega

theorem suffixClauses_succ {n M a q k r : Nat}
    (rows : Fin M → SourceCSPCodec.Row n a q) (hq : 0 < q)
    (h : r + 1 + (k + 1) ≤ M) :
    suffixClauses rows hq r (k + 1) h =
      rowClauses rows hq ⟨r + 1, by omega⟩ ++
        suffixClauses rows hq (r + 1) k (by omega) := by
  simp only [suffixClauses, List.ofFn_succ, List.flatten_cons]
  congr 1
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext j
  congr 1
  apply Fin.ext
  change r + 1 + j.succ.val = r + 1 + 1 + j.val
  simp only [Fin.val_succ]
  omega

noncomputable def withRemaining {q : Nat}
    (S : SourceCSPGlobalDecisionProgram.Stack q → List Bool)
    (k : Nat) : SourceCSPGlobalDecisionProgram.Stack q → List Bool :=
  Function.update S SourceCSPHeaderRowBridge.loopCount
    (List.replicate k true)

theorem decrement_callback_bank {q n r k : Nat}
    (S : SourceCSPGlobalDecisionProgram.Stack q → List Bool)
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (saved output count : List Bool) :
    decremented
      (SourceCSPNextRowBridge.callbackBank S row n r
        saved output count) k =
      SourceCSPNextRowBridge.callbackBank
        (withRemaining S k) row n r saved output count := by
  funext x
  cases x with
  | inl g =>
      by_cases h : g = SourceCSPHeaderRowBridge.loopCount
      · subst g
        simp [decremented, withRemaining,
          SourceCSPNextRowBridge.callbackBank, remainingCount]
      · simp [decremented, withRemaining,
          SourceCSPNextRowBridge.callbackBank, remainingCount,
          Function.update_of_ne, h]
  | inr y =>
      simp [decremented, withRemaining,
        SourceCSPNextRowBridge.callbackBank, remainingCount]

theorem withRemaining_zero_idempotent {q k : Nat}
    (S : SourceCSPGlobalDecisionProgram.Stack q → List Bool) :
    withRemaining (withRemaining S k) 0 = withRemaining S 0 := by
  simp [withRemaining, Function.update_idem]

theorem withRemaining_overwrite {q a b : Nat}
    (S : SourceCSPGlobalDecisionProgram.Stack q → List Bool) :
    withRemaining (withRemaining S a) b = withRemaining S b := by
  simp [withRemaining, Function.update_idem]

/-- The fixed controller consumes precisely the typed remaining rows, runs
the physical row-pair callback for each, and takes the zero-count plus
literal-EOF branch. `saved` and `count` may already contain any prefix. -/
theorem loop_from_check {n M a q : Nat}
    (rows : Fin M → SourceCSPCodec.Row n a q) (hq : 0 < q)
    (L : Nat) (hn : 0 < n)
    (hword : ∀ i : Fin M, ∀ j : Fin q,
      ((rows i).1 j).val.bits.length ≤ L)
    (hcapL : n - 1 ≤ L)
    (r k : Nat) (hbound : r + 1 + k = M)
    (S : SourceCSPGlobalDecisionProgram.Stack q → List Bool)
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (saved output count : List Bool) (v : Control (a := a) hq)
    (hcount : S SourceCSPHeaderRowBridge.loopCount =
      List.replicate k true)
    (hcap : S SourceCSPHeaderRowBridge.capSource =
      List.replicate (n - 1) true)
    (hsource : row (.inr 0) = SourceCSPCodec.fnFields
      SourceCSPCodec.rowFields
        (remainingRows rows r k (by omega))) :
    let clauses := suffixClauses rows hq r k (by omega)
    ∃ (t : Nat) (lastRow : SourceCSPRowQueryFrame.Stack q → List Bool),
      ((advance (program (a := a) hq))^[t])
        (⟨some .check, v,
          SourceCSPNextRowBridge.callbackBank S row n r
            saved output count⟩ :
          TM2.Cfg (fun _ : Stack q => Bool) (Label (a := a) hq) (Control (a := a) hq)) =
        ⟨none, .done true,
          SourceCSPNextRowBridge.callbackBank (withRemaining S 0)
            lastRow n (M - 1)
            ((EncodedCNF.clauseFields clauses).reverse ++ saved)
          output (List.replicate clauses.length true ++ count)⟩ ∧
      lastRow (.inr 0) = [] := by
  induction k generalizing r S row saved output count v with
  | zero =>
      let B := SourceCSPNextRowBridge.callbackBank S row n r
        saved output count
      have hc : B remainingCount = [] := by
        change S SourceCSPHeaderRowBridge.loopCount = []
        simpa using hcount
      have hs : B rowSource = [] := by
        change SourceCSPNextRowBridge.callbackBank S row n r
          saved output count
          (SourceCSPNextRowBridge.rowEmbedding (.inr 0)) = []
        rw [SourceCSPNextRowBridge.callback_bank_row]
        simpa [SourceCSPCodec.fnFields_zero] using hsource
      have hrun : ((advance (program (a := a) hq))^[3])
          (⟨some .check, v, B⟩ :
            TM2.Cfg (fun _ : Stack q => Bool) (Label (a := a) hq) (Control (a := a) hq)) =
          ⟨none, .done true, B⟩ := by
        change advance (program (a := a) hq)
          (advance (program (a := a) hq)
            (advance (program (a := a) hq)
              (⟨some .check, v, B⟩ :
                TM2.Cfg (fun _ : Stack q => Bool)
                  (Label (a := a) hq) (Control (a := a) hq)))) = _
        rw [check_zero (a := a) hq v B hc, eof_empty (a := a) hq B hs, accept_step]
      have hS : withRemaining S 0 = S := by
        funext g
        by_cases hg : g = SourceCSPHeaderRowBridge.loopCount
        · subst g
          simpa [withRemaining] using hcount.symm
        · simp [withRemaining, Function.update_of_ne hg]
      have hr : r = M - 1 := by omega
      refine ⟨3, row, ?_, ?_⟩
      · simpa only [suffixClauses, List.ofFn_zero, List.flatten_nil,
          EncodedCNF.clauseFields, List.reverse_nil,
          List.nil_append, List.length_nil, List.replicate_zero,
          hS, hr, B] using hrun
      · simpa [SourceCSPCodec.fnFields_zero] using hsource
  | succ k ih =>
      let rem := remainingRows rows r (k + 1) (by omega)
      let next : Fin M := ⟨r + 1, by omega⟩
      let S1 := withRemaining S k
      let B := SourceCSPNextRowBridge.callbackBank S row n r
        saved output count
      let B1 := SourceCSPNextRowBridge.callbackBank S1 row n r
        saved output count
      have hcB : B remainingCount = List.replicate (k + 1) true := by
        exact hcount
      have htwo : ((advance (program (a := a) hq))^[2])
          (⟨some .check, v, B⟩ :
            TM2.Cfg (fun _ : Stack q => Bool)
              (Label (a := a) hq) (Control (a := a) hq)) =
          ⟨some (.row (rowPairCircuit (a := a) hq).start),
            .row (rowPairCircuit (a := a) hq).initial, B1⟩ := by
        change advance (program (a := a) hq)
          (advance (program (a := a) hq)
            (⟨some .check, v, B⟩ :
              TM2.Cfg (fun _ : Stack q => Bool)
                (Label (a := a) hq) (Control (a := a) hq))) = _
        rw [check_positive (a := a) hq v B hcB,
          take_positive (a := a) hq B hcB,
          decrement_callback_bank]
      have hcap1 : S1 SourceCSPHeaderRowBridge.capSource =
          List.replicate (n - 1) true := by
        have hne : SourceCSPHeaderRowBridge.capSource (q := q) ≠
            SourceCSPHeaderRowBridge.loopCount (q := q) := by
          simp [SourceCSPHeaderRowBridge.capSource,
            SourceCSPHeaderRowBridge.loopCount]
        change Function.update S SourceCSPHeaderRowBridge.loopCount
          (List.replicate k true) SourceCSPHeaderRowBridge.capSource = _
        rw [Function.update_of_ne hne]
        exact hcap
      have hrem : row (.inr 0) =
          SourceCSPCodec.fnFields SourceCSPCodec.rowFields rem :=
        hsource
      obtain ⟨tp, V, htp, hpair, htail⟩ := SourceGenericRowBridge.row_pair_run
        rows rem next r L S1 row saved output count hq hn
        (by rfl) (by exact (remainingRows_head rows (by omega)).symm)
        hrem hcap1 (hword next) hcapL
      let headClauses := rowClauses rows hq next
      let saved1 := (EncodedCNF.clauseFields headClauses).reverse ++ saved
      let count1 := List.replicate headClauses.length true ++ count
      let B2 := SourceCSPNextRowBridge.callbackBank S1 V n (r + 1)
        saved1 output count1
      have hpair' : ((advance (rowPairCircuit (a := a) hq).program)^[tp])
          (⟨some (rowPairCircuit (a := a) hq).start,
            (rowPairCircuit (a := a) hq).initial, B1⟩ :
            TM2.Cfg (fun _ : Stack q => Bool)
              (rowPairCircuit (a := a) hq).Label
              (rowPairCircuit (a := a) hq).Control) =
          ⟨none, (rowPairCircuit (a := a) hq).initial, B2⟩ := by
        simpa only [rowPairCircuit, headClauses, saved1,
          count1, B1, B2] using hpair
      obtain ⟨up, hup, hrowHandoff⟩ :=
        row_handoff (a := a) hq B1 B2 tp hpair'
      have hcount1 : S1 SourceCSPHeaderRowBridge.loopCount =
          List.replicate k true := by
        simp [S1, withRemaining]
      have hsource1 : V (.inr 0) = SourceCSPCodec.fnFields
          SourceCSPCodec.rowFields
            (remainingRows rows (r + 1) k (by omega)) := by
        rw [remainingRows_tail] at htail
        exact htail
      obtain ⟨ut, lastRow, htailRun, hfinalSource⟩ :=
        ih (r + 1) (by omega) S1 V saved1 output count1
          (.row (rowPairCircuit (a := a) hq).initial)
          hcount1 hcap1 hsource1
      have hseq : ((advance (program (a := a) hq))^[ut + up + 2])
          (⟨some .check, v, B⟩ :
            TM2.Cfg (fun _ : Stack q => Bool)
              (Label (a := a) hq) (Control (a := a) hq)) =
          ⟨none, .done true,
            SourceCSPNextRowBridge.callbackBank (withRemaining S1 0)
              lastRow n (M - 1)
              ((EncodedCNF.clauseFields
                (suffixClauses rows hq (r + 1) k (by omega))).reverse ++
                saved1)
              output
              (List.replicate
                (suffixClauses rows hq (r + 1) k (by omega)).length true ++
                count1)⟩ := by
        rw [show ut + up + 2 = ut + (up + 2) by omega,
          Function.iterate_add_apply,
          show up + 2 = up + 2 by rfl,
          Function.iterate_add_apply, htwo, hrowHandoff]
        exact htailRun
      refine ⟨ut + up + 2, lastRow, ?_, hfinalSource⟩
      have hcountorder :
          List.replicate
              (suffixClauses rows hq (r + 1) k (by omega)).length true ++
            List.replicate headClauses.length true =
          List.replicate headClauses.length true ++
            List.replicate
              (suffixClauses rows hq (r + 1) k (by omega)).length true := by
        rw [← List.replicate_add, ← List.replicate_add,
          Nat.add_comm]
      rw [show withRemaining S1 0 = withRemaining S 0 from
        withRemaining_zero_idempotent S] at hseq
      dsimp only [count1, saved1] at hseq
      simp only [← List.append_assoc] at hseq
      rw [hcountorder] at hseq
      rw [suffixClauses_succ, clauseFields_append,
        List.reverse_append, List.length_append,
        List.replicate_add]
      simpa only [saved1, count1, List.append_assoc] using hseq

/-- After the first row has already been emitted, physically copy the
validated header's unary `m` into the exhausted validator loop counter,
consume one mark for that first row, and run the checked row loop. The
starting clause payload and count are whatever the first callback left. -/
theorem all_remaining_after_first {n m a q : Nat}
    (rows : Fin m → SourceCSPCodec.Row n a q) (hq : 0 < q)
    (L : Nat) (hn : 0 < n) (hm : 0 < m)
    (hword : ∀ i : Fin m, ∀ j : Fin q,
      ((rows i).1 j).val.bits.length ≤ L)
    (hcapL : n - 1 ≤ L)
    (S : SourceCSPGlobalDecisionProgram.Stack q → List Bool)
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (saved output count : List Bool)
    (hheader : S SourceCSPHeaderRowBridge.count =
      List.replicate m true)
    (hvalidatorDone : S SourceCSPHeaderRowBridge.loopCount = [])
    (hcap : S SourceCSPHeaderRowBridge.capSource =
      List.replicate (n - 1) true)
    (hsource : row (.inr 0) = SourceCSPCodec.fnFields
      SourceCSPCodec.rowFields
        (remainingRows rows 0 (m - 1) (by omega))) :
    let clauses := suffixClauses rows hq 0 (m - 1) (by omega)
    ∃ (tcopy tloop t : Nat)
      (lastRow : SourceCSPRowQueryFrame.Stack q → List Bool),
      tcopy ≤ 2 * m + 2 ∧ t = tcopy + 1 + tloop ∧
      ((advance (program (a := a) hq))^[t])
        (⟨some (.copy .scan), .copy none,
          SourceCSPNextRowBridge.callbackBank S row n 0
            saved output count⟩ :
          TM2.Cfg (fun _ : Stack q => Bool) (Label (a := a) hq) (Control (a := a) hq)) =
        ⟨none, .done true,
          SourceCSPNextRowBridge.callbackBank (withRemaining S 0)
            lastRow n (m - 1)
            ((EncodedCNF.clauseFields clauses).reverse ++ saved)
            output (List.replicate clauses.length true ++ count)⟩ ∧
      lastRow (.inr 0) = [] ∧
      (withRemaining S 0) SourceCSPHeaderRowBridge.count =
        List.replicate m true := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
  let B := SourceCSPNextRowBridge.callbackBank S row n 0
    saved output count
  let S1 := withRemaining S k
  have hheaderB : B headerCount = List.replicate (k + 1) true :=
    hheader
  have hcountB : B remainingCount = [] := hvalidatorDone
  have hscratchB : B copyScratch = [] := rfl
  obtain ⟨tc, htc, hcopy⟩ := copy_handoff (a := a) hq B
    hheaderB hcountB hscratchB
  have hcCopy : copiedCount B (k + 1) remainingCount =
      List.replicate (k + 1) true := by
    simp [copiedCount]
  have hpop := first_pop_positive (a := a) hq (copiedCount B (k + 1))
    hcCopy
  have hbank : decremented (copiedCount B (k + 1)) k =
      SourceCSPNextRowBridge.callbackBank S1 row n 0
        saved output count := by
    change decremented (decremented B (k + 1)) k = _
    rw [decrement_callback_bank, decrement_callback_bank,
      withRemaining_overwrite]
  rw [hbank] at hpop
  have hcount1 : S1 SourceCSPHeaderRowBridge.loopCount =
      List.replicate k true := by
    simp [S1, withRemaining]
  have hcap1 : S1 SourceCSPHeaderRowBridge.capSource =
      List.replicate (n - 1) true := by
    have hne : SourceCSPHeaderRowBridge.capSource (q := q) ≠
        SourceCSPHeaderRowBridge.loopCount (q := q) := by
      simp [SourceCSPHeaderRowBridge.capSource,
        SourceCSPHeaderRowBridge.loopCount]
    change Function.update S SourceCSPHeaderRowBridge.loopCount
      (List.replicate k true) SourceCSPHeaderRowBridge.capSource = _
    rw [Function.update_of_ne hne]
    exact hcap
  obtain ⟨tl, lastRow, hloop, hfinalSource⟩ :=
    loop_from_check (a := a) rows hq L hn hword hcapL
      0 k (by omega) S1 row saved output count
      (.idle (some true)) hcount1 hcap1 hsource
  refine ⟨tc, tl, tc + 1 + tl, lastRow, htc, rfl, ?_, hfinalSource, ?_⟩
  have hrun : ((advance (program (a := a) hq))^[tc + 1 + tl])
      (⟨some (.copy .scan), .copy none, B⟩ :
        TM2.Cfg (fun _ : Stack q => Bool) (Label (a := a) hq) (Control (a := a) hq)) =
      ⟨none, .done true,
        SourceCSPNextRowBridge.callbackBank (withRemaining S1 0)
          lastRow n (k + 1 - 1)
          ((EncodedCNF.clauseFields
            (suffixClauses rows hq 0 k (by omega))).reverse ++ saved)
          output
          (List.replicate
            (suffixClauses rows hq 0 k (by omega)).length true ++ count)⟩ := by
    rw [show tc + 1 + tl = tl + (1 + tc) by omega,
      Function.iterate_add_apply,
      show 1 + tc = 1 + tc by rfl,
      Function.iterate_add_apply, hcopy]
    change ((advance (program (a := a) hq))^[tl])
      (advance (program (a := a) hq)
        (⟨some .firstPop, .copy none, copiedCount B (k + 1)⟩)) = _
    rw [hpop]
    exact hloop
  rw [show withRemaining S1 0 = withRemaining S 0 from
    withRemaining_zero_idempotent S] at hrun
  simpa only [B] using hrun
  have hne : SourceCSPHeaderRowBridge.count (q := q) ≠
      SourceCSPHeaderRowBridge.loopCount (q := q) := by
    simp [SourceCSPHeaderRowBridge.count,
      SourceCSPHeaderRowBridge.loopCount]
  change Function.update S SourceCSPHeaderRowBridge.loopCount []
    SourceCSPHeaderRowBridge.count = _
  rw [Function.update_of_ne hne]
  exact hheader

#print axioms loop_from_check
#print axioms all_remaining_after_first

end EthInapproximability.CurrentPaper.SourceGenericAllRowLoop
