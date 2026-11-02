import EthInapproximability.CurrentPaper.SourceClauseFalseDispatch
import EthInapproximability.CurrentPaper.SourceClauseGenericTrue
import EthInapproximability.CurrentPaper.SourceClauseGenericCallback
import EthInapproximability.CurrentPaper.SourceClauseFalseDispatch

/-! Physical choice between both source-labelled Boolean CSP tuple clauses.
The accepted position is not skipped: it emits the source's tautological
`q+1`-literal chain. -/

namespace EthInapproximability.CurrentPaper.SourceClauseGenericDual

open Turing BitMachineEncoding BitMachineStackEmbedding
open SourceClauseCallback
open scoped Classical

abbrev Stack (q : ℕ) := SourceClauseRowWriterTruthFrame.Stack q

noncomputable def falseCircuit {a q : ℕ} (k : Fin (a ^ q)) :=
  FalseDispatch.liftCircuit (SourceClauseGenericCallback.blockCircuit k)

noncomputable def trueCircuit {a q : ℕ} (hq : 0 < q)
    (k : Fin (a ^ q)) :=
  FalseDispatch.liftCircuit (SourceClauseGenericTrue.blockCircuit hq k)

abbrev Label {a q : ℕ} (hq : 0 < q) (k : Fin (a ^ q)) :=
  SourceClauseRowTruthBranch.Label (a ^ q) ⊕
    (Unit ⊕ ((falseCircuit k).Label ⊕ (trueCircuit hq k).Label))

def flagLabel {a q : ℕ} (hq : 0 < q) (k : Fin (a ^ q))
    (l : SourceClauseRowTruthBranch.Label (a ^ q)) : Label hq k :=
  .inl l

def checkLabel {a q : ℕ} (hq : 0 < q) (k : Fin (a ^ q)) :
    Label hq k := .inr (.inl ())

def falseLabel {a q : ℕ} (hq : 0 < q) (k : Fin (a ^ q))
    (l : (falseCircuit k).Label) : Label hq k :=
  .inr (.inr (.inl l))

def trueLabel {a q : ℕ} (hq : 0 < q) (k : Fin (a ^ q))
    (l : (trueCircuit hq k).Label) : Label hq k :=
  .inr (.inr (.inr l))

noncomputable def program {a q : ℕ} (hq : 0 < q) (k : Fin (a ^ q)) :
    Label hq k → Turing.TM2.Stmt (fun _ : Stack q => Bool)
      (Label hq k)
      ((Option Bool × (falseCircuit k).Control) ×
        (trueCircuit hq k).Control) :=
  let Bf := falseCircuit k
  let Bt := trueCircuit hq k
  fun
  | .inl l => BitMachineInline.stmt (flagLabel hq k)
      (fun v => ((v, Bf.initial), Bt.initial))
      (fun v => v.1.1) (some (checkLabel hq k))
      (SourceClauseRowWriterTruthFlagFrame.program k l)
  | .inr (.inl _) =>
      Turing.TM2.Stmt.branch (fun v => v.1.1 == some false)
        (Turing.TM2.Stmt.load
          (fun _ => (((none : Option Bool), Bf.initial), Bt.initial))
          (Turing.TM2.Stmt.goto
            (fun _ => falseLabel hq k Bf.start)))
        (Turing.TM2.Stmt.load
          (fun _ => (((none : Option Bool), Bf.initial), Bt.initial))
          (Turing.TM2.Stmt.goto
            (fun _ => trueLabel hq k Bt.start)))
  | .inr (.inr (.inl l)) => BitMachineInline.stmt (falseLabel hq k)
      (fun w => (((none : Option Bool), w), Bt.initial))
      (fun v => v.1.2) none (Bf.program l)
  | .inr (.inr (.inr l)) => BitMachineInline.stmt (trueLabel hq k)
      (fun w => (((none : Option Bool), Bf.initial), w))
      (fun v => v.2) none (Bt.program l)

theorem check_false {a q : ℕ} (hq : 0 < q) (k : Fin (a ^ q))
    (S : Stack q → List Bool) :
    advance (program hq k)
      (⟨some (checkLabel hq k),
        ((some false, (falseCircuit k).initial),
          (trueCircuit hq k).initial), S⟩) =
      ⟨some (falseLabel hq k (falseCircuit k).start),
        (((none : Option Bool), (falseCircuit k).initial),
          (trueCircuit hq k).initial), S⟩ := rfl

theorem check_true {a q : ℕ} (hq : 0 < q) (k : Fin (a ^ q))
    (S : Stack q → List Bool) :
    advance (program hq k)
      (⟨some (checkLabel hq k),
        ((some true, (falseCircuit k).initial),
          (trueCircuit hq k).initial), S⟩) =
      ⟨some (trueLabel hq k (trueCircuit hq k).start),
        (((none : Option Bool), (falseCircuit k).initial),
          (trueCircuit hq k).initial), S⟩ := rfl

theorem flag_phase {a q : ℕ} (hq : 0 < q)
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r : ℕ) (k : Fin (a ^ q))
    (saved output count : List Bool)
    (table : Fin (a ^ q) → Bool)
    (hrow : row (.inr 2) = true :: List.ofFn table) :
    ∃ tf ≤ k.val + 3,
      ((advance (program hq k))^[tf])
        (⟨some (flagLabel hq k .marker),
          (((none : Option Bool), (falseCircuit k).initial),
            (trueCircuit hq k).initial),
          SourceClauseRowWriterTruthFrame.afterCopy row n r
            saved output count (true :: List.ofFn table)⟩) =
        ⟨some (checkLabel hq k),
          ((some (table k), (falseCircuit k).initial),
            (trueCircuit hq k).initial),
          SourceClauseRowWriterTruthFlagFrame.afterFlag row n r
            saved output count (table k)
            ((List.ofFn table).drop (k.val + 1))⟩ := by
  let Bf := falseCircuit k
  let Bt := trueCircuit hq k
  have hf := SourceClauseRowWriterTruthFlagFrame.run
    k row n r saved output count table hrow
  have ho := BitMachineInline.outputs
    (flagLabel hq k)
    (fun v : Option Bool => ((v, Bf.initial), Bt.initial))
    (fun v => v.1.1) (fun _ => rfl)
    (some (checkLabel hq k))
    (SourceClauseRowWriterTruthFlagFrame.program k)
    (program hq k) (fun l => rfl)
    (⟨some SourceClauseRowTruthBranch.Label.marker, none,
      SourceClauseRowWriterTruthFrame.afterCopy row n r
        saved output count (true :: List.ofFn table)⟩)
    (k.val + 3) (by rw [hf])
  obtain ⟨tf, htf, hr⟩ := ho
  refine ⟨tf, htf, ?_⟩
  simpa only [BitMachineInline.cfg, hf] using hr

theorem true_framed_run {a q : ℕ} (hq : 0 < q)
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r : ℕ) (k : Fin (a ^ q))
    (saved output count remaining : List Bool)
    (hquery : ∀ j : Fin q, row (.inl (j, 1)) =
      List.replicate (row (.inl (j, 1))).length true) :
    SourceClauseCallback.Circuit.Run (trueCircuit hq k)
      (SourceClauseRowWriterTruthFlagFrame.afterFlag row n r
        saved output count true remaining)
      (bank SourceClauseRowWriterTruthFrame.writerEmbedding
        (SourceClauseRowWriterTruthFlagFrame.afterFlag row n r
          saved output count true remaining)
        (SourceClauseRowWriterBlank.bank row n r
          ((EncodedCNF.clauseFields
            (SourceClauseEncoding.chain (SourceClauseGenericCallback.base n r k)
              (SourceClauseRowSchedule.tupleClause hq k
                (SourceClauseCallback.rowQuery row) true))).reverse ++ saved)
          output (List.replicate (3 * q + 5) true ++ count))) := by
  apply FalseDispatch.lift_run (SourceClauseGenericTrue.blockCircuit hq k)
  · exact SourceClauseGenericTrue.block_source_run hq row n r k
      saved output count hquery
  · exact FalseDispatch.flagged_writer_bank row n r
      saved output count remaining true

theorem false_framed_run {a q : ℕ} (hq : 0 < q)
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r : ℕ) (k : Fin (a ^ q))
    (saved output count remaining : List Bool)
    (hquery : ∀ j : Fin q, row (.inl (j, 1)) =
      List.replicate (row (.inl (j, 1))).length true) :
    SourceClauseCallback.Circuit.Run (falseCircuit k)
      (SourceClauseRowWriterTruthFlagFrame.afterFlag row n r
        saved output count false remaining)
      (bank SourceClauseRowWriterTruthFrame.writerEmbedding
        (SourceClauseRowWriterTruthFlagFrame.afterFlag row n r
          saved output count false remaining)
        (SourceClauseRowWriterBlank.bank row n r
          ((EncodedCNF.clauseFields
            (SourceClauseEncoding.chain (SourceClauseGenericCallback.base n r k)
              (SourceClauseRowSchedule.tupleClause hq k
                (SourceClauseCallback.rowQuery row) false))).reverse ++ saved)
          output (List.replicate (3 * q + 2) true ++ count))) := by
  apply FalseDispatch.lift_run (SourceClauseGenericCallback.blockCircuit k)
  · exact SourceClauseGenericCallback.block_source_run hq row n r k
      saved output count hquery
  · exact FalseDispatch.flagged_writer_bank row n r
      saved output count remaining false

def clauseCount (q : ℕ) (b : Bool) : ℕ :=
  if b then 3 * q + 5 else 3 * q + 2

noncomputable def finalBank {a q : ℕ} (hq : 0 < q)
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r : ℕ) (k : Fin (a ^ q))
    (saved output count remaining : List Bool) (b : Bool) :
    Stack q → List Bool :=
  bank SourceClauseRowWriterTruthFrame.writerEmbedding
    (SourceClauseRowWriterTruthFlagFrame.afterFlag row n r
      saved output count b remaining)
    (SourceClauseRowWriterBlank.bank row n r
      ((EncodedCNF.clauseFields
        (SourceClauseEncoding.chain (SourceClauseGenericCallback.base n r k)
          (SourceClauseRowSchedule.tupleClause hq k
            (SourceClauseCallback.rowQuery row) b))).reverse ++ saved)
      output (List.replicate (clauseCount q b) true ++ count))

theorem false_run {a q : ℕ} (hq : 0 < q)
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r : ℕ) (k : Fin (a ^ q))
    (saved output count : List Bool)
    (table : Fin (a ^ q) → Bool)
    (hrow : row (.inr 2) = true :: List.ofFn table)
    (hfalse : table k = false)
    (hquery : ∀ j : Fin q, row (.inl (j, 1)) =
      List.replicate (row (.inl (j, 1))).length true) :
    ∃ t,
      ((advance (program hq k))^[t])
        (⟨some (flagLabel hq k .marker),
          (((none : Option Bool), (falseCircuit k).initial),
            (trueCircuit hq k).initial),
          SourceClauseRowWriterTruthFrame.afterCopy row n r
            saved output count (true :: List.ofFn table)⟩) =
        ⟨none,
          (((none : Option Bool), (falseCircuit k).initial),
            (trueCircuit hq k).initial),
          finalBank hq row n r k saved output count
            ((List.ofFn table).drop (k.val + 1)) false⟩ := by
  let Bf := falseCircuit k
  let Bt := trueCircuit hq k
  let F := SourceClauseRowWriterTruthFlagFrame.afterFlag row n r
    saved output count false ((List.ofFn table).drop (k.val + 1))
  let U := finalBank hq row n r k saved output count
    ((List.ofFn table).drop (k.val + 1)) false
  obtain ⟨tf, _, htf⟩ := flag_phase hq row n r k
    saved output count table hrow
  rw [hfalse] at htf
  obtain ⟨tb, hb⟩ := false_framed_run hq row n r k
    saved output count ((List.ofFn table).drop (k.val + 1)) hquery
  have hh :
      ((advance Bf.program)^[tb])
        (⟨some Bf.start, Bf.initial, F⟩) =
        ⟨none, Bf.initial, U⟩ := by
    simpa [Bf, F, U, finalBank, clauseCount] using hb
  have hbo := BitMachineInline.outputs
    (falseLabel hq k)
    (fun w : Bf.Control => (((none : Option Bool), w), Bt.initial))
    (fun v => v.1.2) (fun _ => rfl)
    none Bf.program (program hq k) (fun l => rfl)
    (⟨some Bf.start, Bf.initial, F⟩) tb (by rw [hh])
  obtain ⟨te, _, hte⟩ := hbo
  have hbAll (d : DecidableEq (Stack q)) :
      ((@advance _ _ _ d Bf.program)^[tb])
        (⟨some Bf.start, Bf.initial, F⟩) =
        ⟨none, Bf.initial, U⟩ := by
    have hd : d = Classical.decEq _ := Subsingleton.elim _ _
    subst d
    exact hh
  have hte' :
      ((advance (program hq k))^[te])
        (⟨some (falseLabel hq k Bf.start),
          (((none : Option Bool), Bf.initial), Bt.initial), F⟩) =
      ⟨none, (((none : Option Bool), Bf.initial), Bt.initial), U⟩ := by
    simpa only [BitMachineInline.cfg, hbAll] using hte
  refine ⟨tf + 1 + te, ?_⟩
  rw [show tf + 1 + te = te + (1 + tf) by omega,
    Function.iterate_add_apply,
    show 1 + tf = tf + 1 by omega,
    Function.iterate_succ_apply', htf]
  rw [check_false]
  exact hte'

theorem true_run {a q : ℕ} (hq : 0 < q)
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r : ℕ) (k : Fin (a ^ q))
    (saved output count : List Bool)
    (table : Fin (a ^ q) → Bool)
    (hrow : row (.inr 2) = true :: List.ofFn table)
    (htrue : table k = true)
    (hquery : ∀ j : Fin q, row (.inl (j, 1)) =
      List.replicate (row (.inl (j, 1))).length true) :
    ∃ t,
      ((advance (program hq k))^[t])
        (⟨some (flagLabel hq k .marker),
          (((none : Option Bool), (falseCircuit k).initial),
            (trueCircuit hq k).initial),
          SourceClauseRowWriterTruthFrame.afterCopy row n r
            saved output count (true :: List.ofFn table)⟩) =
        ⟨none,
          (((none : Option Bool), (falseCircuit k).initial),
            (trueCircuit hq k).initial),
          finalBank hq row n r k saved output count
            ((List.ofFn table).drop (k.val + 1)) true⟩ := by
  let Bf := falseCircuit k
  let Bt := trueCircuit hq k
  let F := SourceClauseRowWriterTruthFlagFrame.afterFlag row n r
    saved output count true ((List.ofFn table).drop (k.val + 1))
  let U := finalBank hq row n r k saved output count
    ((List.ofFn table).drop (k.val + 1)) true
  obtain ⟨tf, _, htf⟩ := flag_phase hq row n r k
    saved output count table hrow
  rw [htrue] at htf
  obtain ⟨tb, hb⟩ := true_framed_run hq row n r k
    saved output count ((List.ofFn table).drop (k.val + 1)) hquery
  have hh :
      ((advance Bt.program)^[tb])
        (⟨some Bt.start, Bt.initial, F⟩) =
        ⟨none, Bt.initial, U⟩ := by
    simpa [Bt, F, U, finalBank, clauseCount] using hb
  have hbo := BitMachineInline.outputs
    (trueLabel hq k)
    (fun w : Bt.Control => (((none : Option Bool), Bf.initial), w))
    (fun v => v.2) (fun _ => rfl)
    none Bt.program (program hq k) (fun l => rfl)
    (⟨some Bt.start, Bt.initial, F⟩) tb (by rw [hh])
  obtain ⟨te, _, hte⟩ := hbo
  have hbAll (d : DecidableEq (Stack q)) :
      ((@advance _ _ _ d Bt.program)^[tb])
        (⟨some Bt.start, Bt.initial, F⟩) =
        ⟨none, Bt.initial, U⟩ := by
    have hd : d = Classical.decEq _ := Subsingleton.elim _ _
    subst d
    exact hh
  have hte' :
      ((advance (program hq k))^[te])
        (⟨some (trueLabel hq k Bt.start),
          (((none : Option Bool), Bf.initial), Bt.initial), F⟩) =
      ⟨none, (((none : Option Bool), Bf.initial), Bt.initial), U⟩ := by
    simpa only [BitMachineInline.cfg, hbAll] using hte
  refine ⟨tf + 1 + te, ?_⟩
  rw [show tf + 1 + te = te + (1 + tf) by omega,
    Function.iterate_add_apply,
    show 1 + tf = tf + 1 by omega,
    Function.iterate_succ_apply', htf]
  rw [check_true]
  exact hte'

/-- For either truth bit, one finite-control program selects and physically
emits exactly the corresponding source-labelled chain on the same writer bank.
This theorem is not yet an aggregate clock bound or iteration over slots. -/
theorem selected_run {a q : ℕ} (hq : 0 < q)
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r : ℕ) (k : Fin (a ^ q))
    (saved output count : List Bool)
    (table : Fin (a ^ q) → Bool)
    (hrow : row (.inr 2) = true :: List.ofFn table)
    (hquery : ∀ j : Fin q, row (.inl (j, 1)) =
      List.replicate (row (.inl (j, 1))).length true) :
    ∃ t,
      ((advance (program hq k))^[t])
        (⟨some (flagLabel hq k .marker),
          (((none : Option Bool), (falseCircuit k).initial),
            (trueCircuit hq k).initial),
          SourceClauseRowWriterTruthFrame.afterCopy row n r
            saved output count (true :: List.ofFn table)⟩) =
        ⟨none,
          (((none : Option Bool), (falseCircuit k).initial),
            (trueCircuit hq k).initial),
          finalBank hq row n r k saved output count
            ((List.ofFn table).drop (k.val + 1)) (table k)⟩ := by
  cases h : table k with
  | false =>
      simpa only [h] using
        (false_run hq row n r k saved output count table hrow h hquery)
  | true =>
      simpa only [h] using
        (true_run hq row n r k saved output count table hrow h hquery)

noncomputable def fullProgram {a q : ℕ} (hq : 0 < q)
    (k : Fin (a ^ q)) :=
  BitMachineRawSequence.program
    (SourceClauseRowWriterTruthFrame.copyProgram (q := q))
    (program hq k) (flagLabel hq k .marker)
    (none : Option Bool)
    ((((none : Option Bool), (falseCircuit k).initial),
      (trueCircuit hq k).initial))

/-- Starts with the checked row's truth word on its own stack; the program
physically copies and scans it, then chooses the matching source clause
block.  The only row premises are the actual encoded truth word and unary
query words.  The result is one selected slot, not a loop over all slots. -/
theorem selected_full_run {a q : ℕ} (hq : 0 < q)
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r : ℕ) (k : Fin (a ^ q))
    (saved output count : List Bool)
    (table : Fin (a ^ q) → Bool)
    (hrow : row (.inr 2) = true :: List.ofFn table)
    (hquery : ∀ j : Fin q, row (.inl (j, 1)) =
      List.replicate (row (.inl (j, 1))).length true) :
    ∃ t,
      ((advance (fullProgram hq k))^[t])
        (⟨some (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan),
          ((none : Option Bool),
            (((none : Option Bool), (falseCircuit k).initial),
              (trueCircuit hq k).initial)),
          SourceClauseRowWriterTruthFrame.initial row n r
            saved output count⟩) =
        ⟨none,
          ((none : Option Bool),
            (((none : Option Bool), (falseCircuit k).initial),
              (trueCircuit hq k).initial)),
          finalBank hq row n r k saved output count
            ((List.ofFn table).drop (k.val + 1)) (table k)⟩ := by
  have hc := SourceClauseRowWriterTruthFrame.copy_run row n r
    saved output count (true :: List.ofFn table) hrow
  obtain ⟨td, hd⟩ := selected_run hq row n r k
    saved output count table hrow hquery
  obtain ⟨t, _, ht⟩ := BitMachineRawSequence.runs
    (SourceClauseRowWriterTruthFrame.copyProgram (q := q))
    (program hq k)
    BitMachineCopy.Label.scan (flagLabel hq k .marker)
    (none : Option Bool) (none : Option Bool)
    ((((none : Option Bool), (falseCircuit k).initial),
      (trueCircuit hq k).initial))
    ((((none : Option Bool), (falseCircuit k).initial),
      (trueCircuit hq k).initial))
    (SourceClauseRowWriterTruthFrame.initial row n r saved output count)
    (SourceClauseRowWriterTruthFrame.afterCopy row n r saved output count
      (true :: List.ofFn table))
    (finalBank hq row n r k saved output count
      ((List.ofFn table).drop (k.val + 1)) (table k))
    (2 * (true :: List.ofFn table).length + 2) td hc hd
  exact ⟨t, ht⟩

end EthInapproximability.CurrentPaper.SourceClauseGenericDual
