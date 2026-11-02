import EthInapproximability.CurrentPaper.SourceClauseCallback
import EthInapproximability.CurrentPaper.SourceClauseRowWriterTruthFlagFrame

namespace EthInapproximability.CurrentPaper.SourceClauseCallback.FalseDispatch

open Turing BitMachineEncoding BitMachineStackEmbedding
open scoped Classical

abbrev Stack (q : ℕ) := SourceClauseRowWriterTruthFrame.Stack q

noncomputable def liftCircuit {q : ℕ}
    (A : SourceClauseCallback.Circuit
      (SourceClauseRowWriterOperands.Stack q)) :
    SourceClauseCallback.Circuit (Stack q) where
  Label := A.Label
  Control := A.Control
  labelsFinite := A.labelsFinite
  controlFinite := A.controlFinite
  program := fun l => stackStmt
    (SourceClauseRowWriterTruthFrame.writerEmbedding (q := q))
    (A.program l)
  start := A.start
  initial := A.initial

theorem lift_run {q : ℕ}
    (A : SourceClauseCallback.Circuit
      (SourceClauseRowWriterOperands.Stack q))
    (S T : SourceClauseRowWriterOperands.Stack q → List Bool)
    (F : Stack q → List Bool)
    (h : SourceClauseCallback.Circuit.Run A S T)
    (hbank : bank SourceClauseRowWriterTruthFrame.writerEmbedding F S = F) :
    SourceClauseCallback.Circuit.Run (liftCircuit A) F
      (bank SourceClauseRowWriterTruthFrame.writerEmbedding F T) := by
  obtain ⟨t, ht⟩ := h
  have he := BitMachineStackRun.run
    (SourceClauseRowWriterTruthFrame.writerEmbedding (q := q)) F
    A.program (⟨some A.start, A.initial, S⟩) t
  have hall (d : DecidableEq (SourceClauseRowWriterOperands.Stack q)) :
      ((@advance _ _ _ d A.program)^[t])
        (⟨some A.start, A.initial, S⟩) =
        ⟨none, A.initial, T⟩ := by
    have hd : d = Classical.decEq _ := Subsingleton.elim _ _
    subst d
    exact ht
  rw [hall] at he
  apply SourceClauseCallback.exists_run_irrel _ _ _ _ _
  refine ⟨t, ?_⟩
  simpa only [liftCircuit, stackCfg, hbank] using he

theorem flagged_writer_bank {q : ℕ}
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r : ℕ) (saved output count remaining : List Bool) (b : Bool) :
    bank SourceClauseRowWriterTruthFrame.writerEmbedding
      (SourceClauseRowWriterTruthFlagFrame.afterFlag row n r
        saved output count b remaining)
      (SourceClauseRowWriterBlank.bank row n r saved output count) =
      SourceClauseRowWriterTruthFlagFrame.afterFlag row n r
        saved output count b remaining := by
  apply bank_eq_self
  intro x
  exact (SourceClauseRowWriterTruthFlagFrame.writer_unchanged
    row n r saved output count b remaining x).symm

theorem flagged_block_run {q : ℕ} (hq : 0 < q)
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r : ℕ) (k : Fin (2 ^ q))
    (saved output count remaining : List Bool) (b : Bool)
    (hquery : ∀ j : Fin q, row (.inl (j, 1)) =
      List.replicate (row (.inl (j, 1))).length true) :
    SourceClauseCallback.Circuit.Run
      (liftCircuit (SourceClauseCallback.blockCircuit k))
      (SourceClauseRowWriterTruthFlagFrame.afterFlag row n r
        saved output count b remaining)
      (bank SourceClauseRowWriterTruthFrame.writerEmbedding
        (SourceClauseRowWriterTruthFlagFrame.afterFlag row n r
          saved output count b remaining)
        (SourceClauseRowWriterBlank.bank row n r
          ((EncodedCNF.clauseFields
            (SourceClauseEncoding.chain (SourceClauseCallback.base n r k)
              (SourceClauseRowSchedule.tupleClause hq k
                (SourceClauseCallback.rowQuery row) false))).reverse ++ saved)
          output (List.replicate (3 * q + 2) true ++ count))) := by
  apply lift_run (SourceClauseCallback.blockCircuit k)
  · exact SourceClauseCallback.block_source_run hq row n r k
      saved output count hquery
  · exact flagged_writer_bank row n r saved output count remaining b

noncomputable def program {q : ℕ} (k : Fin (2 ^ q)) :=
  let B := liftCircuit (SourceClauseCallback.blockCircuit k)
  BitMachineRawSequence.program
    (SourceClauseRowWriterTruthFlagFrame.program k)
    B.program B.start (none : Option Bool) B.initial

theorem false_dispatch_run {q : ℕ} (hq : 0 < q)
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r : ℕ) (k : Fin (2 ^ q))
    (saved output count : List Bool)
    (table : Fin (2 ^ q) → Bool)
    (hrow : row (.inr 2) = true :: List.ofFn table)
    (hfalse : table k = false)
    (hquery : ∀ j : Fin q, row (.inl (j, 1)) =
      List.replicate (row (.inl (j, 1))).length true) :
    ∃ t,
      ((advance (program k))^[t])
        (⟨some (BitMachineRawSequence.leftLabel
          SourceClauseRowTruthBranch.Label.marker),
          ((none : Option Bool),
            (liftCircuit (SourceClauseCallback.blockCircuit k)).initial),
          SourceClauseRowWriterTruthFrame.afterCopy row n r
            saved output count (true :: List.ofFn table)⟩) =
        ⟨none,
          ((none : Option Bool),
            (liftCircuit (SourceClauseCallback.blockCircuit k)).initial),
          bank SourceClauseRowWriterTruthFrame.writerEmbedding
            (SourceClauseRowWriterTruthFlagFrame.afterFlag row n r
              saved output count false
              ((List.ofFn table).drop (k.val + 1)))
            (SourceClauseRowWriterBlank.bank row n r
              ((EncodedCNF.clauseFields
                (SourceClauseEncoding.chain
                  (SourceClauseCallback.base n r k)
                  (SourceClauseRowSchedule.tupleClause hq k
                    (SourceClauseCallback.rowQuery row) false))).reverse ++ saved)
              output (List.replicate (3 * q + 2) true ++ count))⟩ := by
  let B := liftCircuit (SourceClauseCallback.blockCircuit k)
  have hf := SourceClauseRowWriterTruthFlagFrame.run
    k row n r saved output count table hrow
  rw [hfalse] at hf
  obtain ⟨tb, hb⟩ := flagged_block_run hq row n r k
    saved output count ((List.ofFn table).drop (k.val + 1)) false hquery
  obtain ⟨t, _, ht⟩ := BitMachineRawSequence.runs
    (SourceClauseRowWriterTruthFlagFrame.program k)
    B.program
    SourceClauseRowTruthBranch.Label.marker B.start
    (none : Option Bool) (some false)
    B.initial B.initial
    (SourceClauseRowWriterTruthFrame.afterCopy row n r
      saved output count (true :: List.ofFn table))
    (SourceClauseRowWriterTruthFlagFrame.afterFlag row n r
      saved output count false ((List.ofFn table).drop (k.val + 1)))
    (bank SourceClauseRowWriterTruthFrame.writerEmbedding
      (SourceClauseRowWriterTruthFlagFrame.afterFlag row n r
        saved output count false ((List.ofFn table).drop (k.val + 1)))
      (SourceClauseRowWriterBlank.bank row n r
        ((EncodedCNF.clauseFields
          (SourceClauseEncoding.chain (SourceClauseCallback.base n r k)
            (SourceClauseRowSchedule.tupleClause hq k
              (SourceClauseCallback.rowQuery row) false))).reverse ++ saved)
        output (List.replicate (3 * q + 2) true ++ count)))
    (k.val + 3) tb hf hb
  exact ⟨t, ht⟩

/-! The preceding `program` is an unconditional serial composition useful
for transporting the physical flag-run witness.  The following controller
actually tests that flag and enters the rejecting-slot writer only when the
selected bit is false. -/

abbrev ConditionalLabel {q : ℕ} (k : Fin (2 ^ q)) :=
  SourceClauseRowTruthBranch.Label (2 ^ q) ⊕
    (Unit ⊕ (liftCircuit (SourceClauseCallback.blockCircuit k)).Label)

def flagLabel {q : ℕ} (k : Fin (2 ^ q))
    (l : SourceClauseRowTruthBranch.Label (2 ^ q)) :
    ConditionalLabel k := .inl l

def checkLabel {q : ℕ} (k : Fin (2 ^ q)) : ConditionalLabel k :=
  .inr (.inl ())

def blockLabel {q : ℕ} (k : Fin (2 ^ q))
    (l : (liftCircuit (SourceClauseCallback.blockCircuit k)).Label) :
    ConditionalLabel k := .inr (.inr l)

noncomputable def conditionalProgram {q : ℕ} (k : Fin (2 ^ q)) :
    ConditionalLabel k →
      Turing.TM2.Stmt (fun _ : Stack q => Bool) (ConditionalLabel k)
        (Option Bool ×
          (liftCircuit (SourceClauseCallback.blockCircuit k)).Control) :=
  let B := liftCircuit (SourceClauseCallback.blockCircuit k)
  fun
  | .inl l => BitMachineInline.stmt (flagLabel k)
      (fun v => (v, B.initial)) Prod.fst (some (checkLabel k))
      (SourceClauseRowWriterTruthFlagFrame.program k l)
  | .inr (.inl _) =>
      Turing.TM2.Stmt.branch (fun v => v.1 == some false)
        (Turing.TM2.Stmt.load (fun _ => (none, B.initial))
          (Turing.TM2.Stmt.goto (fun _ => blockLabel k B.start)))
        Turing.TM2.Stmt.halt
  | .inr (.inr l) => BitMachineInline.stmt (blockLabel k)
      (fun w => ((none : Option Bool), w)) Prod.snd none
      (B.program l)

theorem check_false_step {q : ℕ} (k : Fin (2 ^ q))
    (S : Stack q → List Bool) :
    advance (conditionalProgram k)
      (⟨some (checkLabel k),
        (some false, (liftCircuit
          (SourceClauseCallback.blockCircuit k)).initial), S⟩) =
      ⟨some (blockLabel k
        (liftCircuit (SourceClauseCallback.blockCircuit k)).start),
        ((none : Option Bool),
          (liftCircuit (SourceClauseCallback.blockCircuit k)).initial), S⟩ := by
  rfl

theorem conditional_false_run {q : ℕ} (hq : 0 < q)
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r : ℕ) (k : Fin (2 ^ q))
    (saved output count : List Bool)
    (table : Fin (2 ^ q) → Bool)
    (hrow : row (.inr 2) = true :: List.ofFn table)
    (hfalse : table k = false)
    (hquery : ∀ j : Fin q, row (.inl (j, 1)) =
      List.replicate (row (.inl (j, 1))).length true) :
    ∃ t,
      ((advance (conditionalProgram k))^[t])
        (⟨some (flagLabel k .marker),
          ((none : Option Bool),
            (liftCircuit (SourceClauseCallback.blockCircuit k)).initial),
          SourceClauseRowWriterTruthFrame.afterCopy row n r
            saved output count (true :: List.ofFn table)⟩) =
        ⟨none,
          ((none : Option Bool),
            (liftCircuit (SourceClauseCallback.blockCircuit k)).initial),
          bank SourceClauseRowWriterTruthFrame.writerEmbedding
            (SourceClauseRowWriterTruthFlagFrame.afterFlag row n r
              saved output count false
              ((List.ofFn table).drop (k.val + 1)))
            (SourceClauseRowWriterBlank.bank row n r
              ((EncodedCNF.clauseFields
                (SourceClauseEncoding.chain
                  (SourceClauseCallback.base n r k)
                  (SourceClauseRowSchedule.tupleClause hq k
                    (SourceClauseCallback.rowQuery row) false))).reverse ++ saved)
              output (List.replicate (3 * q + 2) true ++ count))⟩ := by
  let B := liftCircuit (SourceClauseCallback.blockCircuit k)
  let F := SourceClauseRowWriterTruthFlagFrame.afterFlag row n r
    saved output count false ((List.ofFn table).drop (k.val + 1))
  let U := bank SourceClauseRowWriterTruthFrame.writerEmbedding F
    (SourceClauseRowWriterBlank.bank row n r
      ((EncodedCNF.clauseFields
        (SourceClauseEncoding.chain (SourceClauseCallback.base n r k)
          (SourceClauseRowSchedule.tupleClause hq k
            (SourceClauseCallback.rowQuery row) false))).reverse ++ saved)
      output (List.replicate (3 * q + 2) true ++ count))
  have hf := SourceClauseRowWriterTruthFlagFrame.run
    k row n r saved output count table hrow
  rw [hfalse] at hf
  have hflag := BitMachineInline.outputs
    (flagLabel k) (fun v : Option Bool => (v, B.initial)) Prod.fst
    (fun _ => rfl) (some (checkLabel k))
    (SourceClauseRowWriterTruthFlagFrame.program k)
    (conditionalProgram k)
    (fun l => rfl)
    (⟨some SourceClauseRowTruthBranch.Label.marker, none,
      SourceClauseRowWriterTruthFrame.afterCopy row n r
        saved output count (true :: List.ofFn table)⟩)
    (k.val + 3) (by rw [hf])
  obtain ⟨tf, _, htf⟩ := hflag
  have hblock := flagged_block_run hq row n r k
    saved output count ((List.ofFn table).drop (k.val + 1)) false hquery
  obtain ⟨tb, hb⟩ := hblock
  have hbo := BitMachineInline.outputs
    (blockLabel k) (fun w : B.Control => ((none : Option Bool), w))
    Prod.snd (fun _ => rfl) none B.program (conditionalProgram k)
    (fun l => rfl)
    (⟨some B.start, B.initial, F⟩) tb (by rw [hb])
  obtain ⟨te, _, hte⟩ := hbo
  have htf' :
      ((advance (conditionalProgram k))^[tf])
        (⟨some (flagLabel k .marker),
          ((none : Option Bool), B.initial),
          SourceClauseRowWriterTruthFrame.afterCopy row n r
            saved output count (true :: List.ofFn table)⟩) =
      ⟨some (checkLabel k), (some false, B.initial), F⟩ := by
    simpa only [BitMachineInline.cfg, hf] using htf
  have hbAll (d : DecidableEq (Stack q)) :
      ((@advance _ _ _ d B.program)^[tb])
        (⟨some B.start, B.initial, F⟩) =
        ⟨none, B.initial, U⟩ := by
    have hd : d = Classical.decEq _ := Subsingleton.elim _ _
    subst d
    exact hb
  have hte' :
      ((advance (conditionalProgram k))^[te])
        (⟨some (blockLabel k B.start),
          ((none : Option Bool), B.initial), F⟩) =
      ⟨none, ((none : Option Bool), B.initial), U⟩ := by
    simpa only [BitMachineInline.cfg, hbAll] using hte
  refine ⟨tf + 1 + te, ?_⟩
  rw [show tf + 1 + te = te + (1 + tf) by omega,
    Function.iterate_add_apply,
    show 1 + tf = tf + 1 by omega,
    Function.iterate_succ_apply', htf']
  rw [check_false_step]
  exact hte'

end EthInapproximability.CurrentPaper.SourceClauseCallback.FalseDispatch
