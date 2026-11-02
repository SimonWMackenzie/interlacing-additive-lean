import EthInapproximability.CurrentPaper.SourceClauseGenericReset

/-! Fixed-q finite-control sequencing of every Boolean truth-table slot. -/

namespace EthInapproximability.CurrentPaper.SourceClauseGenericAllSlots

open Turing BitMachineEncoding
open scoped Classical
open SourceClauseCallback SourceClauseRowSchedule SourceClauseEncoding

abbrev Stack (q : ℕ) := SourceClauseRowWriterTruthFrame.Stack q

noncomputable def fullCircuit {a q : ℕ} (hq : 0 < q)
    (k : Fin (a ^ q)) : Circuit (Stack q) := by
  let Bf := SourceClauseGenericDual.falseCircuit k
  let Bt := SourceClauseGenericDual.trueCircuit hq k
  letI := Bf.labelsFinite
  letI := Bt.labelsFinite
  letI := Bf.controlFinite
  letI := Bt.controlFinite
  exact Circuit.of (SourceClauseGenericDual.fullProgram hq k)
    (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan)
    ((none : Option Bool),
      (((none : Option Bool), Bf.initial), Bt.initial))

noncomputable def resetCircuit {q : ℕ} : Circuit (Stack q) :=
  Circuit.of (TruthReset.program (q := q)) (0 : Fin 4) ((), none)

noncomputable def slotCircuit {a q : ℕ} (hq : 0 < q)
    (k : Fin (a ^ q)) : Circuit (Stack q) :=
  Circuit.seq (fullCircuit hq k) (resetCircuit (q := q))

def slotClauses {a q : ℕ} (hq : 0 < q)
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r : ℕ) (k : Fin (a ^ q)) (b : Bool) :
    List EncodedCNF.Clause :=
  chain (SourceClauseGenericCallback.base n r k)
    (tupleClause hq k (SourceClauseCallback.rowQuery row) b)

def slotSaved {a q : ℕ} (hq : 0 < q)
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r : ℕ) (k : Fin (a ^ q)) (b : Bool)
    (saved : List Bool) : List Bool :=
  (EncodedCNF.clauseFields (slotClauses hq row n r k b)).reverse ++ saved

def slotCount {q : ℕ} (b : Bool) (count : List Bool) : List Bool :=
  List.replicate (SourceClauseGenericDual.clauseCount q b) true ++ count

theorem slot_run {a q : ℕ} (hq : 0 < q)
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r : ℕ) (k : Fin (a ^ q))
    (saved output count : List Bool)
    (table : Fin (a ^ q) → Bool)
    (hrow : row (.inr 2) = true :: List.ofFn table)
    (hquery : ∀ j : Fin q, row (.inl (j, 1)) =
      List.replicate (row (.inl (j, 1))).length true) :
    Circuit.Run (slotCircuit hq k)
      (SourceClauseRowWriterTruthFrame.initial row n r saved output count)
      (SourceClauseRowWriterTruthFrame.initial row n r
        (slotSaved hq row n r k (table k) saved)
        output (slotCount (q := q) (table k) count)) := by
  apply Circuit.seq_run
  · exact SourceClauseGenericDual.selected_full_run hq row n r k
      saved output count table hrow hquery
  · refine ⟨(SourceClauseGenericDual.finalBank hq row n r k saved output count
        ((List.ofFn table).drop (k.val + 1)) (table k) (.inr 0)).length +
      (SourceClauseGenericDual.finalBank hq row n r k saved output count
        ((List.ofFn table).drop (k.val + 1)) (table k) (.inr 1)).length + 4,
      ?_⟩
    simpa only [resetCircuit, Circuit.of, slotSaved, slotClauses,
      slotCount, SourceClauseGenericReset.cleared_finalBank] using
      TruthReset.run (SourceClauseGenericDual.finalBank hq row n r k saved output count
        ((List.ofFn table).drop (k.val + 1)) (table k))

noncomputable def listCircuit {a q : ℕ} (hq : 0 < q) :
    List (Fin (a ^ q)) → Circuit (Stack q)
  | [] => Circuit.halt
  | k :: ks => Circuit.seq (slotCircuit hq k) (listCircuit hq ks)

def listSaved {a q : ℕ} (hq : 0 < q)
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r : ℕ) (table : Fin (a ^ q) → Bool) :
    List (Fin (a ^ q)) → List Bool → List Bool
  | [], saved => saved
  | k :: ks, saved =>
      listSaved hq row n r table ks
        (slotSaved hq row n r k (table k) saved)

def listCount {a q : ℕ} (table : Fin (a ^ q) → Bool) :
    List (Fin (a ^ q)) → List Bool → List Bool
  | [], count => count
  | k :: ks, count =>
      listCount table ks (slotCount (q := q) (table k) count)

def listClauses {a q : ℕ} (hq : 0 < q)
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r : ℕ) (table : Fin (a ^ q) → Bool)
    (ks : List (Fin (a ^ q))) : List EncodedCNF.Clause :=
  ks.flatMap (fun k => slotClauses hq row n r k (table k))

theorem list_run {a q : ℕ} (hq : 0 < q)
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r : ℕ) (table : Fin (a ^ q) → Bool)
    (hrow : row (.inr 2) = true :: List.ofFn table)
    (hquery : ∀ j : Fin q, row (.inl (j, 1)) =
      List.replicate (row (.inl (j, 1))).length true)
    (ks : List (Fin (a ^ q))) (saved output count : List Bool) :
    Circuit.Run (listCircuit hq ks)
      (SourceClauseRowWriterTruthFrame.initial row n r saved output count)
      (SourceClauseRowWriterTruthFrame.initial row n r
        (listSaved hq row n r table ks saved) output
        (listCount table ks count)) := by
  induction ks generalizing saved count with
  | nil =>
      exact Circuit.halt_run _
  | cons k ks ih =>
      apply Circuit.seq_run
      · exact slot_run hq row n r k saved output count table hrow hquery
      · exact ih (slotSaved hq row n r k (table k) saved)
          (slotCount (q := q) (table k) count)

private theorem clauseFields_append (xs ys : List EncodedCNF.Clause) :
    EncodedCNF.clauseFields (xs ++ ys) =
      EncodedCNF.clauseFields xs ++ EncodedCNF.clauseFields ys := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [EncodedCNF.clauseFields, ih, List.append_assoc]

theorem listSaved_ordered {a q : ℕ} (hq : 0 < q)
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r : ℕ) (table : Fin (a ^ q) → Bool)
    (ks : List (Fin (a ^ q))) (saved : List Bool) :
    listSaved hq row n r table ks saved =
      (EncodedCNF.clauseFields
        (listClauses hq row n r table ks)).reverse ++ saved := by
  induction ks generalizing saved with
  | nil => simp [listSaved, listClauses, EncodedCNF.clauseFields]
  | cons k ks ih =>
      rw [listSaved, ih]
      simp only [listClauses, List.flatMap_cons, clauseFields_append,
        List.reverse_append, slotSaved, List.append_assoc]

noncomputable def allCircuit {a q : ℕ} (hq : 0 < q) : Circuit (Stack q) :=
  listCircuit hq (List.ofFn (fun k : Fin (a ^ q) => k))

theorem all_run {a q : ℕ} (hq : 0 < q)
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r : ℕ) (table : Fin (a ^ q) → Bool)
    (hrow : row (.inr 2) = true :: List.ofFn table)
    (hquery : ∀ j : Fin q, row (.inl (j, 1)) =
      List.replicate (row (.inl (j, 1))).length true)
    (saved output count : List Bool) :
    Circuit.Run (allCircuit (a := a) hq)
      (SourceClauseRowWriterTruthFrame.initial row n r saved output count)
      (SourceClauseRowWriterTruthFrame.initial row n r
        ((EncodedCNF.clauseFields
          (listClauses hq row n r table
            (List.ofFn (fun k : Fin (a ^ q) => k)))).reverse ++ saved)
        output
        (listCount table (List.ofFn (fun k : Fin (a ^ q) => k)) count)) := by
  simpa only [allCircuit, listSaved_ordered] using
    list_run hq row n r table hrow hquery
      (List.ofFn (fun k : Fin (a ^ q) => k)) saved output count

end EthInapproximability.CurrentPaper.SourceClauseGenericAllSlots
