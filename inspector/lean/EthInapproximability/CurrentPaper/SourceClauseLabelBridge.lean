import EthInapproximability.CurrentPaper.SourceClauseDualDispatch

/-! The selected physical tuple slot is the actual indexed clause occurrence
of the source Boolean CSP-to-3CNF translation, not merely an isomorphic
surrogate list.  The query/table correspondence premises identify a checked
row with a typed CSP row; the parser must supply these in a later interface.
-/

namespace EthInapproximability.CurrentPaper.SourceClauseCallback.SourceLabelBridge

open SourceBooleanEncoding SourceClauseRowSchedule SourceClauseEncoding

def label {n m q : ℕ} (r : Fin m) (k : Fin (2 ^ q)) :
    ClauseLabel n m 2 q :=
  .inr (.inr (r, tuple 2 q k))

theorem slot_address {n m q : ℕ} (r : Fin m) (k : Fin (2 ^ q)) :
    SourceClauseCallback.base n r.val k =
      n * 2 + ((labelEquiv n m 2 q) (label r k)).val *
        (SourceBooleanEncoding.width 2 q + 1) := by
  rw [label, label_slot]
  rfl

def sourceIndex {n m q : ℕ} (P : CSP n m 2 q) (hq : 0 < q)
    (r : Fin m) (k : Fin (2 ^ q)) :
    Fin (formula P hq).clauses.length :=
  ⟨((labelEquiv n m 2 q) (label r k)).val, by
    simpa [formula, SourceClauseEncoding.fromIndexed] using
      ((labelEquiv n m 2 q) (label r k)).isLt⟩

theorem sourceIndex_val {n m q : ℕ} (P : CSP n m 2 q) (hq : 0 < q)
    (r : Fin m) (k : Fin (2 ^ q)) :
    (sourceIndex P hq r k).val =
      ((labelEquiv n m 2 q) (label r k)).val := rfl

theorem indexed_clause {n m q : ℕ} (P : CSP n m 2 q)
    (hq : 0 < q) (r : Fin m) (k : Fin (2 ^ q)) :
    (formula P hq).clauses.get (sourceIndex P hq r k) =
      clause P hq (label r k) := by
  simp [formula, SourceClauseEncoding.fromIndexed, sourceIndex]

def actualTranslateBlock {n m q : ℕ} (P : CSP n m 2 q)
    (hq : 0 < q) (r : Fin m) (k : Fin (2 ^ q)) :
    List EncodedCNF.Clause :=
  chain ((formula P hq).variables + (sourceIndex P hq r k).val *
      (SourceBooleanEncoding.width 2 q + 1))
    ((formula P hq).clauses.get (sourceIndex P hq r k))

theorem actualTranslateBlock_eq {n m q : ℕ} (P : CSP n m 2 q)
    (hq : 0 < q) (r : Fin m) (k : Fin (2 ^ q)) :
    actualTranslateBlock P hq r k =
      chain (n * 2 + ((labelEquiv n m 2 q) (label r k)).val *
        (SourceBooleanEncoding.width 2 q + 1))
        (clause P hq (label r k)) := by
  simp [actualTranslateBlock, sourceIndex_val,
    formula, SourceClauseEncoding.fromIndexed]

theorem actualTranslateBlock_occurs {n m q : ℕ} (P : CSP n m 2 q)
    (hq : 0 < q) (r : Fin m) (k : Fin (2 ^ q))
    (c : EncodedCNF.Clause) (hc : c ∈ actualTranslateBlock P hq r k) :
    c ∈ (SourceClauseEncoding.translate (SourceBooleanEncoding.width 2 q)
      (formula P hq)).clauses := by
  let i := sourceIndex P hq r k
  have hi : i.val < (formula P hq).clauses.zipIdx.length := by
    simpa only [List.length_zipIdx] using i.isLt
  have hzip : ((formula P hq).clauses.get i, i.val) ∈
      (formula P hq).clauses.zipIdx := by
    have h := List.getElem_mem (l := (formula P hq).clauses.zipIdx) hi
    simpa only [List.getElem_zipIdx, Nat.zero_add, List.get_eq_getElem] using h
  change c ∈ ((formula P hq).clauses.zipIdx.flatMap fun (d, j) =>
    chain ((formula P hq).variables + j *
      (SourceBooleanEncoding.width 2 q + 1)) d)
  apply List.mem_flatMap.mpr
  exact ⟨_, hzip, hc⟩

theorem source_chain_eq {n m q : ℕ}
    (P : CSP n m 2 q) (hq : 0 < q)
    (r : Fin m) (k : Fin (2 ^ q))
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (table : Fin (2 ^ q) → Bool)
    (hquery : ∀ j : Fin q,
      SourceClauseCallback.rowQuery row j = (P.query r j).val)
    (haccept : table k = P.accept r (tuple 2 q k)) :
    chain (SourceClauseCallback.base n r.val k)
      (tupleClause hq k (SourceClauseCallback.rowQuery row) (table k)) =
    chain (n * 2 + ((labelEquiv n m 2 q) (label r k)).val *
      (SourceBooleanEncoding.width 2 q + 1))
      (clause P hq (label r k)) := by
  have hqfun : SourceClauseCallback.rowQuery row =
      fun j => (P.query r j).val := by
    funext j
    exact hquery j
  rw [haccept, hqfun, slot_address]
  exact congrArg (chain _)
    (SourceClauseRowSchedule.exact_row_clause P hq r k)

theorem selected_payload_original {n m q : ℕ}
    (P : CSP n m 2 q) (hq : 0 < q)
    (r : Fin m) (k : Fin (2 ^ q))
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (table : Fin (2 ^ q) → Bool)
    (saved : List Bool)
    (hquery : ∀ j : Fin q,
      SourceClauseCallback.rowQuery row j = (P.query r j).val)
    (haccept : table k = P.accept r (tuple 2 q k)) :
    (EncodedCNF.clauseFields
      (chain (SourceClauseCallback.base n r.val k)
        (tupleClause hq k (SourceClauseCallback.rowQuery row)
          (table k)))).reverse ++ saved =
    (EncodedCNF.clauseFields
      (chain (n * 2 + ((labelEquiv n m 2 q) (label r k)).val *
        (SourceBooleanEncoding.width 2 q + 1))
        (clause P hq (label r k)))).reverse ++ saved := by
  rw [source_chain_eq P hq r k row table hquery haccept]

theorem selected_payload_actual_block {n m q : ℕ}
    (P : CSP n m 2 q) (hq : 0 < q)
    (r : Fin m) (k : Fin (2 ^ q))
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (table : Fin (2 ^ q) → Bool)
    (saved : List Bool)
    (hquery : ∀ j : Fin q,
      SourceClauseCallback.rowQuery row j = (P.query r j).val)
    (haccept : table k = P.accept r (tuple 2 q k)) :
    (EncodedCNF.clauseFields
      (chain (SourceClauseCallback.base n r.val k)
        (tupleClause hq k (SourceClauseCallback.rowQuery row)
          (table k)))).reverse ++ saved =
    (EncodedCNF.clauseFields
      (actualTranslateBlock P hq r k)).reverse ++ saved := by
  rw [source_chain_eq P hq r k row table hquery haccept,
    actualTranslateBlock_eq]

end EthInapproximability.CurrentPaper.SourceClauseCallback.SourceLabelBridge
