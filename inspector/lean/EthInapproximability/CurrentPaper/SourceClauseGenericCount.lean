import EthInapproximability.CurrentPaper.SourceClauseGenericActual

namespace EthInapproximability.CurrentPaper.SourceClauseGenericCount

open SourceClauseGenericAllSlots SourceClauseRowSchedule SourceClauseEncoding

theorem slot_length {a q : ℕ} (hq : 0 < q)
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r : ℕ) (k : Fin (a ^ q)) (b : Bool) :
    (slotClauses hq row n r k b).length =
      SourceClauseGenericDual.clauseCount q b := by
  cases b <;>
    simp [slotClauses, SourceClauseGenericDual.clauseCount,
      SourceClauseRowSchedule.tupleClause] <;> omega

theorem list_count_exact {a q : ℕ} (hq : 0 < q)
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r : ℕ) (table : Fin (a ^ q) → Bool)
    (ks : List (Fin (a ^ q))) (count : List Bool) :
    listCount table ks count =
      List.replicate (listClauses hq row n r table ks).length true ++ count := by
  induction ks generalizing count with
  | nil => simp [listCount, listClauses]
  | cons k ks ih =>
      rw [listCount, ih]
      simp only [listClauses, List.flatMap_cons, List.length_append]
      rw [slot_length]
      simp only [slotCount]
      rw [← List.append_assoc, ← List.replicate_add]
      congr 2
      omega

theorem list_count_actual {n m a q : ℕ}
    (P : SourceBooleanEncoding.CSP n m a q) (hq : 0 < q)
    (r : Fin m) (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (table : Fin (a ^ q) → Bool)
    (ks : List (Fin (a ^ q))) (count : List Bool)
    (hquery : ∀ j : Fin q,
      SourceClauseCallback.rowQuery row j = (P.query r j).val)
    (haccept : ∀ k : Fin (a ^ q),
      table k = P.accept r (tuple a q k)) :
    listCount table ks count =
      List.replicate
        (ks.flatMap (fun k => SourceGenericOrder.rowChain P hq r k)).length
        true ++ count := by
  rw [← SourceClauseGenericActual.list_clauses_actual P hq r row table
    hquery haccept]
  exact list_count_exact hq row n r.val table ks count

end EthInapproximability.CurrentPaper.SourceClauseGenericCount
