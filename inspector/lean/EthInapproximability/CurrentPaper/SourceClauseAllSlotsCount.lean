import EthInapproximability.CurrentPaper.SourceClauseAllSlots

/-! The all-slot unary counter equals the length of the exact emitted
ordered three-clause list, not merely a separately tracked surrogate. -/

namespace EthInapproximability.CurrentPaper.SourceClauseCallback.AllSlotsCount

open SourceClauseCallback SourceClauseRowSchedule SourceClauseEncoding

theorem slot_length {q : ℕ} (hq : 0 < q)
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r : ℕ) (k : Fin (2 ^ q)) (b : Bool) :
    (AllSlots.slotClauses hq row n r k b).length =
      DualDispatch.clauseCount q b := by
  cases b <;>
    simp [AllSlots.slotClauses, DualDispatch.clauseCount,
      SourceClauseRowSchedule.tupleClause] <;> omega

theorem list_count_exact {q : ℕ} (hq : 0 < q)
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r : ℕ) (table : Fin (2 ^ q) → Bool)
    (ks : List (Fin (2 ^ q))) (count : List Bool) :
    AllSlots.listCount table ks count =
      List.replicate (AllSlots.listClauses hq row n r table ks).length true ++
        count := by
  induction ks generalizing count with
  | nil => simp [AllSlots.listCount, AllSlots.listClauses]
  | cons k ks ih =>
      rw [AllSlots.listCount, ih]
      simp only [AllSlots.listClauses, List.flatMap_cons, List.length_append]
      rw [slot_length]
      simp only [AllSlots.slotCount]
      rw [← List.append_assoc, ← List.replicate_add]
      congr 2
      omega

theorem list_count_actual {n m q : ℕ}
    (P : SourceBooleanEncoding.CSP n m 2 q) (hq : 0 < q)
    (r : Fin m) (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (table : Fin (2 ^ q) → Bool)
    (ks : List (Fin (2 ^ q))) (count : List Bool)
    (hquery : ∀ j : Fin q,
      SourceClauseCallback.rowQuery row j = (P.query r j).val)
    (haccept : ∀ k : Fin (2 ^ q),
      table k = P.accept r (tuple 2 q k)) :
    AllSlots.listCount table ks count =
      List.replicate (AllSlots.actualListClauses P hq r ks).length true ++
        count := by
  rw [← AllSlots.listClauses_actual P hq r row table ks hquery haccept]
  exact list_count_exact hq row n r.val table ks count

end EthInapproximability.CurrentPaper.SourceClauseCallback.AllSlotsCount
