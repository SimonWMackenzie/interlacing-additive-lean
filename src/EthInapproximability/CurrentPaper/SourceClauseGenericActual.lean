import EthInapproximability.CurrentPaper.SourceClauseGenericAllSlotsClock
import EthInapproximability.CurrentPaper.SourceGenericOrder

namespace EthInapproximability.CurrentPaper.SourceClauseGenericActual

open SourceBooleanEncoding SourceClauseRowSchedule SourceClauseEncoding
open SourceClauseGenericAllSlots SourceClauseGenericAllSlotsClock
open SourceClauseCallback (Circuit rowQuery)

theorem base_eq_source {a q : ℕ} (n r : ℕ) (k : Fin (a ^ q)) :
    SourceClauseGenericCallback.base n r k =
      SourceGenericPrefix.base n a q (slot n a q r k) := by
  rfl

theorem slot_clause_actual {n m a q : ℕ}
    (P : CSP n m a q) (hq : 0 < q) (r : Fin m)
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (table : Fin (a ^ q) → Bool)
    (hquery : ∀ j : Fin q, rowQuery row j = (P.query r j).val)
    (haccept : ∀ k : Fin (a ^ q),
      table k = P.accept r (tuple a q k))
    (k : Fin (a ^ q)) :
    slotClauses hq row n r.val k (table k) =
      SourceGenericOrder.rowChain P hq r k := by
  have hfun : rowQuery row = fun j => (P.query r j).val := by
    funext j
    exact hquery j
  simp [slotClauses, SourceGenericOrder.rowChain,
    base_eq_source, hfun, haccept k]

theorem list_clauses_actual {n m a q : ℕ}
    (P : CSP n m a q) (hq : 0 < q) (r : Fin m)
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (table : Fin (a ^ q) → Bool)
    (hquery : ∀ j : Fin q, rowQuery row j = (P.query r j).val)
    (haccept : ∀ k : Fin (a ^ q),
      table k = P.accept r (tuple a q k))
    (ks : List (Fin (a ^ q))) :
    listClauses hq row n r.val table ks =
      ks.flatMap (fun k => SourceGenericOrder.rowChain P hq r k) := by
  unfold listClauses
  apply List.flatMap_congr
  intro k _
  exact slot_clause_actual P hq r row table hquery haccept k

theorem all_bounded_actual {n m a q : ℕ}
    (P : CSP n m a q) (hq : 0 < q) (r : Fin m)
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (table : Fin (a ^ q) → Bool)
    (hrow : row (.inr 2) = true :: List.ofFn table)
    (hunary : ∀ j : Fin q, row (.inl (j, 1)) =
      List.replicate (row (.inl (j, 1))).length true)
    (hquery : ∀ j : Fin q, rowQuery row j = (P.query r j).val)
    (haccept : ∀ k : Fin (a ^ q),
      table k = P.accept r (tuple a q k))
    (saved output count : List Bool) :
    Circuit.BoundedRun (allCircuit (a := a) hq)
      (allCost hq row n r.val table saved output count)
      (SourceClauseRowWriterTruthFrame.initial row n r.val saved output count)
      (SourceClauseRowWriterTruthFrame.initial row n r.val
        ((EncodedCNF.clauseFields
          ((List.ofFn fun k : Fin (a ^ q) =>
            SourceGenericOrder.rowChain P hq r k).flatten)).reverse ++ saved)
        output
        (listCount table (List.ofFn (fun k : Fin (a ^ q) => k)) count)) := by
  have h := all_bounded hq row n r.val table hrow hunary saved output count
  simpa only [list_clauses_actual P hq r row table hquery haccept,
    List.flatMap, List.map_ofFn] using h

end EthInapproximability.CurrentPaper.SourceClauseGenericActual
