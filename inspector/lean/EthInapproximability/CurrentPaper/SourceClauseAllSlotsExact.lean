import EthInapproximability.CurrentPaper.SourceClauseAllSlotsClock
import EthInapproximability.CurrentPaper.SourceClauseAllSlotsCount

/-! Literal ordered output and exact unary header count for the same
fixed-q physical all-slot program. -/

namespace EthInapproximability.CurrentPaper.SourceClauseCallback.AllSlotsExact

open SourceClauseCallback

theorem all_bounded_exact {n m q : ℕ}
    (P : SourceBooleanEncoding.CSP n m 2 q) (hq : 0 < q)
    (r : Fin m) (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (table : Fin (2 ^ q) → Bool)
    (hrow : row (.inr 2) = true :: List.ofFn table)
    (hunary : ∀ j : Fin q, row (.inl (j, 1)) =
      List.replicate (row (.inl (j, 1))).length true)
    (hquery : ∀ j : Fin q,
      SourceClauseCallback.rowQuery row j = (P.query r j).val)
    (haccept : ∀ k : Fin (2 ^ q),
      table k = P.accept r (SourceClauseRowSchedule.tuple 2 q k))
    (saved output count : List Bool) :
    Circuit.BoundedRun (AllSlots.allCircuit hq)
      (AllSlotsClock.allCost hq row n r.val table saved output count)
      (SourceClauseRowWriterTruthFrame.initial row n r.val saved output count)
      (SourceClauseRowWriterTruthFrame.initial row n r.val
        ((EncodedCNF.clauseFields
          (AllSlots.actualListClauses P hq r
            (List.ofFn (fun k : Fin (2 ^ q) => k)))).reverse ++ saved)
        output
        (List.replicate
          (AllSlots.actualListClauses P hq r
            (List.ofFn (fun k : Fin (2 ^ q) => k))).length true ++ count)) := by
  simpa only [AllSlotsCount.list_count_actual P hq r row table _ count
    hquery haccept] using
    AllSlotsClock.all_bounded_actual P hq r row table
      hrow hunary hquery haccept saved output count

end EthInapproximability.CurrentPaper.SourceClauseCallback.AllSlotsExact
