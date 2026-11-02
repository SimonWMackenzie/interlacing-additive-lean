import EthInapproximability.CurrentPaper.SourceClauseGenericRow
import EthInapproximability.CurrentPaper.SourceClauseGenericCount

namespace EthInapproximability.CurrentPaper.SourceClauseGenericRowExact

open SourceBooleanEncoding SourceClauseRowSchedule
open SourceClauseGenericAllSlots SourceClauseGenericAllSlotsClock
open SourceClauseGenericAllSlotPolynomial
open SourceClauseCallback (Circuit rowQuery)

theorem row_bounded_exact {n m a q : ℕ}
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
      (allCoefficient a q *
        (SourceClauseGenericRow.inputBits row n r.val saved output count + 1) ^ 2)
      (SourceClauseRowWriterTruthFrame.initial row n r.val saved output count)
      (SourceClauseRowWriterTruthFrame.initial row n r.val
        ((EncodedCNF.clauseFields
          ((List.ofFn fun k : Fin (a ^ q) =>
            SourceGenericOrder.rowChain P hq r k).flatten)).reverse ++ saved)
        output
        (List.replicate
          ((List.ofFn fun k : Fin (a ^ q) =>
            SourceGenericOrder.rowChain P hq r k).flatten).length true ++ count)) := by
  have h := SourceClauseGenericRow.row_bounded_polynomial
    P hq r row table hrow hunary hquery haccept saved output count
  have hc := SourceClauseGenericCount.list_count_actual P hq r row table
    (List.ofFn (fun k : Fin (a ^ q) => k)) count hquery haccept
  simpa only [hc, List.flatMap, List.map_ofFn] using h

#print axioms row_bounded_exact

end EthInapproximability.CurrentPaper.SourceClauseGenericRowExact
