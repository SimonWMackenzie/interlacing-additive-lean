import EthInapproximability.CurrentPaper.SourceBooleanThreeCNF

/-!
# Exact clause-count target for the ordered Boolean source adapter

Source: frozen v8 `06-eth.tex`, the exact-one encoding and ordered prefix-OR
three-CNF translation. A future physical writer must count *emitted* clauses:
accepted tuple slots have one extra literal and therefore three extra output
clauses. This finite identity fixes the header target, not a runtime claim.
-/

namespace EthInapproximability.CurrentPaper.SourceClauseHeaderCount

open SourceClauseEncoding

def countedClauses (cs : List (List EncodedCNF.Literal)) : Nat :=
  (cs.map fun c => 3 * c.length + 2).sum

private theorem gates_length (c : List EncodedCNF.Literal) (j base : Nat) :
    ((c.zipIdx j).flatMap fun (l, t) => orGate (base + t) l).length =
      3 * c.length := by
  induction c generalizing j with
  | nil => simp
  | cons l cs ih =>
      simp only [List.zipIdx_cons, List.flatMap_cons, List.length_append,
        orGate_length, List.length_cons]
      rw [ih]
      omega

theorem chain_length (base : Nat) (c : List EncodedCNF.Literal) :
    (chain base c).length = 3 * c.length + 2 := by
  simp only [chain, List.length_append, List.length_singleton]
  rw [gates_length]
  omega

private theorem translate_list_length (cs : List (List EncodedCNF.Literal))
    (j vars K : Nat) :
    ((cs.zipIdx j).flatMap fun (c, i) => chain (vars + i * (K + 1)) c).length =
      countedClauses cs := by
  induction cs generalizing j with
  | nil => simp [countedClauses]
  | cons c cs ih =>
      simp only [List.zipIdx_cons, List.flatMap_cons, List.length_append,
        chain_length, countedClauses, List.map_cons, List.sum_cons]
      rw [ih]
      rfl

/-- The exact number to put in the second header field of `EncodedCNF.encode`.
It counts the actual prefix-chain clauses in their existing order. -/
theorem translate_clause_count (K : Nat) (f : LongFormula) :
    (translate K f).clauses.length = countedClauses f.clauses := by
  change ((f.clauses.zipIdx 0).flatMap fun (c, i) =>
    chain (f.variables + i * (K + 1)) c).length = _
  exact translate_list_length f.clauses 0 f.variables K

theorem boolean_clause_count {n m a q : Nat} (P : SourceBooleanEncoding.CSP n m a q)
    (hq : 0 < q) :
    (SourceBooleanEncoding.threeCNF P hq).clauses.length =
      countedClauses (SourceBooleanEncoding.formula P hq).clauses := by
  exact translate_clause_count _ _

end EthInapproximability.CurrentPaper.SourceClauseHeaderCount
