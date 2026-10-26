import EthInapproximability.CurrentPaper.GenericPairGateCycle
import EthInapproximability.CurrentPaper.GenericPairUnitLift

namespace EthInapproximability.CurrentPaper.SourceGenericPrefixMachine.PairSource

open SourceBooleanEncoding SourceClauseEncoding EncodedCNF SourceGenericPrefix

private theorem clauseFields_append (xs ys : List Clause) :
    clauseFields (xs ++ ys) = clauseFields xs ++ clauseFields ys := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [clauseFields,ih,List.append_assoc]

def savedAfter {n a q : Nat} (v : Fin n) (s t : Fin a)
    (saved : List Bool) : List Bool :=
  let ordinal := pairOrdinal v s t
  let w := width a q + 1
  let s₁ := UnitHandoff.nextSaved n a ordinal w 0 false saved
  let s₂ := (clauseFields (PairGateCleanup.emitted v s 0 ordinal w
    (decide (s = t)))).reverse ++ s₁
  let s₃ := (clauseFields (PairGateCleanup.emitted v t 1 ordinal w false)).reverse ++ s₂
  UnitHandoff.nextSaved n a ordinal w 2 true s₃

theorem savedAfter_eq_chain {n a q : Nat} (v : Fin n) (s t : Fin a)
    (saved : List Bool) :
    savedAfter (q := q) v s t saved =
      (clauseFields (chain (base n a q (pairOrdinal v s t))
        (pairPayload v s t))).reverse ++ saved := by
  rw [pair_payload_signs]
  simp [savedAfter,UnitHandoff.nextSaved,
    PairGateCleanup.emitted,SourceClauseUnitMachine.unitClause,
    chain,base,clauseFields_append,clauseFields,List.reverse_append,
    List.append_assoc,SourceClauseEncoding.positive,
    SourceClauseEncoding.negative]
  have h0 : pairOrdinal v s t * (width a q + 1) + n * a =
      n * a + pairOrdinal v s t * (width a q + 1) := by omega
  have h1 : pairOrdinal v s t * (width a q + 1) + (n * a + 1) =
      n * a + pairOrdinal v s t * (width a q + 1) + 1 := by omega
  have h2 : pairOrdinal v s t * (width a q + 1) + (n * a + 2) =
      n * a + pairOrdinal v s t * (width a q + 1) + 2 := by omega
  simp only [h0,h1,h2,SourceBooleanEncoding.negative]

#print axioms savedAfter_eq_chain

end EthInapproximability.CurrentPaper.SourceGenericPrefixMachine.PairSource
