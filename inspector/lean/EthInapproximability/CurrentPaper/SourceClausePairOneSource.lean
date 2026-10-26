import EthInapproximability.CurrentPaper.SourceClausePairSignedGate

/-! Exact source byte identity for the four physical stages of one ordered pair. -/

namespace EthInapproximability.CurrentPaper.SourceBooleanPrefix.PairOneSource

open SourceBooleanEncoding SourceClauseEncoding EncodedCNF

private theorem clauseFields_append (xs ys : List Clause) :
    clauseFields (xs ++ ys) = clauseFields xs ++ clauseFields ys := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [clauseFields, ih, List.append_assoc]

def savedAfter {n q : Nat} (v : Fin n) (s t : Fin 2)
    (saved : List Bool) : List Bool :=
  PrefixSharedUnitHandoff.nextSaved n (pairOrdinal v s t)
    (width 2 q + 1) 2 true
    ((clauseFields (PairSignedGate.emittedGate (q := q) v s t 1)).reverse ++
      ((clauseFields (PairSignedGate.emittedGate (q := q) v s t 0)).reverse ++
        PrefixSharedUnitHandoff.nextSaved n (pairOrdinal v s t)
          (width 2 q + 1) 0 false saved))

theorem savedAfter_eq_chain {n q : Nat} (v : Fin n) (s t : Fin 2)
    (saved : List Bool) :
    savedAfter (q := q) v s t saved =
      (clauseFields (chain (base n q (pairOrdinal v s t))
        (pairPayload v s t))).reverse ++ saved := by
  rw [PairSignedGate.chain_stages]
  simp [savedAfter, PrefixSharedUnitHandoff.nextSaved,
    SourceClauseUnitMachine.unitClause, clauseFields,
    List.reverse_append, List.append_assoc, base]
  have htop : pairOrdinal v s t * (width 2 q + 1) + (2 * n + 2) =
      2 * n + pairOrdinal v s t * (width 2 q + 1) + 2 := by omega
  have hbottom : pairOrdinal v s t * (width 2 q + 1) + 2 * n =
      2 * n + pairOrdinal v s t * (width 2 q + 1) := by omega
  rw [htop, hbottom]
  simp [clauseFields_append, clauseFields, List.reverse_append,
    List.append_assoc, SourceClauseEncoding.positive,
    SourceClauseEncoding.negative]

end EthInapproximability.CurrentPaper.SourceBooleanPrefix.PairOneSource

#print axioms EthInapproximability.CurrentPaper.SourceBooleanPrefix.PairOneSource.savedAfter_eq_chain
