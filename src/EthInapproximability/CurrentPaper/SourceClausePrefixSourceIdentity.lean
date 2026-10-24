import EthInapproximability.CurrentPaper.SourceClausePrefixGateCycle

namespace EthInapproximability.CurrentPaper.SourceBooleanPrefix.PrefixSourceIdentity

open SourceClauseEncoding SourceBooleanEncoding EncodedCNF

def savedAfter {n q : ℕ} (v : Fin n) (saved : List Bool) : List Bool :=
  PrefixSharedUnitHandoff.nextSaved n v.val (width 2 q + 1) 2 true
    (PrefixSharedGateHandoff.nextSaved (q := q) v (1 : Fin 2)
      (PrefixSharedGateHandoff.nextSaved (q := q) v (0 : Fin 2)
        (PrefixSharedUnitHandoff.nextSaved n v.val (width 2 q + 1) 0 false
          saved)))

theorem savedAfter_eq_chain {n q : ℕ} (v : Fin n)
    (saved : List Bool) :
    savedAfter (q := q) v saved =
      (clauseFields (chain (base n q (atLeastOrdinal v))
        (atLeastPayload v))).reverse ++ saved := by
  simp [savedAfter, PrefixSharedUnitHandoff.nextSaved,
    PrefixSharedGateHandoff.nextSaved, SourceClauseUnitMachine.unitClause,
    atLeastPayload, chain, orGate, clauseFields,
    List.reverse_append, List.append_assoc, base, atLeastOrdinal]
  have htop : v.val * (width 2 q + 1) + (2 * n + 2) =
      2 * n + v.val * (width 2 q + 1) + 2 := by omega
  have hbottom : v.val * (width 2 q + 1) + 2 * n =
      2 * n + v.val * (width 2 q + 1) := by omega
  rw [htop, hbottom]
  rfl

end EthInapproximability.CurrentPaper.SourceBooleanPrefix.PrefixSourceIdentity

#print axioms EthInapproximability.CurrentPaper.SourceBooleanPrefix.PrefixSourceIdentity.savedAfter_eq_chain
