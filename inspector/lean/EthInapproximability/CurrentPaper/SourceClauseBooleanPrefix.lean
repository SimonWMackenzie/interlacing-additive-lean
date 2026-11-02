import EthInapproximability.CurrentPaper.SourceClauseWriter
import EthInapproximability.CurrentPaper.SourceBooleanThreeCNF

/-!
Exact source identities for the first `5*n` Boolean clause slots of the
frozen v8 converter. The physical callbacks are separate obligations.
-/

namespace EthInapproximability.CurrentPaper.SourceBooleanPrefix

open SourceBooleanEncoding SourceClauseEncoding EncodedCNF

def atLeastOrdinal {n : ℕ} (v : Fin n) : ℕ := v.val

def pairOrdinal {n : ℕ} (v : Fin n) (s t : Fin 2) : ℕ :=
  n + 4 * v.val + 2 * s.val + t.val

def atLeastIndex {n m q : ℕ} (v : Fin n) : Fin (clauseCount n m 2 q) :=
  ⟨atLeastOrdinal v, by simp [atLeastOrdinal, clauseCount]; omega⟩

def pairIndex {n m q : ℕ} (v : Fin n) (s t : Fin 2) :
    Fin (clauseCount n m 2 q) :=
  ⟨pairOrdinal v s t, by
    have hv := v.isLt
    have hs := s.isLt
    have ht := t.isLt
    simp only [pairOrdinal, clauseCount]
    omega⟩

theorem atLeast_label {n m q : ℕ} (v : Fin n) :
    labelEquiv n m 2 q (.inl v) = atLeastIndex (m := m) (q := q) v := by
  apply Fin.ext
  rfl

theorem pair_label {n m q : ℕ} (v : Fin n) (s t : Fin 2) :
    labelEquiv n m 2 q (.inr (.inl (v, s, t))) =
      pairIndex (m := m) (q := q) v s t := by
  apply Fin.ext
  dsimp [labelEquiv, Equiv.sumCongr, Equiv.prodCongr,
    finSumFinEquiv, finProdFinEquiv, pairIndex, pairOrdinal]
  change n + (t.val + 2 * s.val + 4 * v.val) =
    pairOrdinal v s t
  simp only [pairOrdinal]
  omega

def base (n q ordinal : ℕ) : ℕ :=
  2 * n + ordinal * (width 2 q + 1)

def atLeastPayload {n : ℕ} (v : Fin n) : List Literal :=
  [SourceBooleanEncoding.positive (bitIndex v (0 : Fin 2)),
   SourceBooleanEncoding.positive (bitIndex v (1 : Fin 2))]

def pairPayload {n : ℕ} (v : Fin n) (s t : Fin 2) : List Literal :=
  if s = t then
    [SourceBooleanEncoding.positive (bitIndex v s),
     SourceBooleanEncoding.negative (bitIndex v s)]
  else
    [SourceBooleanEncoding.negative (bitIndex v s),
     SourceBooleanEncoding.negative (bitIndex v t)]

theorem atLeast_clause {n m q : ℕ} (P : CSP n m 2 q) (hq : 0 < q)
    (v : Fin n) :
    clause P hq (.inl v) = atLeastPayload v := by
  simp [clause, atLeastPayload, List.ofFn, Fin.foldr, Fin.foldr.loop]

theorem pair_clause {n m q : ℕ} (P : CSP n m 2 q) (hq : 0 < q)
    (v : Fin n) (s t : Fin 2) :
    clause P hq (.inr (.inl (v, s, t))) = pairPayload v s t := by
  simp [clause, pairPayload]

theorem atLeast_source_slot {n m q : ℕ} (P : CSP n m 2 q) (hq : 0 < q)
    (v : Fin n) :
    (formula P hq).clauses[atLeastIndex (m := m) (q := q) v] =
      atLeastPayload v := by
  have hi : (labelEquiv n m 2 q).symm (atLeastIndex (m := m) (q := q) v) =
      .inl v := by
    rw [← atLeast_label]
    exact (labelEquiv n m 2 q).symm_apply_apply _
  simp [formula, SourceClauseEncoding.fromIndexed, hi]
  exact atLeast_clause P hq v

theorem pair_source_slot {n m q : ℕ} (P : CSP n m 2 q) (hq : 0 < q)
    (v : Fin n) (s t : Fin 2) :
    (formula P hq).clauses[pairIndex (m := m) (q := q) v s t] =
      pairPayload v s t := by
  have hi : (labelEquiv n m 2 q).symm (pairIndex (m := m) (q := q) v s t) =
      .inr (.inl (v, s, t)) := by
    rw [← pair_label]
    exact (labelEquiv n m 2 q).symm_apply_apply _
  simp [formula, SourceClauseEncoding.fromIndexed, hi]
  exact pair_clause P hq v s t

theorem atLeast_length {n : ℕ} (v : Fin n) :
    (atLeastPayload v).length = 2 := rfl

theorem pair_length {n : ℕ} (v : Fin n) (s t : Fin 2) :
    (pairPayload v s t).length = 2 := by
  by_cases h : s = t <;> simp [pairPayload, h]

theorem atLeast_chain_length {n q : ℕ} (v : Fin n) :
    (chain (base n q (atLeastOrdinal v)) (atLeastPayload v)).length = 8 := by
  simp [chain, atLeastPayload, orGate]

theorem pair_chain_length {n q : ℕ} (v : Fin n) (s t : Fin 2) :
    (chain (base n q (pairOrdinal v s t)) (pairPayload v s t)).length = 8 := by
  by_cases h : s = t <;> simp [chain, pairPayload, h, orGate]

theorem pair_diagonal {n : ℕ} (v : Fin n) (s : Fin 2) :
    pairPayload v s s =
      [SourceBooleanEncoding.positive (bitIndex v s),
       SourceBooleanEncoding.negative (bitIndex v s)] := by
  simp [pairPayload]

theorem atLeast_source_chain {n m q : ℕ} (P : CSP n m 2 q) (hq : 0 < q)
    (v : Fin n) :
    SourceClauseWriter.slotClauses P hq
      ((formula P hq).clauses[atLeastIndex (m := m) (q := q) v],
        (atLeastIndex (m := m) (q := q) v).val) =
      chain (base n q (atLeastOrdinal v)) (atLeastPayload v) := by
  rw [atLeast_source_slot]
  simp only [SourceClauseWriter.slotClauses, base, atLeastIndex,
    atLeastOrdinal, Fin.val_mk]
  congr 1
  ring

theorem pair_source_chain {n m q : ℕ} (P : CSP n m 2 q) (hq : 0 < q)
    (v : Fin n) (s t : Fin 2) :
    SourceClauseWriter.slotClauses P hq
      ((formula P hq).clauses[pairIndex (m := m) (q := q) v s t],
        (pairIndex (m := m) (q := q) v s t).val) =
      chain (base n q (pairOrdinal v s t)) (pairPayload v s t) := by
  rw [pair_source_slot]
  simp only [SourceClauseWriter.slotClauses, base, pairIndex,
    pairOrdinal, Fin.val_mk]
  congr 1
  ring

theorem atLeast_reverse_accumulator {n m q : ℕ} (P : CSP n m 2 q)
    (hq : 0 < q) (v : Fin n) (saved : List Bool) :
    SourceClauseWriter.prependSlot P hq
      ((formula P hq).clauses[atLeastIndex (m := m) (q := q) v],
        (atLeastIndex (m := m) (q := q) v).val) saved =
      (clauseFields (chain (base n q (atLeastOrdinal v))
        (atLeastPayload v))).reverse ++ saved := by
  rw [SourceClauseWriter.prependSlot_correct, atLeast_source_chain]

theorem pair_reverse_accumulator {n m q : ℕ} (P : CSP n m 2 q)
    (hq : 0 < q) (v : Fin n) (s t : Fin 2) (saved : List Bool) :
    SourceClauseWriter.prependSlot P hq
      ((formula P hq).clauses[pairIndex (m := m) (q := q) v s t],
        (pairIndex (m := m) (q := q) v s t).val) saved =
      (clauseFields (chain (base n q (pairOrdinal v s t))
        (pairPayload v s t))).reverse ++ saved := by
  rw [SourceClauseWriter.prependSlot_correct, pair_source_chain]

end EthInapproximability.CurrentPaper.SourceBooleanPrefix
