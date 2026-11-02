import EthInapproximability.CurrentPaper.SourceClauseWriter
import EthInapproximability.CurrentPaper.SourceClauseHeaderCount

/-!
Locked v8 Section 6, thm:paper-sparse-gap-source: the exact generic-alphabet
prefix of the Boolean encoding, in the original source order. This provides
literal targets for physical callbacks; it does not assume their execution.
-/

namespace EthInapproximability.CurrentPaper.SourceGenericPrefix

open SourceBooleanEncoding SourceClauseEncoding EncodedCNF

def atLeastOrdinal {n : ℕ} (v : Fin n) : ℕ := v.val

def pairOrdinal {n a : ℕ} (v : Fin n) (s t : Fin a) : ℕ :=
  n + a * a * v.val + a * s.val + t.val

def atLeastIndex {n m a q : ℕ} (v : Fin n) : Fin (clauseCount n m a q) :=
  labelEquiv n m a q (.inl v)

def pairIndex {n m a q : ℕ} (v : Fin n) (s t : Fin a) :
    Fin (clauseCount n m a q) :=
  labelEquiv n m a q (.inr (.inl (v, s, t)))

@[simp] theorem atLeastIndex_val {n m a q : ℕ} (v : Fin n) :
    (atLeastIndex (m := m) (a := a) (q := q) v).val = atLeastOrdinal v := rfl

@[simp] theorem pairIndex_val {n m a q : ℕ} (v : Fin n) (s t : Fin a) :
    (pairIndex (m := m) (q := q) v s t).val = pairOrdinal v s t := by
  change n + (t.val + a * s.val + (a * a) * v.val) = _
  simp only [pairOrdinal]
  omega

def base (n a q ordinal : ℕ) : ℕ :=
  n * a + ordinal * (width a q + 1)

def atLeastPayload {n a : ℕ} (v : Fin n) : List Literal :=
  List.ofFn fun s : Fin a => SourceBooleanEncoding.positive (bitIndex v s)

def pairPayload {n a : ℕ} (v : Fin n) (s t : Fin a) : List Literal :=
  if s = t then
    [SourceBooleanEncoding.positive (bitIndex v s),
     SourceBooleanEncoding.negative (bitIndex v s)]
  else
    [SourceBooleanEncoding.negative (bitIndex v s),
     SourceBooleanEncoding.negative (bitIndex v t)]

theorem atLeast_source_slot {n m a q : ℕ} (P : CSP n m a q) (hq : 0 < q)
    (v : Fin n) :
    (formula P hq).clauses[atLeastIndex (m := m) (a := a) (q := q) v] =
      atLeastPayload (a := a) v := by
  simp [formula, SourceClauseEncoding.fromIndexed, atLeastIndex,
    clause, atLeastPayload]

theorem pair_source_slot {n m a q : ℕ} (P : CSP n m a q) (hq : 0 < q)
    (v : Fin n) (s t : Fin a) :
    (formula P hq).clauses[pairIndex (m := m) (q := q) v s t] =
      pairPayload v s t := by
  simp [formula, SourceClauseEncoding.fromIndexed, pairIndex,
    clause, pairPayload]

@[simp] theorem atLeast_length {n a : ℕ} (v : Fin n) :
    (atLeastPayload (a := a) v).length = a := by simp [atLeastPayload]

@[simp] theorem pair_length {n a : ℕ} (v : Fin n) (s t : Fin a) :
    (pairPayload v s t).length = 2 := by
  by_cases h : s = t <;> simp [pairPayload, h]

theorem atLeast_chain_length {n a q : ℕ} (v : Fin n) :
    (chain (base n a q (atLeastOrdinal v))
      (atLeastPayload (a := a) v)).length = 3 * a + 2 := by
  rw [SourceClauseHeaderCount.chain_length, atLeast_length]

theorem pair_chain_length {n a q : ℕ} (v : Fin n) (s t : Fin a) :
    (chain (base n a q (pairOrdinal v s t)) (pairPayload v s t)).length = 8 := by
  rw [SourceClauseHeaderCount.chain_length, pair_length]

theorem pair_payload_signs {n a : ℕ} (v : Fin n) (s t : Fin a) :
    pairPayload v s t =
      [⟨bitIndex v s, decide (s = t)⟩,
       SourceBooleanEncoding.negative (bitIndex v t)] := by
  by_cases h : s = t
  · subst t
    simp [pairPayload, SourceBooleanEncoding.positive,
      SourceBooleanEncoding.negative]
  · simp [pairPayload, h, SourceBooleanEncoding.negative]

theorem atLeast_source_chain {n m a q : ℕ} (P : CSP n m a q) (hq : 0 < q)
    (v : Fin n) :
    SourceClauseWriter.slotClauses P hq
      ((formula P hq).clauses[atLeastIndex (m := m) (a := a) (q := q) v],
        (atLeastIndex (m := m) (a := a) (q := q) v).val) =
      chain (base n a q (atLeastOrdinal v)) (atLeastPayload (a := a) v) := by
  rw [atLeast_source_slot, atLeastIndex_val]
  rfl

theorem pair_source_chain {n m a q : ℕ} (P : CSP n m a q) (hq : 0 < q)
    (v : Fin n) (s t : Fin a) :
    SourceClauseWriter.slotClauses P hq
      ((formula P hq).clauses[pairIndex (m := m) (q := q) v s t],
        (pairIndex (m := m) (q := q) v s t).val) =
      chain (base n a q (pairOrdinal v s t)) (pairPayload v s t) := by
  rw [pair_source_slot, pairIndex_val]
  rfl

def atLeastChains (n a q : ℕ) : List Clause :=
  (List.ofFn fun v : Fin n =>
    chain (base n a q v.val) (atLeastPayload (a := a) v)).flatten

def pairChains (n a q : ℕ) : List Clause :=
  (List.ofFn fun v : Fin n =>
    (List.ofFn fun u : Fin (a * a) =>
      let st : Fin a × Fin a := finProdFinEquiv.symm u
      chain (base n a q (pairOrdinal v st.1 st.2))
        (pairPayload v st.1 st.2)).flatten).flatten

private theorem flatten_ofFn_length {α : Type*} {N c : ℕ}
    (f : Fin N → List α) (h : ∀ i, (f i).length = c) :
    (List.ofFn f).flatten.length = c * N := by
  simp only [List.length_flatten, List.map_ofFn]
  have hmap : List.ofFn (List.length ∘ f) =
      List.ofFn (fun _ : Fin N => c) := by
    apply congrArg List.ofFn
    funext i
    exact h i
  rw [hmap]
  simp [List.ofFn_const, Nat.mul_comm]

theorem atLeastChains_length (n a q : ℕ) :
    (atLeastChains n a q).length = (3 * a + 2) * n := by
  apply flatten_ofFn_length
  intro v
  exact atLeast_chain_length v

theorem pairChains_length (n a q : ℕ) :
    (pairChains n a q).length = (8 * (a * a)) * n := by
  apply flatten_ofFn_length
  intro v
  apply flatten_ofFn_length
  intro u
  exact pair_chain_length v _ _

theorem prefix_length (n a q : ℕ) :
    (atLeastChains n a q ++ pairChains n a q).length =
      (3 * a + 2 + 8 * a * a) * n := by
  rw [List.length_append, atLeastChains_length, pairChains_length]
  ring

#print axioms atLeast_source_chain
#print axioms pair_source_chain
#print axioms prefix_length

end EthInapproximability.CurrentPaper.SourceGenericPrefix
