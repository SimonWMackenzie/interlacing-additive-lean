import EthInapproximability.CurrentPaper.SourceGenericPrefix
import EthInapproximability.CurrentPaper.SourceClauseRowSchedule
import EthInapproximability.CurrentPaper.SourceClauseCountFinalize

/-!
Locked v8 Section 6: exact generic-alphabet source order, emitted-clause
count and final serialization. No parser or prefix/row execution is assumed
to have occurred; the finalizer theorem names its entire required input bank.
-/

namespace EthInapproximability.CurrentPaper.SourceGenericOrder

open SourceBooleanEncoding SourceClauseEncoding EncodedCNF
open SourceGenericPrefix SourceClauseRowSchedule

private theorem zipIdx_ofFn {α : Type*} (xs : List α) :
    xs.zipIdx = List.ofFn (fun j : Fin xs.length => (xs.get j, j.val)) := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp only [List.getElem_zipIdx, List.getElem_ofFn,
      Nat.zero_add, List.get_eq_getElem]

private theorem flatMap_indexed_ofFn {α β : Type*} {N : ℕ}
    (f : Fin N → α) (g : α → ℕ → List β) :
    ((List.ofFn f).zipIdx.flatMap fun (x, j) => g x j) =
      (List.ofFn fun i : Fin N => g (f i) i.val).flatten := by
  rw [zipIdx_ofFn]
  simp only [List.length_ofFn, List.get_ofFn, List.flatMap, List.map_ofFn]
  rfl

def rowChain {n m a q : ℕ} (P : CSP n m a q) (hq : 0 < q)
    (r : Fin m) (k : Fin (a ^ q)) : List Clause :=
  chain (base n a q (slot n a q r.val k))
    (tupleClause hq k (fun j => (P.query r j).val)
      (P.accept r (tuple a q k)))

def rowChains {n m a q : ℕ} (P : CSP n m a q) (hq : 0 < q) : List Clause :=
  (List.ofFn fun r : Fin m =>
    (List.ofFn fun k : Fin (a ^ q) => rowChain P hq r k).flatten).flatten

private def indexedChain {n m a q : ℕ} (P : CSP n m a q) (hq : 0 < q)
    (i : Fin (clauseCount n m a q)) : List Clause :=
  chain (base n a q i.val) (clause P hq ((labelEquiv n m a q).symm i))

private theorem threeCNF_indexed {n m a q : ℕ} (P : CSP n m a q)
    (hq : 0 < q) :
    (threeCNF P hq).clauses =
      (List.ofFn fun i : Fin (clauseCount n m a q) =>
        indexedChain P hq i).flatten := by
  change ((List.ofFn (fun i : Fin (clauseCount n m a q) =>
      clause P hq ((labelEquiv n m a q).symm i))).zipIdx.flatMap
      fun (c, j) => chain (n * a + j * (width a q + 1)) c) = _
  simpa only [indexedChain, base] using flatMap_indexed_ofFn
    (fun i : Fin (clauseCount n m a q) =>
      clause P hq ((labelEquiv n m a q).symm i))
    (fun c j => chain (n * a + j * (width a q + 1)) c)

/-- All at-least-one slots precede all ordered pairs; only then do row-major
tuple slots begin. Diagonal pairs and accepted tuples are not deleted. -/
theorem threeCNF_clauses_blocks {n m a q : ℕ}
    (P : CSP n m a q) (hq : 0 < q) :
    (threeCNF P hq).clauses =
      atLeastChains n a q ++ pairChains n a q ++ rowChains P hq := by
  rw [threeCNF_indexed]
  change (List.ofFn (fun i : Fin (n + (n * (a * a) + m * a ^ q)) =>
      indexedChain P hq i)).flatten = _
  rw [List.ofFn_add]
  simp only [List.flatten_append]
  rw [List.ofFn_add (f := fun i : Fin (n * (a * a) + m * a ^ q) =>
    indexedChain P hq (Fin.natAdd n i))]
  simp only [List.flatten_append]
  rw [List.append_assoc]
  apply congrArg₂ List.append
  · unfold atLeastChains
    apply congrArg List.flatten
    apply congrArg List.ofFn
    funext v
    change indexedChain P hq
      (atLeastIndex (m := m) (a := a) (q := q) v) = _
    simp only [indexedChain, atLeastIndex_val]
    simp [atLeastIndex, atLeastPayload, clause, atLeastOrdinal]
  · apply congrArg₂ List.append
    · rw [List.ofFn_mul]
      rw [List.flatten_flatten, List.map_ofFn]
      unfold pairChains
      apply congrArg List.flatten
      apply congrArg List.ofFn
      funext v
      apply congrArg List.flatten
      apply congrArg List.ofFn
      funext u
      let st : Fin a × Fin a := finProdFinEquiv.symm u
      have hu : u.val = a * st.1.val + st.2.val := by
        have h := congrArg Fin.val
          ((finProdFinEquiv : Fin a × Fin a ≃ Fin (a * a)).apply_symm_apply u)
        simpa only [st, finProdFinEquiv_apply_val, Nat.add_comm] using h.symm
      have hi :
          (Fin.natAdd n (Fin.castLE (by omega)
            (⟨v.val * (a * a) + u.val, by
              have hv := v.isLt
              have hu' := u.isLt
              nlinarith⟩ : Fin (n * (a * a)))) : Fin (clauseCount n m a q)) =
            pairIndex (m := m) (q := q) v st.1 st.2 := by
        apply Fin.ext
        simp only [Fin.val_natAdd, Fin.val_castLE, pairIndex_val, pairOrdinal]
        rw [hu]
        ring
      rw [hi]
      unfold indexedChain
      rw [pairIndex_val]
      simp only [pairIndex, Equiv.symm_apply_apply, clause, pairPayload]
      rfl
    · rw [List.ofFn_mul]
      rw [List.flatten_flatten, List.map_ofFn]
      unfold rowChains
      apply congrArg List.flatten
      apply congrArg List.ofFn
      funext r
      apply congrArg List.flatten
      apply congrArg List.ofFn
      funext k
      have hi :
          (Fin.natAdd n (Fin.natAdd (n * (a * a))
            (⟨r.val * a ^ q + k.val, by
              have hr := r.isLt
              have hk := k.isLt
              nlinarith⟩ : Fin (m * a ^ q))) :
              Fin (clauseCount n m a q)) =
            (labelEquiv n m a q) (.inr (.inr (r, tuple a q k))) := by
        apply Fin.ext
        simp only [Fin.val_natAdd, label_slot, slot]
        omega
      rw [hi]
      simp only [indexedChain, Equiv.symm_apply_apply, label_slot, rowChain]
      rw [exact_row_clause]

theorem threeCNF_header_length {n m a q : ℕ}
    (P : CSP n m a q) (hq : 0 < q) :
    (threeCNF P hq).clauses.length =
      (3 * a + 2 + 8 * a * a) * n + (rowChains P hq).length := by
  rw [threeCNF_clauses_blocks, List.length_append, prefix_length]

def sourceVariables {n m a q : ℕ} (_P : CSP n m a q) : ℕ :=
  n * a + (width a q + 1) * clauseCount n m a q

def sourceEmittedCount {n m a q : ℕ} (P : CSP n m a q) (hq : 0 < q) : ℕ :=
  (3 * a + 2 + 8 * a * a) * n + (rowChains P hq).length

def sourceReversePayload {n m a q : ℕ} (P : CSP n m a q)
    (hq : 0 < q) : List Bool :=
  (clauseFields (atLeastChains n a q ++ pairChains n a q ++ rowChains P hq)).reverse

theorem sourceVariables_eq {n m a q : ℕ} (P : CSP n m a q) (hq : 0 < q) :
    sourceVariables P = (threeCNF P hq).variables := by
  simp [sourceVariables, threeCNF, SourceClauseEncoding.translate,
    formula, SourceClauseEncoding.fromIndexed]

theorem sourceEmittedCount_eq {n m a q : ℕ} (P : CSP n m a q) (hq : 0 < q) :
    sourceEmittedCount P hq = (threeCNF P hq).clauses.length :=
  (threeCNF_header_length P hq).symm

theorem sourceReversePayload_eq {n m a q : ℕ} (P : CSP n m a q) (hq : 0 < q) :
    sourceReversePayload P hq = (clauseFields (threeCNF P hq).clauses).reverse := by
  rw [threeCNF_clauses_blocks]
  rfl

open Turing BitMachineEncoding in
/-- This is the unchanged fixed physical finalizer, on its fully specified
required input bank, for arbitrary source alphabet and arity. Upstream
construction of this bank is a separate obligation, not a hidden premise. -/
theorem source_count_and_finalize {n m a q : ℕ}
    (P : CSP n m a q) (hq : 0 < q) (output : List Bool) :
    ∃ t ≤ UnaryBinaryEncoding.coefficient * (sourceEmittedCount P hq + 1) ^ 2 +
        (sourceReversePayload P hq).length +
        3 * (sourceEmittedCount P hq).bits.length + sourceVariables P + 6,
      let c := ((advance SourceClauseCountFinalize.program)^[t])
        (⟨some (BitMachineRawSequence.leftLabel (.inr .testFuel)),
          ((SourceClauseCountFinalize.counter.initial, none), none),
          SourceClauseCountFinalize.inputBank
            (sourceVariables P) (sourceEmittedCount P hq)
            (sourceReversePayload P hq) output⟩ : SourceClauseCountFinalize.Config)
      c.l = none ∧ c.stk (.inl 3) = encode (threeCNF P hq) ++ output := by
  obtain ⟨t, ht, hr⟩ := SourceClauseCountFinalize.count_and_finalize_output
    (sourceVariables P) (sourceEmittedCount P hq) (sourceReversePayload P hq) output
  refine ⟨t, ht, ?_⟩
  dsimp only
  obtain ⟨hl, ho⟩ := hr
  constructor
  · exact hl
  · rw [ho, sourceVariables_eq P hq, sourceEmittedCount_eq P hq,
      sourceReversePayload_eq]
    simp [EncodedCNF.encode, List.append_assoc]

#print axioms threeCNF_clauses_blocks
#print axioms threeCNF_header_length
#print axioms source_count_and_finalize

end EthInapproximability.CurrentPaper.SourceGenericOrder
