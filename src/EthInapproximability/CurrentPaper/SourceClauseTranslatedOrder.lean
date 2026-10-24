import EthInapproximability.CurrentPaper.SourceClauseOrderDecomposition
import EthInapproximability.CurrentPaper.SourceClauseAllSlots
import EthInapproximability.CurrentPaper.SourceClauseHeaderCount

/-! Exact ordered translation of the Boolean source clause list. -/

namespace EthInapproximability.CurrentPaper.TranslatedOrder

open SourceBooleanEncoding SourceClauseEncoding EncodedCNF

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
  simp only [List.length_ofFn, List.get_ofFn, List.flatMap,
    List.map_ofFn]
  rfl

def atLeastChains {n m q : ℕ} (_P : CSP n m 2 q) :
    List EncodedCNF.Clause :=
  (List.ofFn fun v : Fin n =>
    chain (SourceBooleanPrefix.base n q v.val)
      (SourceBooleanPrefix.atLeastPayload v)).flatten

def pairChains {n m q : ℕ} (_P : CSP n m 2 q) :
    List EncodedCNF.Clause :=
  (List.ofFn fun v : Fin n =>
    (List.ofFn fun u : Fin 4 =>
      let st : Fin 2 × Fin 2 :=
        (finProdFinEquiv : Fin 2 × Fin 2 ≃ Fin 4).symm u
      chain (SourceBooleanPrefix.base n q
        (SourceBooleanPrefix.pairOrdinal v st.1 st.2))
        (SourceBooleanPrefix.pairPayload v st.1 st.2)).flatten).flatten

private def indexedChain {n m q : ℕ} (P : CSP n m 2 q) (hq : 0 < q)
    (i : Fin (clauseCount n m 2 q)) : List EncodedCNF.Clause :=
  chain ((formula P hq).variables + i.val * (width 2 q + 1))
    ((formula P hq).clauses.get
      (Fin.cast (by simp [formula, SourceClauseEncoding.fromIndexed]) i))

private theorem threeCNF_indexed {n m q : ℕ} (P : CSP n m 2 q)
    (hq : 0 < q) :
    (threeCNF P hq).clauses =
      (List.ofFn fun i : Fin (clauseCount n m 2 q) =>
        indexedChain P hq i).flatten := by
  change ((List.ofFn (fun i : Fin (clauseCount n m 2 q) =>
      clause P hq ((labelEquiv n m 2 q).symm i))).zipIdx.flatMap
      fun (c, j) => chain (n * 2 + j * (width 2 q + 1)) c) = _
  rw [flatMap_indexed_ofFn
    (f := fun i : Fin (clauseCount n m 2 q) =>
      clause P hq ((labelEquiv n m 2 q).symm i))
    (g := fun c j => chain (n * 2 + j * (width 2 q + 1)) c)]
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext i
  simp [indexedChain, formula, SourceClauseEncoding.fromIndexed]

/-- Literal clause order of the actual Boolean-to-three-CNF translation:
at-least-one chains, four pair chains per vertex, and all row-major tuple
chains. Each tuple chain is the actual source-indexed block, not a relabeling. -/
theorem threeCNF_clauses_blocks {n m q : ℕ}
    (P : CSP n m 2 q) (hq : 0 < q) :
    (threeCNF P hq).clauses =
      atLeastChains P ++ pairChains P ++
      (List.ofFn fun r : Fin m =>
        SourceClauseCallback.AllSlots.actualListClauses P hq r
          (List.ofFn fun k : Fin (2 ^ q) => k)).flatten := by
  rw [threeCNF_indexed]
  change (List.ofFn (fun i : Fin (n + (n * 4 + m * 2 ^ q)) =>
      indexedChain P hq i)).flatten = _
  rw [List.ofFn_add]
  simp only [List.flatten_append]
  rw [List.ofFn_add (f := fun i : Fin (n * 4 + m * 2 ^ q) =>
    indexedChain P hq (Fin.natAdd n i))]
  simp only [List.flatten_append]
  rw [List.append_assoc]
  apply congrArg₂ List.append
  · unfold atLeastChains
    apply congrArg List.flatten
    apply congrArg List.ofFn
    funext v
    change indexedChain P hq
      (SourceBooleanPrefix.atLeastIndex (m := m) (q := q) v) = _
    have hslot : (formula P hq).clauses.get
        (Fin.cast (by simp [formula, SourceClauseEncoding.fromIndexed])
          (SourceBooleanPrefix.atLeastIndex (m := m) (q := q) v)) =
        SourceBooleanPrefix.atLeastPayload v := by
      exact SourceBooleanPrefix.atLeast_source_slot P hq v
    simp only [indexedChain]
    rw [hslot]
    simp [SourceBooleanPrefix.base, SourceBooleanPrefix.atLeastIndex,
      SourceBooleanPrefix.atLeastOrdinal, Nat.mul_comm]
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
      let st : Fin 2 × Fin 2 :=
        (finProdFinEquiv : Fin 2 × Fin 2 ≃ Fin 4).symm u
      have hu : u.val = 2 * st.1.val + st.2.val := by
        have h := congrArg Fin.val
          ((finProdFinEquiv : Fin 2 × Fin 2 ≃ Fin 4).apply_symm_apply u)
        simpa only [st, finProdFinEquiv_apply_val, Nat.add_comm,
          Nat.mul_comm] using h.symm
      have hi :
          (Fin.natAdd n (Fin.castLE (by omega)
            (⟨v.val * 4 + u.val, by
              have hv := v.isLt
              have hu' := u.isLt
              nlinarith⟩ : Fin (n * 4))) : Fin (clauseCount n m 2 q)) =
            SourceBooleanPrefix.pairIndex (m := m) (q := q) v st.1 st.2 := by
        apply Fin.ext
        simp only [Fin.val_natAdd, Fin.val_castLE,
          SourceBooleanPrefix.pairIndex, SourceBooleanPrefix.pairOrdinal]
        omega
      rw [hi]
      have hslot : (formula P hq).clauses.get
          (Fin.cast (by simp [formula, SourceClauseEncoding.fromIndexed])
            (SourceBooleanPrefix.pairIndex (m := m) (q := q)
              v st.1 st.2)) =
          SourceBooleanPrefix.pairPayload v st.1 st.2 := by
        exact SourceBooleanPrefix.pair_source_slot P hq v st.1 st.2
      simp only [indexedChain]
      rw [hslot]
      simp only [SourceBooleanPrefix.base, SourceBooleanPrefix.pairIndex,
        SourceBooleanPrefix.pairOrdinal, Fin.val_mk]
      simp only [formula, SourceClauseEncoding.fromIndexed]
      simp only [st]
      rw [Nat.mul_comm n 2]
    · rw [List.ofFn_mul]
      rw [List.flatten_flatten, List.map_ofFn]
      simp only [SourceClauseCallback.AllSlots.actualListClauses,
        List.flatMap, List.map_ofFn, Function.comp_def]
      apply congrArg List.flatten
      apply congrArg List.ofFn
      funext r
      apply congrArg List.flatten
      apply congrArg List.ofFn
      funext k
      have hi :
          (Fin.natAdd n (Fin.natAdd (n * 4)
            (⟨r.val * 2 ^ q + k.val, by
              have hr := r.isLt
              have hk := k.isLt
              nlinarith⟩ : Fin (m * 2 ^ q))) :
              Fin (clauseCount n m 2 q)) =
            (labelEquiv n m 2 q)
              (SourceClauseCallback.SourceLabelBridge.label r k) := by
        apply Fin.ext
        simp only [Fin.val_natAdd]
        rw [SourceClauseCallback.SourceLabelBridge.label,
          SourceClauseRowSchedule.label_slot]
        simp only [SourceClauseRowSchedule.slot]
        omega
      rw [hi]
      rfl

private theorem flatten_ofFn_constant_length {α : Type*} {N c : ℕ}
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

theorem atLeastChains_length {n m q : ℕ} (P : CSP n m 2 q) :
    (atLeastChains P).length = 8 * n := by
  unfold atLeastChains
  apply flatten_ofFn_constant_length
  intro v
  exact SourceBooleanPrefix.atLeast_chain_length v

theorem pairChains_length {n m q : ℕ} (P : CSP n m 2 q) :
    (pairChains P).length = 32 * n := by
  unfold pairChains
  have h : ∀ v : Fin n,
      ((List.ofFn fun u : Fin 4 =>
        let st : Fin 2 × Fin 2 :=
          (finProdFinEquiv : Fin 2 × Fin 2 ≃ Fin 4).symm u
        chain (SourceBooleanPrefix.base n q
          (SourceBooleanPrefix.pairOrdinal v st.1 st.2))
          (SourceBooleanPrefix.pairPayload v st.1 st.2)).flatten).length = 32 := by
    intro v
    convert flatten_ofFn_constant_length
      (f := fun u : Fin 4 =>
        let st : Fin 2 × Fin 2 :=
          (finProdFinEquiv : Fin 2 × Fin 2 ≃ Fin 4).symm u
        chain (SourceBooleanPrefix.base n q
          (SourceBooleanPrefix.pairOrdinal v st.1 st.2))
          (SourceBooleanPrefix.pairPayload v st.1 st.2))
      (c := 8) (by intro u; exact SourceBooleanPrefix.pair_chain_length v _ _) using 1
  exact flatten_ofFn_constant_length _ h

/-- Exact clause count in the actual encoded header: forty Boolean-prefix
three-clauses per vertex, followed by the literal row-block lengths. -/
theorem threeCNF_header_length {n m q : ℕ}
    (P : CSP n m 2 q) (hq : 0 < q) :
    (threeCNF P hq).clauses.length =
      40 * n +
        ((List.ofFn fun r : Fin m =>
          SourceClauseCallback.AllSlots.actualListClauses P hq r
            (List.ofFn fun k : Fin (2 ^ q) => k)).flatten).length := by
  rw [threeCNF_clauses_blocks]
  simp only [List.length_append, atLeastChains_length, pairChains_length]
  omega

theorem countedClauses_blocks {n m q : ℕ}
    (P : CSP n m 2 q) (hq : 0 < q) :
    SourceClauseHeaderCount.countedClauses (formula P hq).clauses =
      40 * n +
        ((List.ofFn fun r : Fin m =>
          SourceClauseCallback.AllSlots.actualListClauses P hq r
            (List.ofFn fun k : Fin (2 ^ q) => k)).flatten).length := by
  rw [← SourceClauseHeaderCount.boolean_clause_count P hq]
  exact threeCNF_header_length P hq


end EthInapproximability.CurrentPaper.TranslatedOrder
