import EthInapproximability.CurrentPaper.SourceClauseBooleanPrefix
import EthInapproximability.CurrentPaper.SourceClauseRowSchedule

/-! Exact three-block occurrence order of the source Boolean clause list. -/

namespace EthInapproximability.CurrentPaper.SourceOrderDecomposition

open SourceBooleanEncoding SourceClauseEncoding EncodedCNF

def pairCoords {n : Nat} (i : Fin (n * 4)) : Fin n × (Fin 2 × Fin 2) :=
  let z : Fin n × Fin 4 := (finProdFinEquiv : Fin n × Fin 4 ≃ Fin (n * 4)).symm i
  let st : Fin 2 × Fin 2 :=
    (finProdFinEquiv : Fin 2 × Fin 2 ≃ Fin 4).symm z.2
  (z.1, st)

def rowCoords {m q : Nat} (i : Fin (m * 2 ^ q)) :
    Fin m × Fin (2 ^ q) :=
  (finProdFinEquiv : Fin m × Fin (2 ^ q) ≃ Fin (m * 2 ^ q)).symm i

def pairLabel {n m q : Nat} (i : Fin (n * 4)) :
    ClauseLabel n m 2 q :=
  let z := pairCoords i
  .inr (.inl (z.1, z.2.1, z.2.2))

def rowLabel {n m q : Nat} (i : Fin (m * 2 ^ q)) :
    ClauseLabel n m 2 q :=
  let z := rowCoords i
  .inr (.inr (z.1, SourceClauseRowSchedule.tuple 2 q z.2))

def atLeastList {n m q : Nat} (_P : CSP n m 2 q) :
    List (List Literal) :=
  List.ofFn (fun v : Fin n => SourceBooleanPrefix.atLeastPayload v)

def pairList {n m q : Nat} (_P : CSP n m 2 q) :
    List (List Literal) :=
  List.ofFn (fun i : Fin (n * 4) =>
    let z := pairCoords i
    SourceBooleanPrefix.pairPayload z.1 z.2.1 z.2.2)

def rowList {n m q : Nat} (P : CSP n m 2 q) (hq : 0 < q) :
    List (List Literal) :=
  List.ofFn (fun i : Fin (m * 2 ^ q) => clause P hq (rowLabel i))

theorem pairCoords_ordinal {n : Nat} (i : Fin (n * 4)) :
    i.val = 4 * (pairCoords i).1.val +
      2 * (pairCoords i).2.1.val + (pairCoords i).2.2.val := by
  let z : Fin n × Fin 4 :=
    (finProdFinEquiv : Fin n × Fin 4 ≃ Fin (n * 4)).symm i
  let st : Fin 2 × Fin 2 :=
    (finProdFinEquiv : Fin 2 × Fin 2 ≃ Fin 4).symm z.2
  have hi : (finProdFinEquiv z).val = i.val :=
    congrArg Fin.val ((finProdFinEquiv : Fin n × Fin 4 ≃ Fin (n * 4)).apply_symm_apply i)
  have hz : (finProdFinEquiv st).val = z.2.val :=
    congrArg Fin.val ((finProdFinEquiv : Fin 2 × Fin 2 ≃ Fin 4).apply_symm_apply z.2)
  simp only [finProdFinEquiv_apply_val] at hi hz
  change i.val = 4 * z.1.val + 2 * st.1.val + st.2.val
  omega

theorem rowCoords_ordinal {m q : Nat} (i : Fin (m * 2 ^ q)) :
    i.val = (rowCoords i).1.val * 2 ^ q + (rowCoords i).2.val := by
  have hi := congrArg Fin.val
    ((finProdFinEquiv : Fin m × Fin (2 ^ q) ≃ Fin (m * 2 ^ q)).apply_symm_apply i)
  simpa only [rowCoords, finProdFinEquiv_apply_val,
    Nat.add_comm, Nat.mul_comm] using hi.symm

theorem pairLabel_ordinal {n m q : Nat} (i : Fin (n * 4)) :
    ((labelEquiv n m 2 q) (pairLabel (m := m) (q := q) i)).val = n + i.val := by
  change ((labelEquiv n m 2 q)
    (.inr (.inl ((pairCoords i).1, (pairCoords i).2.1,
      (pairCoords i).2.2)))).val = n + i.val
  rw [SourceBooleanPrefix.pair_label]
  simp only [SourceBooleanPrefix.pairIndex,
    SourceBooleanPrefix.pairOrdinal, Fin.val_mk]
  rw [pairCoords_ordinal i]
  omega

theorem rowLabel_ordinal {n m q : Nat} (i : Fin (m * 2 ^ q)) :
    ((labelEquiv n m 2 q) (rowLabel (n := n) i)).val =
      n + n * 4 + i.val := by
  change ((labelEquiv n m 2 q)
    (.inr (.inr ((rowCoords i).1,
      SourceClauseRowSchedule.tuple 2 q (rowCoords i).2)))).val = _
  rw [SourceClauseRowSchedule.label_slot]
  simp only [SourceClauseRowSchedule.slot]
  rw [rowCoords_ordinal i]
  omega

/-- The actual original Boolean clause list is the exact concatenation of
all at-least-one occurrences, all ordered pair occurrences including the
diagonal tautologies, and all row-major tuple occurrences. -/
theorem formula_clauses_ordered {n m q : Nat}
    (P : CSP n m 2 q) (hq : 0 < q) :
    (formula P hq).clauses =
      atLeastList P ++ pairList P ++ rowList P hq := by
  let f : Fin (n + (n * 4 + m * 2 ^ q)) → List Literal :=
    fun i => clause P hq ((labelEquiv n m 2 q).symm i)
  have hsource : (formula P hq).clauses = List.ofFn f := by
    rfl
  rw [hsource]
  have hsplit : List.ofFn f =
      List.ofFn (fun i : Fin n => f (Fin.castLE (by omega) i)) ++
      List.ofFn (fun i : Fin (n * 4) =>
        f (Fin.natAdd n (Fin.castLE (by omega) i))) ++
      List.ofFn (fun i : Fin (m * 2 ^ q) =>
        f (Fin.natAdd n (Fin.natAdd (n * 4) i))) := by
    calc
      List.ofFn f =
          List.ofFn (fun i : Fin n => f (Fin.castLE (by omega) i)) ++
          List.ofFn (fun i : Fin (n * 4 + m * 2 ^ q) =>
            f (Fin.natAdd n i)) := List.ofFn_add
      _ = _ := by
        rw [List.ofFn_add (f := fun i : Fin (n * 4 + m * 2 ^ q) =>
          f (Fin.natAdd n i))]
        rw [List.append_assoc]
  rw [hsplit]
  apply congrArg₂ (· ++ ·)
  · apply congrArg₂ (· ++ ·)
    · unfold atLeastList
      congr 1
      funext i
      change clause P hq ((labelEquiv n m 2 q).symm
      (Fin.castLE (by simp [clauseCount]) i)) =
        SourceBooleanPrefix.atLeastPayload i
      have hindex : (Fin.castLE (by simp [clauseCount]) i :
          Fin (clauseCount n m 2 q)) =
          SourceBooleanPrefix.atLeastIndex (m := m) (q := q) i := by
        apply Fin.ext
        rfl
      calc
        clause P hq ((labelEquiv n m 2 q).symm
            (Fin.castLE (by simp [clauseCount]) i)) =
            clause P hq ((labelEquiv n m 2 q).symm
              (SourceBooleanPrefix.atLeastIndex (m := m) (q := q) i)) :=
          congrArg (fun j => clause P hq ((labelEquiv n m 2 q).symm j)) hindex
        _ = SourceBooleanPrefix.atLeastPayload i := by
          rw [← SourceBooleanPrefix.atLeast_label,
            Equiv.symm_apply_apply]
          exact SourceBooleanPrefix.atLeast_clause P hq i
    · unfold pairList
      congr 1
      funext i
      have hindex : (labelEquiv n m 2 q) (pairLabel (m := m) (q := q) i) =
        (Fin.natAdd n (Fin.castLE (by omega) i) :
          Fin (n + (n * 4 + m * 2 ^ q))) := by
        apply Fin.ext
        exact pairLabel_ordinal i
      change clause P hq ((labelEquiv n m 2 q).symm
      (Fin.natAdd n (Fin.castLE (by omega) i))) = _
      rw [← hindex, Equiv.symm_apply_apply]
      exact SourceBooleanPrefix.pair_clause P hq
        (pairCoords i).1 (pairCoords i).2.1 (pairCoords i).2.2
  · unfold rowList
    congr 1
    funext i
    have hindex : (labelEquiv n m 2 q) (rowLabel (n := n) i) =
        (Fin.natAdd n (Fin.natAdd (n * 4) i) :
          Fin (n + (n * 4 + m * 2 ^ q))) := by
      apply Fin.ext
      have h := rowLabel_ordinal (n := n) i
      simp only [Fin.val_natAdd] at *
      omega
    change clause P hq ((labelEquiv n m 2 q).symm
      (Fin.natAdd n (Fin.natAdd (n * 4) i))) = clause P hq (rowLabel i)
    rw [← hindex, Equiv.symm_apply_apply]

/-- The final block is literally row-major: `r=0,...,m-1`, and inside each
row every tuple ordinal `k=0,...,2^q-1`, including accepting tuples. -/
theorem rowList_eq_flatten {n m q : Nat}
    (P : CSP n m 2 q) (hq : 0 < q) :
    rowList P hq =
      (List.ofFn (fun r : Fin m =>
        List.ofFn (fun k : Fin (2 ^ q) =>
          clause P hq (.inr (.inr
            (r, SourceClauseRowSchedule.tuple 2 q k)))))).flatten := by
  unfold rowList
  rw [List.ofFn_mul]
  congr 1
  congr 1
  funext r
  congr 1
  funext k
  have hindex : (⟨r.val * 2 ^ q + k.val, by
      have hk := k.isLt
      have hr := r.isLt
      nlinarith⟩ : Fin (m * 2 ^ q)) =
        (finProdFinEquiv (r, k) : Fin (m * 2 ^ q)) := by
    apply Fin.ext
    simp [finProdFinEquiv_apply_val, Nat.mul_comm, Nat.add_comm]
  simp only [rowLabel, rowCoords, hindex,
    Equiv.symm_apply_apply]

theorem pairList_eq_flatten {n m q : Nat}
    (P : CSP n m 2 q) :
    pairList P =
      (List.ofFn (fun v : Fin n =>
        List.ofFn (fun u : Fin 4 =>
          let st : Fin 2 × Fin 2 :=
            (finProdFinEquiv : Fin 2 × Fin 2 ≃ Fin 4).symm u
          SourceBooleanPrefix.pairPayload v st.1 st.2))).flatten := by
  unfold pairList
  rw [List.ofFn_mul]
  congr 1
  congr 1
  funext v
  congr 1
  funext u
  have hindex : (⟨v.val * 4 + u.val, by
      have hv := v.isLt
      have hu := u.isLt
      nlinarith⟩ : Fin (n * 4)) =
      (finProdFinEquiv (v, u) : Fin (n * 4)) := by
    apply Fin.ext
    simp [finProdFinEquiv_apply_val, Nat.mul_comm, Nat.add_comm]
  simp only [pairCoords, hindex, Equiv.symm_apply_apply]

/-- An explicit three-block list with `n` source at-least-one occurrences,
then `n` consecutive blocks of four pair occurrences, then `m` consecutive
blocks of `2^q` truth-table tuple occurrences. -/
theorem formula_clauses_blocks {n m q : Nat}
    (P : CSP n m 2 q) (hq : 0 < q) :
    (formula P hq).clauses =
      (List.ofFn (fun v : Fin n => SourceBooleanPrefix.atLeastPayload v)) ++
      (List.ofFn (fun v : Fin n =>
        List.ofFn (fun u : Fin 4 =>
          let st : Fin 2 × Fin 2 :=
            (finProdFinEquiv : Fin 2 × Fin 2 ≃ Fin 4).symm u
          SourceBooleanPrefix.pairPayload v st.1 st.2))).flatten ++
      (List.ofFn (fun r : Fin m =>
        List.ofFn (fun k : Fin (2 ^ q) =>
          clause P hq (.inr (.inr
            (r, SourceClauseRowSchedule.tuple 2 q k)))))).flatten := by
  rw [formula_clauses_ordered, pairList_eq_flatten,
    rowList_eq_flatten]
  rfl

theorem formula_clauses_row_major {n m q : Nat}
    (P : CSP n m 2 q) (hq : 0 < q) :
    (formula P hq).clauses = atLeastList P ++ pairList P ++
      (List.ofFn (fun r : Fin m =>
        List.ofFn (fun k : Fin (2 ^ q) =>
          clause P hq (.inr (.inr
            (r, SourceClauseRowSchedule.tuple 2 q k)))))).flatten := by
  rw [formula_clauses_ordered, rowList_eq_flatten]


end EthInapproximability.CurrentPaper.SourceOrderDecomposition
