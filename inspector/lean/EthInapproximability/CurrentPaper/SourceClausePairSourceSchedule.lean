import EthInapproximability.CurrentPaper.SourceClauseOrderDecomposition
import EthInapproximability.CurrentPaper.SourceClausePrefixPairOrdinal

/-!
The exact second source block for Boolean alphabet two. This module certifies
the bytes and source order that a future physical pair callback must emit;
it makes no machine-run claim.
-/

namespace EthInapproximability.CurrentPaper.SourceBooleanPrefix.PairSourceSchedule

open SourceBooleanEncoding SourceClauseEncoding EncodedCNF
open EthInapproximability.CurrentPaper.SourceOrderDecomposition

def coords {n : Nat} (i : Fin (n * 4)) :
    Fin n × (Fin 2 × Fin 2) := pairCoords i

def pairChain (n q : Nat) (i : Fin (n * 4)) : List Clause :=
  let z := coords i
  chain (base n q (n + i.val)) (pairPayload z.1 z.2.1 z.2.2)

def pairWord (n q : Nat) (i : Fin (n * 4)) : List Bool :=
  (clauseFields (pairChain n q i)).reverse

theorem payload_signs {n : Nat} (v : Fin n) (s t : Fin 2) :
    pairPayload v s t =
      [⟨bitIndex v s, decide (s = t)⟩,
       SourceBooleanEncoding.negative (bitIndex v t)] := by
  by_cases h : s = t
  · subst t
    simp [pairPayload, SourceBooleanEncoding.positive,
      SourceBooleanEncoding.negative]
  · simp [pairPayload, h, SourceBooleanEncoding.negative]

def pairClauses (n q : Nat) : List Clause :=
  (List.ofFn (pairChain n q)).flatten

def pairWords (n q : Nat) : List Bool :=
  (clauseFields (pairClauses n q)).reverse

theorem ordinal (n : Nat) (i : Fin (n * 4)) :
    pairOrdinal (coords i).1 (coords i).2.1 (coords i).2.2 =
      n + i.val := by
  simp only [pairOrdinal, coords]
  rw [pairCoords_ordinal i]
  omega

theorem chain_source {n m q : Nat} (P : CSP n m 2 q)
    (hq : 0 < q) (i : Fin (n * 4)) :
    SourceClauseWriter.slotClauses P hq
      ((formula P hq).clauses[pairIndex (m := m) (q := q)
        (coords i).1 (coords i).2.1 (coords i).2.2],
        (pairIndex (m := m) (q := q)
          (coords i).1 (coords i).2.1 (coords i).2.2).val) =
      pairChain n q i := by
  rw [pair_source_chain]
  simp only [pairChain]
  rw [ordinal]

theorem chains_source {n m q : Nat} (P : CSP n m 2 q)
    (hq : 0 < q) :
    (List.ofFn (fun i : Fin (n * 4) =>
      SourceClauseWriter.slotClauses P hq
        ((formula P hq).clauses[pairIndex (m := m) (q := q)
          (coords i).1 (coords i).2.1 (coords i).2.2],
          (pairIndex (m := m) (q := q)
            (coords i).1 (coords i).2.1 (coords i).2.2).val))).flatten =
      pairClauses n q := by
  have hf : (fun i : Fin (n * 4) =>
      SourceClauseWriter.slotClauses P hq
        ((formula P hq).clauses[pairIndex (m := m) (q := q)
          (coords i).1 (coords i).2.1 (coords i).2.2],
          (pairIndex (m := m) (q := q)
            (coords i).1 (coords i).2.1 (coords i).2.2).val)) =
      pairChain n q := by
    funext i
    exact chain_source P hq i
  simp only [pairClauses, hf]

theorem pairChain_length (n q : Nat) (i : Fin (n * 4)) :
    (pairChain n q i).length = 8 := by
  have h := pair_chain_length (q := q) (coords i).1
    (coords i).2.1 (coords i).2.2
  simpa only [pairChain, ← ordinal n i] using h

theorem pairClauses_length (n q : Nat) :
    (pairClauses n q).length = 8 * (n * 4) := by
  simp only [pairClauses, List.length_flatten, List.map_ofFn,
    List.sum_ofFn]
  simp [pairChain_length]
  omega

theorem pairClauses_length_32 (n q : Nat) :
    (pairClauses n q).length = 32 * n := by
  rw [pairClauses_length]
  omega

theorem pairWords_zero (q : Nat) : pairWords 0 q = [] := by
  simp [pairWords, pairClauses, clauseFields]

theorem pairClauses_zero (q : Nat) : pairClauses 0 q = [] := by
  simp [pairClauses]

def word (n q k : Nat) : List Bool :=
  if h : k < n * 4 then pairWord n q ⟨k, h⟩ else []

def savedAt (n q : Nat) (saved : List Bool) : Nat → List Bool
  | 0 => saved
  | k + 1 => word n q k ++ savedAt n q saved k

def countAt (count : List Bool) (k : Nat) : List Bool :=
  List.replicate (8 * k) true ++ count

def prefixFields (n q k : Nat) : List Bool :=
  (List.range k).flatMap (fun j => (word n q j).reverse)

theorem savedAt_eq_prefix (n q k : Nat) (saved : List Bool) :
    savedAt n q saved k = (prefixFields n q k).reverse ++ saved := by
  induction k with
  | zero => simp [savedAt, prefixFields]
  | succ k ih =>
      rw [savedAt, ih]
      simp only [prefixFields, List.range_succ, List.flatMap_append,
        List.flatMap_singleton, List.reverse_append, List.reverse_reverse]
      simp [List.append_assoc]

theorem countAt_next (count : List Bool) (k : Nat) :
    countAt count (k + 1) = List.replicate 8 true ++ countAt count k := by
  unfold countAt
  rw [show 8 * (k + 1) = 8 + 8 * k by omega,
    List.replicate_add, List.append_assoc]

theorem countAt_final (n : Nat) (count : List Bool) :
    countAt count (n * 4) = List.replicate (32 * n) true ++ count := by
  simp only [countAt, show 8 * (n * 4) = 32 * n by omega]

theorem prefixFields_production {n m q : Nat}
    (P : CSP n m 2 q) (hq : 0 < q) :
    prefixFields n q (n * 4) =
      (List.range (n * 4)).flatMap (fun k =>
        if h : k < n * 4 then
          clauseFields (SourceClauseWriter.slotClauses P hq
            ((formula P hq).clauses[pairIndex (m := m) (q := q)
              (coords (⟨k, h⟩ : Fin (n * 4))).1
              (coords (⟨k, h⟩ : Fin (n * 4))).2.1
              (coords (⟨k, h⟩ : Fin (n * 4))).2.2],
              (pairIndex (m := m) (q := q)
                (coords (⟨k, h⟩ : Fin (n * 4))).1
                (coords (⟨k, h⟩ : Fin (n * 4))).2.1
                (coords (⟨k, h⟩ : Fin (n * 4))).2.2).val))
        else []) := by
  simp only [prefixFields]
  congr 1
  funext k
  by_cases h : k < n * 4
  · simp only [word, pairWord, List.reverse_reverse, dif_pos h]
    rw [chain_source P hq ⟨k, h⟩]
  · simp [word, h]

theorem zero_source (q : Nat) :
    prefixFields 0 q 0 = [] ∧ savedAt 0 q [] 0 = [] ∧
      countAt [] 0 = [] := by
  simp [prefixFields, savedAt, countAt]

end EthInapproximability.CurrentPaper.SourceBooleanPrefix.PairSourceSchedule
