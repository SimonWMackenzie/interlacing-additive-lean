import EthInapproximability.CurrentPaper.SourceCSPRowCodecParser

/-!
# Codec-success converse for the literal CSP query parser

The existing parser bridge establishes soundness from a successful physical
query parse. Here the reverse direction follows the recursive physical query
reader on canonical index fields, including the empty query bank. This lets
the all-input row loop use the same machine for decoder completeness.
-/

namespace EthInapproximability.CurrentPaper.SourceCSPRowCodecConverse

open EncodedCommunication SourceCSPRowController

theorem parse_canonical_from {q : Nat} (i : Fin (q + 1))
    (query : Fin q → Nat) (bank : Bank q) (rest : List Bool)
    (hpast : ∀ j : Fin q, j.val < i.val → bank j = (query j).bits)
    (hfuture : ∀ j : Fin q, i.val ≤ j.val → bank j = []) :
    readQueriesFrom i.val (queriesFrom i.val query ++ rest) bank =
      some ((fun j => (query j).bits), rest) := by
  by_cases hi : i.val < q
  · let j : Fin q := ⟨i.val, hi⟩
    let bank' := Function.update bank j (query j).bits
    have hb : bank j = [] := hfuture j le_rfl
    have hrec := parse_canonical_from
      (⟨i.val + 1, by omega⟩ : Fin (q + 1)) query bank' rest
      (by
        intro k hk
        by_cases he : k = j
        · subst k; exact Function.update_self j (query j).bits bank
        · have hk' : k.val < i.val := by
            have hneq : k.val ≠ i.val := fun h => he (Fin.ext h)
            change k.val < i.val + 1 at hk
            omega
          simpa only [bank', Function.update_of_ne he] using hpast k hk')
      (by
        intro k hk
        have he : k ≠ j := by
          intro he
          subst k
          change i.val + 1 ≤ i.val at hk
          omega
        simpa only [bank', Function.update_of_ne he] using hfuture k (by
          change i.val + 1 ≤ k.val at hk
          omega))
    rw [readQueriesFrom.eq_1, dif_pos hi]
    rw [queriesFrom.eq_1, dif_pos hi]
    simp only [List.append_assoc, readNat_append,
      Bind.bind, Option.bind]
    have hbank' : Function.update bank ⟨i.val, hi⟩
        ((query ⟨i.val, hi⟩).bits ++ bank ⟨i.val, hi⟩) = bank' := by
      simp [bank', j, hb]
    rw [hbank']
    exact hrec
  · have he : i = Fin.last q := Fin.ext (by change i.val = q; omega)
    have hbank : bank = fun j => (query j).bits := by
      funext j
      exact hpast j (by omega)
    rw [readQueriesFrom.eq_1, dif_neg hi,
      queriesFrom.eq_1, dif_neg hi,
      List.nil_append, hbank]
termination_by q - i.val

theorem parse_canonical_zero {q : Nat} (query : Fin q → Nat)
    (rest : List Bool) :
    readQueriesFrom (q := q) 0 (queriesFrom 0 query ++ rest)
      (fun _ => []) = some ((fun j => (query j).bits), rest) := by
  exact parse_canonical_from (0 : Fin (q + 1)) query
    (fun _ => []) rest (by intro j hj; change j.val < 0 at hj; omega)
    (by intros; rfl)

/-- Every successful codec row yields a successful physical query parse,
the exact row query-coordinate bank, and enough suffix bits for the table. -/
theorem readRow_to_parse {n a q : Nat} (input suffix : List Bool)
    (row : SourceCSPCodec.Row n a q)
    (hread : SourceCSPCodec.readRow n a q input = some (row, suffix)) :
    ∃ rest : List Bool,
      readQueriesFrom (q := q) 0 input (fun _ => []) =
        some ((fun j => (row.1 j).val.bits), rest) ∧
      a ^ q ≤ rest.length ∧
      rest.drop (a ^ q) = suffix ∧
      (∀ j : Fin q,
        bitsValue ((row.1 j).val.bits) < n) := by
  have hsource := SourceCSPCodec.readRow_sound hread
  let query : Fin q → Nat := fun j => (row.1 j).val
  let rest := List.ofFn row.2 ++ suffix
  have hfields : SourceCSPCodec.rowFields row =
      queriesFrom 0 query ++ List.ofFn row.2 := by
    exact rowFields_eq row
  have hparse : readQueriesFrom (q := q) 0 input (fun _ => []) =
      some ((fun j => (query j).bits), rest) := by
    rw [← hsource, hfields, List.append_assoc]
    exact parse_canonical_zero query rest
  refine ⟨rest, hparse, ?_, ?_, ?_⟩
  · simp [rest]
  · simp [rest]
  · intro j
    simpa only [bitsValue_bits] using (row.1 j).isLt

end EthInapproximability.CurrentPaper.SourceCSPRowCodecConverse
