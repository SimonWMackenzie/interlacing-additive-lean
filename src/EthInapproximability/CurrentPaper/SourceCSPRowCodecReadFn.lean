import EthInapproximability.CurrentPaper.SourceCSPCodec

/-!
# Canonical query-list reader with and without range checking

These lemmas connect the source codec's bounded index reader to its ordinary
canonical-natural reader. They are the semantic half of the raw row parser
bridge; the physical row-controller bank remains a separate obligation.
-/

namespace EthInapproximability.CurrentPaper.SourceCSPRowCodecReadFn

open EncodedCommunication SourceCSPCodec

theorem indexed_to_nat {n q : Nat} {input rest : List Bool}
    {query : Fin q → Fin n}
    (h : readFn (readIndex n) q input = some (query, rest)) :
    readFn readNat q input =
      some ((fun j => (query j).val), rest) := by
  have hs : fnFields (fun v : Fin n => natField v.val) query ++ rest = input :=
    readFn_sound (fun v : Fin n => natField v.val) (readIndex n)
      (fun h => readIndex_sound h) h
  rw [← hs]
  simpa only [fnFields] using
    readFn_append natField readNat readNat_append q
      (fun j => (query j).val) rest

theorem nat_to_index {n q : Nat} {input rest : List Bool}
    {query : Fin q → Nat}
    (h : readFn readNat q input = some (query, rest))
    (hrange : ∀ j : Fin q, query j < n) :
    readFn (readIndex n) q input =
      some ((fun j => (⟨query j, hrange j⟩ : Fin n)), rest) := by
  have hs : fnFields natField query ++ rest = input :=
    readFn_sound natField readNat (fun h => readNat_sound h) h
  rw [← hs]
  simpa only [fnFields] using
    readFn_append (fun v : Fin n => natField v.val)
      (readIndex n) (readIndex_append n) q
      (fun j => (⟨query j, hrange j⟩ : Fin n)) rest

theorem read_bits_total (H : Nat) (input : List Bool)
    (hlen : H ≤ input.length) :
    ∃ table : Fin H → Bool,
      readFn readBit H input = some (table, input.drop H) := by
  induction H generalizing input with
  | zero => exact ⟨Fin.elim0, rfl⟩
  | succ H ih =>
      cases input with
      | nil => simp at hlen
      | cons b tail =>
          obtain ⟨table, ht⟩ := ih tail (by simp at hlen; omega)
          refine ⟨Fin.cases b table, ?_⟩
          simp [readFn, readBit, ht]

end EthInapproximability.CurrentPaper.SourceCSPRowCodecReadFn
