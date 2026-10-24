import EthInapproximability.CurrentPaper.SourceListEncoding

/-!
# Exact framing invariants for ordered source lists

Source: frozen v8 `06-eth.tex`, the ordered list produced by sparsification
and gap reductions. These are codec invariants consumed by the separate
literal list machine, not operational runtime assertions.
-/

namespace EthInapproximability.CurrentPaper.SourceListMachineSemantics

open EncodedCommunication SourceListEncoding

theorem readFields_sound {n : ℕ} {input rest : List Bool} {xs : List (List Bool)}
    (h : readFields n input = some (xs,rest)) :
    xs.length = n ∧ fields xs ++ rest = input := by
  induction n generalizing input xs rest with
  | zero =>
      simp only [readFields, Option.some.injEq, Prod.mk.injEq] at h
      rcases h with ⟨rfl,rfl⟩
      exact ⟨rfl,rfl⟩
  | succ n ih =>
      cases hn : readNat input with
      | none => simp [readFields, hn] at h
      | some pair =>
        rcases pair with ⟨len,tail⟩
        by_cases hfit : len ≤ tail.length
        · cases ht : readFields n (tail.drop len) with
          | none => simp [readFields, hn, hfit, ht] at h
          | some pair =>
            rcases pair with ⟨ys,suffix⟩
            simp [readFields, hn, hfit, ht] at h
            rcases h with ⟨rfl,rfl⟩
            obtain ⟨hlen,hfields⟩ := ih ht
            refine ⟨by simp [hlen], ?_⟩
            have htake : (tail.take len).length = len := List.length_take_of_le hfit
            calc
              fields (tail.take len :: ys) ++ suffix =
                  natField len ++ (tail.take len ++ (fields ys ++ suffix)) := by
                    simp only [fields, htake, List.append_assoc]
              _ = natField len ++ tail := by rw [hfields, List.take_append_drop]
              _ = input := readNat_sound hn
        · simp [readFields, hn, hfit] at h

theorem decode_sound {input : List Bool} {xs : List (List Bool)}
    (h : decode input = some xs) : encode xs = input := by
  cases hn : readNat input with
  | none => simp [decode, hn] at h
  | some pair =>
    rcases pair with ⟨n,tail⟩
    cases hr : readFields n tail with
    | none => simp [decode, hn, hr] at h
    | some pair =>
      rcases pair with ⟨ys,rest⟩
      by_cases he : rest = []
      · subst rest
        simp [decode, hn, hr] at h
        subst xs
        obtain ⟨hlen,hfields⟩ := readFields_sound hr
        simp only [List.append_nil] at hfields
        rw [encode, hlen, hfields]
        exact readNat_sound hn
      · simp [decode, hn, hr, he] at h

theorem decode_eq_some_iff (input : List Bool) (xs : List (List Bool)) :
    decode input = some xs ↔ encode xs = input := by
  constructor
  · exact decode_sound
  · intro h
    rw [← h, SourceListEncoding.decode_encode]

theorem natField_length_pos (n : ℕ) : 0 < (natField n).length := by
  simp only [natField, field_length]
  omega

theorem count_le_fields_length (xs : List (List Bool)) : xs.length ≤ (fields xs).length := by
  induction xs with
  | nil => simp [fields]
  | cons x xs ih =>
    have hn := natField_length_pos x.length
    simp only [fields, List.length_append, List.length_cons]
    omega

theorem totalLength_le_fields_length (xs : List (List Bool)) :
    totalLength xs ≤ (fields xs).length := by
  induction xs with
  | nil => simp [fields, totalLength]
  | cons x xs ih =>
    simp only [fields, List.length_append, totalLength, List.map_cons, List.sum_cons] at *
    omega

def result (f : List Bool → List Bool) (input : List Bool) : List Bool :=
  match decode input with
  | none => []
  | some xs => encode (xs.map f)

theorem result_encode (f : List Bool → List Bool) (xs : List (List Bool)) :
    result f (encode xs) = encode (xs.map f) := by
  simp only [result, SourceListEncoding.decode_encode]

theorem empty_list_code : encode [] = [false] := rfl

theorem invalid_empty (f : List Bool → List Bool) : result f [] = [] := rfl

end EthInapproximability.CurrentPaper.SourceListMachineSemantics
