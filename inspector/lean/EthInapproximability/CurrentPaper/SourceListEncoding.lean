import EthInapproximability.CurrentPaper.EncodedGraph

/-!
# Ordered lists of bit strings

Source: frozen v8 `06-eth.tex`, ordered output graph lists. Both the number
of strings and each payload length are canonically encoded. This is a codec,
not an implementation or time bound in the finite-stack machine model.
-/

namespace EthInapproximability.CurrentPaper.SourceListEncoding

open EncodedCommunication

def fields : List (List Bool) → List Bool
  | [] => []
  | bits :: rest => natField bits.length ++ bits ++ fields rest

def encode (xs : List (List Bool)) : List Bool := natField xs.length ++ fields xs

def readFields : ℕ → List Bool → Option (List (List Bool) × List Bool)
  | 0, bits => some ([], bits)
  | n + 1, bits => do
      let (count, tail) ← readNat bits
      if count ≤ tail.length then
        let (xs, rest) ← readFields n (tail.drop count)
        pure (tail.take count :: xs, rest)
      else none

def decode (bits : List Bool) : Option (List (List Bool)) := do
  let (count, tail) ← readNat bits
  let (xs, rest) ← readFields count tail
  if rest = [] then some xs else none

theorem readFields_append (xs : List (List Bool)) (rest : List Bool) :
    readFields xs.length (fields xs ++ rest) = some (xs, rest) := by
  induction xs with
  | nil => simp [fields, readFields]
  | cons x xs ih =>
      simp [fields, readFields, List.append_assoc, readNat_append, ih]

theorem decode_encode (xs : List (List Bool)) : decode (encode xs) = some xs := by
  have hread := readFields_append xs []
  simp only [List.append_nil] at hread
  have hnat := readNat_append xs.length (fields xs)
  simp [decode, encode, hnat, hread]

theorem encode_injective : Function.Injective encode := by
  intro xs ys h
  have := congrArg decode h
  simpa only [decode_encode, Option.some.injEq] using this

def totalLength (xs : List (List Bool)) : ℕ := (xs.map List.length).sum

theorem fields_length (xs : List (List Bool)) :
    (fields xs).length ≤ 3 * totalLength xs + xs.length := by
  induction xs with
  | nil => simp [fields, totalLength]
  | cons x xs ih =>
      have h := EncodedGraph.natField_length_upper x.length
      simp only [fields, List.length_append, totalLength, List.map_cons,
        List.sum_cons, List.length_cons] at *
      omega

theorem encode_length (xs : List (List Bool)) :
    (encode xs).length ≤ 3 * totalLength xs + 3 * xs.length + 1 := by
  have h := EncodedGraph.natField_length_upper xs.length
  have hfields := fields_length xs
  simp only [encode, List.length_append]
  omega

theorem totalLength_map_le {α : Type*} (xs : List α) (f : α → List Bool) (L : ℕ)
    (h : ∀ x ∈ xs, (f x).length ≤ L) : totalLength (xs.map f) ≤ xs.length * L := by
  induction xs with
  | nil => simp [totalLength]
  | cons x xs ih =>
      have hx := h x (by simp)
      have ht := ih (fun y hy => h y (by simp [hy]))
      simp only [totalLength, List.map_cons, List.sum_cons, List.length_cons] at *
      nlinarith

theorem encode_map_length_le {α : Type*} (xs : List α) (f : α → List Bool) (L : ℕ)
    (h : ∀ x ∈ xs, (f x).length ≤ L) :
    (encode (xs.map f)).length ≤ 3 * xs.length * (L + 1) + 1 := by
  have ht := totalLength_map_le xs f L h
  have he := encode_length (xs.map f)
  simp only [List.length_map] at he
  nlinarith

end EthInapproximability.CurrentPaper.SourceListEncoding
