import CurrentAdditive.CodeDPairProductTargetV2

/-!
The ordered sequence of physical multiply requests in one append step.
An indexed source position is the outer loop; a distinct alphabet position
is the inner loop, including duplicate decoded labels.
-/

namespace CurrentAdditive.CodeDAppendOperandsV2

open CodeDCodec CodeDSourceCodecV2 CodeDCanonicalSourceV2
open CodeDPairProductTargetV2

def rawAlphabet (alphabet : Array (Nat × ℚ)) : List (Nat × RawRat) :=
  alphabet.toList.map (fun y => (y.1, rawOfRat y.2))

def operands {q : Nat} (source : Array ((Fin q → Nat) × ℚ))
    (alphabet : Array (Nat × ℚ)) : List (Entry × (Nat × RawRat)) :=
  (canonicalSource source).flatMap (fun x =>
    (rawAlphabet alphabet).map (fun y => (x, y)))

def packets {q : Nat} (source : Array ((Fin q → Nat) × ℚ))
    (alphabet : Array (Nat × ℚ)) : List (List Bool) :=
  (operands source alphabet).map (fun p => pairBytes p.1.weight p.2.2)

theorem rawAlphabet_length (alphabet : Array (Nat × ℚ)) :
    (rawAlphabet alphabet).length = alphabet.size := by
  simp [rawAlphabet]

private theorem flatMap_pair_length {α β : Type*} (xs : List α) (ys : List β) :
    (xs.flatMap (fun x => ys.map (fun y => (x, y)))).length = xs.length * ys.length := by
  induction xs with
  | nil => simp
  | cons x rest ih =>
      simp only [List.flatMap_cons, List.length_append, List.length_map,
        List.length_cons, ih, Nat.succ_mul]
      omega

theorem operands_length {q : Nat}
    (source : Array ((Fin q → Nat) × ℚ))
    (alphabet : Array (Nat × ℚ)) :
    (operands source alphabet).length = source.size * alphabet.size := by
  rw [operands, flatMap_pair_length]
  simp [canonicalSource, rawAlphabet]

theorem packets_length {q : Nat}
    (source : Array ((Fin q → Nat) × ℚ))
    (alphabet : Array (Nat × ℚ)) :
    (packets source alphabet).length = source.size * alphabet.size := by
  simp [packets, operands_length]

theorem operands_valid {q : Nat}
    (source : Array ((Fin q → Nat) × ℚ))
    (alphabet : Array (Nat × ℚ)) :
    ∀ p ∈ operands source alphabet,
      p.1.weight.Valid ∧ p.2.2.Valid := by
  intro p hp
  obtain ⟨x, hx, hpmap⟩ := List.mem_flatMap.mp hp
  obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hpmap
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hx
  obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hy
  exact ⟨canonicalEntry_valid a, rawOfRat_valid b.2⟩

private theorem weight_row {q : Nat} (x : (Fin q → Nat) × ℚ)
    (ys : List (Nat × ℚ)) :
    ((ys.map (fun y => (y.1, rawOfRat y.2))).map
      (fun y => (canonicalEntry x, y))).map
        (fun p => p.1.weight.value * p.2.2.value) =
      (ys.map (fun y => (SequentialCode.appendWord x.1 y.1, x.2*y.2))).map Prod.snd := by
  simp [List.map_map, canonicalEntry, rawOfRat_value]

theorem operand_weights_match_append {q : Nat}
    (source : Array ((Fin q → Nat) × ℚ))
    (alphabet : Array (Nat × ℚ)) :
    (operands source alphabet).map
      (fun p => p.1.weight.value * p.2.2.value) =
    (CodeDAppendTargetV2.appendedList source alphabet).map Prod.snd := by
  unfold operands CodeDAppendTargetV2.appendedList canonicalSource rawAlphabet
  induction source.toList with
  | nil => simp
  | cons x xs ih =>
      simp only [List.map_cons, List.flatMap_cons, List.map_append]
      rw [weight_row x alphabet.toList, ih]

#print axioms operands_length
#print axioms operands_valid
#print axioms operand_weights_match_append

end CurrentAdditive.CodeDAppendOperandsV2
