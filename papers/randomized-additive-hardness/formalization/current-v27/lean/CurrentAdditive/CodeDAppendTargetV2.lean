import CurrentAdditive.CodeDTargetV2

/-!
Ordered append target for one actual `SequentialCode.appendSource` step.
The physical constructor must traverse source indices first, alphabet indices
second, multiply the two rational weights, and serialize the resulting word
with the new symbol at the final coordinate.
-/

namespace CurrentAdditive.CodeDAppendTargetV2

open SequentialCode CodeDCanonicalSourceV2 CodeDSourceCodecV2

def appendedList {q : Nat} (source : Array ((Fin q → Nat) × ℚ))
    (alphabet : Array (Nat × ℚ)) :
    List ((Fin (q + 1) → Nat) × ℚ) :=
  source.toList.flatMap (fun x =>
    alphabet.toList.map (fun y => (appendWord x.1 y.1, x.2 * y.2)))

private theorem foldl_append_order {q : Nat}
    (xs : List ((Fin q → Nat) × ℚ)) (alphabet : Array (Nat × ℚ))
    (acc : Array ((Fin (q + 1) → Nat) × ℚ)) :
    (xs.foldl (fun out x =>
      out ++ alphabet.map (fun y => (appendWord x.1 y.1, x.2 * y.2))) acc).toList =
      acc.toList ++ xs.flatMap (fun x =>
        alphabet.toList.map (fun y => (appendWord x.1 y.1, x.2 * y.2))) := by
  induction xs generalizing acc with
  | nil => simp
  | cons x xs ih =>
      simp only [List.foldl_cons, List.flatMap_cons]
      rw [ih]
      simp [Array.toList_append, List.append_assoc]

theorem appendSource_order {q : Nat}
    (source : Array ((Fin q → Nat) × ℚ))
    (alphabet : Array (Nat × ℚ)) :
    (appendSource source alphabet).toList = appendedList source alphabet := by
  unfold appendSource appendedList
  rw [← Array.foldl_toList]
  simpa using foldl_append_order source.toList alphabet (#[])

theorem appendSource_canonical_order {q : Nat}
    (source : Array ((Fin q → Nat) × ℚ))
    (alphabet : Array (Nat × ℚ)) :
    canonicalSource (appendSource source alphabet) =
      (appendedList source alphabet).map canonicalEntry := by
  rw [canonicalSource, appendSource_order]

theorem appendSource_encoded_order {q : Nat}
    (source : Array ((Fin q → Nat) × ℚ))
    (alphabet : Array (Nat × ℚ)) :
    encodedSource (appendSource source alphabet) =
      encodeSource ((appendedList source alphabet).map canonicalEntry) := by
  rw [encodedSource, appendSource_canonical_order]

#print axioms appendSource_order
#print axioms appendSource_encoded_order

end CurrentAdditive.CodeDAppendTargetV2
