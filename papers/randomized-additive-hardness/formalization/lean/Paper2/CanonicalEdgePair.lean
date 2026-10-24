import Paper2.CanonicalEdgePrefix

namespace Paper2.CanonicalEdgePair

open Paper2.CanonicalEdgeTape Paper2.CanonicalEdgePrefix
open Paper2.UnaryFieldListParserScratch
open Paper2.RecursiveLabelCodecScratch (finCodec)

private theorem ofFn_last_two {α : Type} (N : Nat)
    (f : Fin (N + 2) → α) :
    List.ofFn f =
      List.ofFn (fun i : Fin N => f ⟨i.val, by omega⟩) ++
        [f ⟨N, by omega⟩, f ⟨N + 1, by omega⟩] := by
  change List.ofFn f =
    List.ofFn (fun i : Fin N => f ⟨i.val, by omega⟩) ++
      [f ⟨N, by omega⟩, f ⟨N + 1, by omega⟩]
  rw [List.ofFn_succ' f]
  rw [List.ofFn_succ' (fun i : Fin (N + 1) => f i.castSucc)]
  simp only [List.concat_eq_append, List.append_assoc,
    List.singleton_append]
  congr 1

def preceding {n m : Nat} (edge : Fin m → Bool → Fin n) (e : Fin m) :
    List (Fin n) :=
  (fields edge).take (2 * e.val)

theorem selectedPrefix_pair {n m : Nat} (edge : Fin m → Bool → Fin n)
    (e : Fin m) :
    selectedPrefix edge e = preceding edge e ++
      [edge e false, edge e true] := by
  let f : Fin (2 * (e.val + 1)) → Fin n :=
    fun t => endpointField edge ⟨t.val, by omega⟩
  have hf : selectedPrefix edge e = List.ofFn f := by
    unfold selectedPrefix fields
    rw [← Fin.ofFn_take_eq_take_ofFn (by omega)]
    apply congrArg List.ofFn
    funext i
    rfl
  have hp : preceding edge e =
      List.ofFn (fun i : Fin (2 * e.val) => f ⟨i.val, by omega⟩) := by
    unfold preceding fields
    rw [← Fin.ofFn_take_eq_take_ofFn (by omega)]
    apply congrArg List.ofFn
    funext i
    rfl
  rw [hf, hp]
  have hsize : 2 * (e.val + 1) = 2 * e.val + 2 := by omega
  let f' : Fin (2 * e.val + 2) → Fin n := fun t => f (Fin.cast hsize.symm t)
  change List.ofFn f' = _
  rw [ofFn_last_two]
  simp [f', f, endpoint_even, endpoint_odd]

theorem reversed_pair_front {n m : Nat} (edge : Fin m → Bool → Fin n)
    (e : Fin m) :
    (selectedPrefix edge e).reverse =
      [edge e true, edge e false] ++ (preceding edge e).reverse := by
  rw [selectedPrefix_pair]
  simp

/-- The actual fixed parser's output bank begins with the selected edge's
second and first endpoint tokens, in that order; earlier occurrences follow.
The source is the identical prefix of the physical unary endpoint stream. -/
theorem physical_prefix_pair {n m : Nat} (edge : Fin m → Bool → Fin n)
    (e : Fin m) :
    run (fuel n (2 * (e.val + 1)) (word edge))
      (initial n (2 * (e.val + 1)) (word edge)) =
    cfg none none (tokens (suffix edge e)) (List.replicate n true) [] []
      ((finCodec n).encode (edge e true) ++
        (finCodec n).encode (edge e false) ++
        tokens (preceding edge e).reverse) [true] := by
  rw [physical_prefix_parse]
  rw [reversed_pair_front]
  simp [tokens, List.append_assoc]

#print axioms selectedPrefix_pair
#print axioms reversed_pair_front
#print axioms physical_prefix_pair

end Paper2.CanonicalEdgePair
