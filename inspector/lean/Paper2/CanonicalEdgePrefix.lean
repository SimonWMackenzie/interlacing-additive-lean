import Paper2.CanonicalEdgeTape

/-! A charged fixed-controller prefix scan of the internal unary endpoint
tape. The consumed number of fields is 2(e+1), supplied on a unary count
bank; the original graph tape must be copied/restored by its caller. -/

namespace Paper2.CanonicalEdgePrefix

open Paper2.CanonicalEdgeTape
open Paper2.UnaryFieldListParserScratch

def selectedPrefix {n m : Nat} (edge : Fin m → Bool → Fin n) (e : Fin m) :
    List (Fin n) :=
  (fields edge).take (2 * (e.val + 1))

def suffix {n m : Nat} (edge : Fin m → Bool → Fin n) (e : Fin m) :
    List (Fin n) :=
  (fields edge).drop (2 * (e.val + 1))

theorem prefix_length {n m : Nat} (edge : Fin m → Bool → Fin n)
    (e : Fin m) :
    (selectedPrefix edge e).length = 2 * (e.val + 1) := by
  simp [selectedPrefix, fields_length]

theorem word_split {n m : Nat} (edge : Fin m → Bool → Fin n)
    (e : Fin m) :
    word edge = tokens (selectedPrefix edge e) ++ tokens (suffix edge e) := by
  simp only [word, selectedPrefix, suffix, tokens, ← List.flatMap_append,
    List.take_append_drop]

theorem physical_prefix_parse {n m : Nat} (edge : Fin m → Bool → Fin n)
    (e : Fin m) :
    run (fuel n (2 * (e.val + 1)) (word edge))
      (initial n (2 * (e.val + 1)) (word edge)) =
    cfg none none (tokens (suffix edge e)) (List.replicate n true) [] []
      (tokens (selectedPrefix edge e).reverse) [true] := by
  have hrun := run_valid_fuel (selectedPrefix edge e) (tokens (suffix edge e))
  rw [prefix_length] at hrun
  rw [← word_split edge e] at hrun
  exact hrun

theorem clock_eq {n m : Nat} (edge : Fin m → Bool → Fin n)
    (e : Fin m) :
    fuel n (2 * (e.val + 1)) (word edge) =
      3 * ((word edge).length + n + 2 * (e.val + 1)) + 2 := rfl

end Paper2.CanonicalEdgePrefix
