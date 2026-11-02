import CurrentAdditive.StreamingPrinter

/-!
The streaming implementation prints the same powers and dots as the direct
equation `bit j = dot x (y^j)` in BitPrinter. This comparison uses only the
recursion defining powers, with no field algebra assumptions.
-/

namespace CurrentAdditive.FiniteFieldConstructor.StreamingEquivalence

open CurrentAdditive.FiniteFieldConstructor.BitPrinter

def expected (d modulus x y j : ℕ) : ℕ → List Bool
  | 0 => []
  | n + 1 => bit d modulus x y j :: expected d modulus x y (j + 1) n

theorem run_expected (d modulus x y n j : ℕ) (acc : List Bool) :
    (StreamingPrinter.run d modulus x y n (power d modulus y j) acc).1 =
      acc.reverse ++ expected d modulus x y j n := by
  induction n generalizing j acc with
  | zero => simp [StreamingPrinter.run, expected]
  | succ n ih =>
      change (StreamingPrinter.run d modulus x y n
          (power d modulus y (j + 1))
          (dot d x (power d modulus y j) :: acc)).1 =
        acc.reverse ++ expected d modulus x y j (n + 1)
      rw [ih]
      simp [expected, bit, List.reverse_cons, List.append_assoc]

theorem expected_eq_direct (d modulus x y j n : ℕ) :
    expected d modulus x y j n =
      (List.range n).map (fun k => bit d modulus x y (j + k)) := by
  induction n generalizing j with
  | zero => simp [expected]
  | succ n ih =>
      rw [expected, List.range_succ_eq_map]
      simp only [List.map_cons, List.map_map, Nat.add_zero]
      rw [ih]
      congr 1
      apply List.map_congr_left
      intro k hk
      congr 1
      omega

theorem streaming_eq_direct (d modulus n x y : ℕ) :
    StreamingPrinter.word d modulus n x y =
      BitPrinter.word d modulus n x y := by
  unfold StreamingPrinter.word BitPrinter.word
  simpa using (run_expected d modulus x y n 0 []).trans
    (expected_eq_direct d modulus x y 0 n)

#print axioms run_expected
#print axioms expected_eq_direct
#print axioms streaming_eq_direct

end CurrentAdditive.FiniteFieldConstructor.StreamingEquivalence
