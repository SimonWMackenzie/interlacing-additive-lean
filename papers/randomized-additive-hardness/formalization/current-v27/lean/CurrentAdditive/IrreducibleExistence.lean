import Mathlib

/-!
Existence of a monic irreducible binary polynomial of each positive degree.
This is a mathematical existence result; the primitive element is selected
noncomputably, so this does not implement the manuscript's degree-d search.
-/

namespace CurrentAdditive.FiniteFieldConstructor

theorem exists_binary_irreducible (d : ℕ) (hd : 0 < d) :
    ∃ f : Polynomial (ZMod 2), f.Monic ∧ Irreducible f ∧ f.natDegree = d := by
  let F := GaloisField 2 d
  letI : Fintype F := Fintype.ofFinite F
  obtain ⟨α, hα⟩ := Field.exists_primitive_element_of_finite_bot (ZMod 2) F
  refine ⟨minpoly (ZMod 2) α, ?_, ?_, ?_⟩
  · exact minpoly.monic (IsIntegral.of_finite (ZMod 2) α)
  · exact minpoly.irreducible (IsIntegral.of_finite (ZMod 2) α)
  · calc
      (minpoly (ZMod 2) α).natDegree = Module.finrank (ZMod 2) F :=
        (Field.primitive_element_iff_minpoly_natDegree_eq (ZMod 2) α).mp hα
      _ = d := GaloisField.finrank 2 (Nat.ne_of_gt hd)

#print axioms exists_binary_irreducible

end CurrentAdditive.FiniteFieldConstructor
