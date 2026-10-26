import Mathlib

/-!
Private component for v27 finite-field list. This file proves the cardinality
and labelled-seed part. The GaloisField type below is existential algebra,
not the manuscript's executable quotient representation.
-/

namespace CurrentAdditive.FiniteFieldConstructor

abbrev BinaryField (d : ℕ) := GaloisField 2 d

noncomputable instance (d : ℕ) : Fintype (BinaryField d) := Fintype.ofFinite _

theorem binaryField_card (d : ℕ) (hd : 0 < d) :
    Fintype.card (BinaryField d) = 2 ^ d := by
  rw [← Nat.card_eq_fintype_card]
  exact GaloisField.card 2 d (Nat.ne_of_gt hd)

abbrev Seed (d : ℕ) := (Fin d → ZMod 2) × BinaryField d

noncomputable def abstractLabels (d : ℕ) : List (Seed d) := Finset.univ.toList

theorem abstractLabels_nodup (d : ℕ) : (abstractLabels d).Nodup := by
  exact Finset.nodup_toList _

theorem mem_abstractLabels (d : ℕ) (seed : Seed d) : seed ∈ abstractLabels d := by
  simp [abstractLabels]

theorem abstractLabels_length (d : ℕ) (hd : 0 < d) :
    (abstractLabels d).length = (2 ^ d) ^ 2 := by
  simp [abstractLabels, Fintype.card_prod, Fintype.card_fin,
    ZMod.card, binaryField_card d hd, pow_two]

#print axioms binaryField_card
#print axioms abstractLabels_length

end CurrentAdditive.FiniteFieldConstructor
