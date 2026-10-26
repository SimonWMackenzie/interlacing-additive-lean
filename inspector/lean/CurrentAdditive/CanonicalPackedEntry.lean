import CurrentAdditive.CanonicalPhysicalSelectorDigitFull

namespace CurrentAdditive.FiniteFieldConstructor.CanonicalTable

open CurrentAdditive.SmallBias

/-- The selected address and the incidence position together form an in-range
payload coordinate of the field word. -/
def numericPayloadCoord {v e : ℕ} (b t d : ℕ) (he : e ≤ 2 ^ b)
    (edges : Fin e → Fin (2 ^ t * 2 ^ t) ↪ Fin v)
    (i : Fin (rowCount v b t)) (j : Fin (columnCount b t d)) :
    Fin (2 ^ b * (2 ^ t * 2 ^ t + 1)) := by
  let row := (rowIndex v b t).symm i
  let col := (columnIndex b t d).symm j
  let H := 2 ^ b
  let K := 2 ^ t * 2 ^ t
  let α : Fin H := ⟨row.2.val / H ^ col.1.val % H,
    Nat.mod_lt _ (by positivity)⟩
  let p := position he edges col.2.1 row.1
  exact ⟨α.val * (K + 1) + p.val, by
    have h1 : α.val * (K + 1) + p.val < (α.val + 1) * (K + 1) := by
      rw [Nat.add_mul]
      omega
    exact h1.trans_le (Nat.mul_le_mul_right (K + 1) α.isLt)⟩

/-- The numeric canonical matrix entry is literally a lookup into the packed
field-bit array, at seed label ℓ and the selected payload coordinate. -/
theorem numericEntry_eq_packedFieldBits {v e : ℕ}
    (b t d modulus : ℕ) (he : e ≤ 2 ^ b)
    (edges : Fin e → Fin (2 ^ t * 2 ^ t) ↪ Fin v)
    (i : Fin (rowCount v b t)) (j : Fin (columnCount b t d)) :
    numericEntry b t d modulus he edges i j =
      (packedFieldBits d modulus (2 ^ b * (2 ^ t * 2 ^ t + 1)))[
        (((columnIndex b t d).symm j).2.2).val *
          (2 ^ b * (2 ^ t * 2 ^ t + 1)) +
        (numericPayloadCoord b t d he edges i j).val]?.getD false := by
  rw [packedFieldBits_get]
  have hs := seed_pair_decode_numeric d (((columnIndex b t d).symm j).2.2)
  simp [numericEntry, numericPayloadCoord, hs.1, hs.2]

#print axioms numericEntry_eq_packedFieldBits

end CurrentAdditive.FiniteFieldConstructor.CanonicalTable
