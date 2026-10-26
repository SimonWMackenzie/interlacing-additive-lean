import CurrentAdditive.CanonicalPhysicalEntryBit

namespace CurrentAdditive.FiniteFieldConstructor.CanonicalTable

def canonicalLookupClock (b t d : ℕ) : ℕ :=
  32 * (4 * (2 ^ t * 2 ^ t + 1) * columnCount b t d + 1) ^ 2

/-- The actual prepared-array lookup clock has one uniform bound over all
canonical matrix entries. The bound counts transitions of the fixed lookup
program; it does not cover preparing the packed array or numeric inputs. -/
theorem physical_entry_lookup_clock_uniform {v e : ℕ}
    (b t d modulus : ℕ) (he : e ≤ 2 ^ b)
    (edges : Fin e → Fin (2 ^ t * 2 ^ t) ↪ Fin v)
    (i : Fin (rowCount v b t)) (j : Fin (columnCount b t d)) :
    32 *
      ((((columnIndex b t d).symm j).2.2).val +
        (2 ^ b * (2 ^ t * 2 ^ t + 1)) +
        (numericPayloadCoord b t d he edges i j).val +
        (packedFieldBits d modulus
          (2 ^ b * (2 ^ t * 2 ^ t + 1))).length + 1) ^ 2 ≤
      canonicalLookupClock b t d := by
  let R2 := (2 ^ d) ^ 2
  let n := 2 ^ b * (2 ^ t * 2 ^ t + 1)
  let C := columnCount b t d
  let L := R2 * n
  have hR : 1 ≤ R2 := by
    have h : 0 < R2 := by dsimp [R2]; positivity
    omega
  have hn : 1 ≤ n := by
    have h : 0 < n := by dsimp [n]; positivity
    omega
  have hq : 1 ≤ 2 ^ (t - 1) := by
    have h : 0 < 2 ^ (t - 1) := by positivity
    omega
  have hL : (packedFieldBits d modulus n).length = L := by
    simp [packedFieldBits_length, L, R2]
  have hLC : L ≤ C * (2 ^ t * 2 ^ t + 1) := by
    have hmul : 2 ^ b * R2 ≤ 2 ^ (t - 1) * (2 ^ b * R2) := by
      simpa only [Nat.one_mul] using
        Nat.mul_le_mul_right (2 ^ b * R2) hq
    calc
      L = (2 ^ b * R2) * (2 ^ t * 2 ^ t + 1) := by
        dsimp [L, n]
        ring
      _ ≤ (2 ^ (t - 1) * (2 ^ b * R2)) *
          (2 ^ t * 2 ^ t + 1) := Nat.mul_le_mul_right _ hmul
      _ = C * (2 ^ t * 2 ^ t + 1) := by
        dsimp [C, columnCount, R2]
        ring
  have hseed : (((columnIndex b t d).symm j).2.2).val < R2 :=
    (((columnIndex b t d).symm j).2.2).isLt
  have hcoord := (numericPayloadCoord b t d he edges i j).isLt
  have hRle : R2 ≤ L := by
    dsimp [L]
    nlinarith
  have hnle : n ≤ L := by
    dsimp [L]
    nlinarith
  unfold canonicalLookupClock
  have harg :
      (((columnIndex b t d).symm j).2.2).val + n +
        (numericPayloadCoord b t d he edges i j).val +
        (packedFieldBits d modulus n).length + 1 ≤
      4 * (2 ^ t * 2 ^ t + 1) * C + 1 := by
    rw [hL]
    calc
      _ ≤ 4 * L + 1 := by omega
      _ ≤ 4 * (2 ^ t * 2 ^ t + 1) * C + 1 := by
        nlinarith [hLC]
  change 32 *
    ((((columnIndex b t d).symm j).2.2).val + n +
      (numericPayloadCoord b t d he edges i j).val +
      (packedFieldBits d modulus n).length + 1) ^ 2 ≤
    32 * (4 * (2 ^ t * 2 ^ t + 1) * C + 1) ^ 2
  exact Nat.mul_le_mul_left 32 (Nat.pow_le_pow_left harg 2)

#print axioms physical_entry_lookup_clock_uniform

end CurrentAdditive.FiniteFieldConstructor.CanonicalTable
