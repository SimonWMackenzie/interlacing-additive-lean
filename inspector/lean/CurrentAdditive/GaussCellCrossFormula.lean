import CurrentAdditive.GaussCellClock

namespace CurrentAdditive.GaussPhysical

open CurrentAdditive.EliminationEntryBounds
open CurrentAdditive.RationalBitBounds

/-- The signed integer numerator of a normalized pivot-row cell, or of a
cleared nonpivot cell, before cancelling a common divisor. -/
def crossNumerator (pivotRow : Bool) (current column row pivot : ℚ) : ℤ :=
  if pivotRow then row.num * (pivot.den : ℤ)
  else current.num * (column.den : ℤ) * pivot.num * (row.den : ℤ) -
    column.num * (pivot.den : ℤ) * row.num * (current.den : ℤ)

def crossDenominator (pivotRow : Bool) (current column row pivot : ℚ) : ℤ :=
  if pivotRow then (row.den : ℤ) * pivot.num
  else (current.den : ℤ) * (column.den : ℤ) * pivot.num * (row.den : ℤ)

/-- This formula is the exact arithmetic performed by a Gauss clear-cell
callback. It uses only integer multiplication and one signed subtraction;
the result may then be reduced to canonical RawRat form. -/
theorem cellFormula_eq_cross (pivotRow : Bool)
    (current column row pivot : ℚ) (hp : pivot ≠ 0) :
    cellFormula pivotRow current column row pivot =
      (crossNumerator pivotRow current column row pivot : ℚ) /
        (crossDenominator pivotRow current column row pivot : ℚ) := by
  have hpn : pivot.num ≠ 0 := Rat.num_ne_zero.mpr hp
  cases pivotRow
  · simp only [cellFormula, Bool.false_eq_true, ↓reduceIte,
      crossNumerator, crossDenominator]
    conv_lhs => rw [← Rat.num_div_den current, ← Rat.num_div_den column,
      ← Rat.num_div_den row, ← Rat.num_div_den pivot]
    field_simp [current.den_ne_zero, column.den_ne_zero,
      row.den_ne_zero, pivot.den_ne_zero, hpn]
    push_cast
    ring
  · simp only [cellFormula, ↓reduceIte,
      crossNumerator, crossDenominator]
    conv_lhs => rw [← Rat.num_div_den row, ← Rat.num_div_den pivot]
    field_simp [row.den_ne_zero, pivot.den_ne_zero, hpn]
    push_cast
    ring

private theorem twoFactor_bound (a b : ℤ) (S : ℕ)
    (ha : a.natAbs ≤ 2 ^ S) (hb : b.natAbs ≤ 2 ^ S) :
    (a * b).natAbs ≤ 2 ^ (2 * S) := by
  rw [Int.natAbs_mul]
  calc
    a.natAbs * b.natAbs ≤ 2 ^ S * 2 ^ S := Nat.mul_le_mul ha hb
    _ = 2 ^ (2 * S) := by rw [← pow_add]; congr 1; omega

private theorem fourFactor_bound (a b c d : ℤ) (S : ℕ)
    (ha : a.natAbs ≤ 2 ^ S) (hb : b.natAbs ≤ 2 ^ S)
    (hc : c.natAbs ≤ 2 ^ S) (hd : d.natAbs ≤ 2 ^ S) :
    (a * b * c * d).natAbs ≤ 2 ^ (4 * S) := by
  have hab := twoFactor_bound a b S ha hb
  have hcd := twoFactor_bound c d S hc hd
  have hh := Nat.mul_le_mul hab hcd
  rw [Int.natAbs_mul] at hh
  calc
    (a * b * c * d).natAbs = ((a*b)*(c*d)).natAbs := by ring
    _ ≤ 2 ^ (2*S) * 2 ^ (2*S) := by
      simpa [Int.natAbs_mul, mul_assoc] using hh
    _ = 2 ^ (4*S) := by rw [← pow_add]; congr 1; omega

/-- The two operands of the one signed subtraction in a nonpivot Gauss
update each fit in four times the source-cell bit budget, plus one bit. -/
theorem cross_subtrahends_bits
    (current column row pivot : ℚ) (S : ℕ)
    (hcurrent : ComponentsWithin (2 ^ S) current)
    (hcolumn : ComponentsWithin (2 ^ S) column)
    (hrow : ComponentsWithin (2 ^ S) row)
    (hpivot : ComponentsWithin (2 ^ S) pivot) :
    Nat.size (current.num * (column.den : ℤ) * pivot.num * (row.den : ℤ)).natAbs ≤
        4 * S + 1 ∧
      Nat.size (column.num * (pivot.den : ℤ) * row.num * (current.den : ℤ)).natAbs ≤
        4 * S + 1 := by
  constructor
  · apply size_le_of_pow_bound
    exact fourFactor_bound current.num (column.den : ℤ)
      pivot.num (row.den : ℤ) S hcurrent.1
      (by simpa using hcolumn.2) hpivot.1 (by simpa using hrow.2)
  · apply size_le_of_pow_bound
    exact fourFactor_bound column.num (pivot.den : ℤ)
      row.num (current.den : ℤ) S hcolumn.1
      (by simpa using hpivot.2) hrow.1 (by simpa using hcurrent.2)

/-- The unreduced numerator and denominator written by a direct Gauss
clear-cell callback have at most four times the canonical cell bit budget,
plus two bits for the subtraction. -/
theorem cross_words_bits (pivotRow : Bool)
    (current column row pivot : ℚ) (S : ℕ)
    (hcurrent : ComponentsWithin (2 ^ S) current)
    (hcolumn : ComponentsWithin (2 ^ S) column)
    (hrow : ComponentsWithin (2 ^ S) row)
    (hpivot : ComponentsWithin (2 ^ S) pivot) :
    Nat.size (crossNumerator pivotRow current column row pivot).natAbs ≤
        4 * S + 2 ∧
      Nat.size (crossDenominator pivotRow current column row pivot).natAbs ≤
        4 * S + 2 := by
  have hnum : (crossNumerator pivotRow current column row pivot).natAbs ≤
      2 ^ (4*S+1) := by
    cases pivotRow
    · simp only [crossNumerator, Bool.false_eq_true, ↓reduceIte]
      have h := fourFactor_bound current.num (column.den : ℤ)
        pivot.num (row.den : ℤ) S hcurrent.1
        (by simpa using hcolumn.2) hpivot.1 (by simpa using hrow.2)
      have h' := fourFactor_bound column.num (pivot.den : ℤ)
        row.num (current.den : ℤ) S hcolumn.1
        (by simpa using hpivot.2) hrow.1 (by simpa using hcurrent.2)
      calc
        _ ≤ (current.num * (column.den : ℤ) * pivot.num * (row.den : ℤ)).natAbs +
          (column.num * (pivot.den : ℤ) * row.num * (current.den : ℤ)).natAbs :=
          Int.natAbs_sub_le _ _
        _ ≤ 2 ^ (4*S) + 2 ^ (4*S) := Nat.add_le_add h h'
        _ = 2 ^ (4*S+1) := by rw [pow_succ]; omega
    · simp only [crossNumerator, ↓reduceIte]
      have h := twoFactor_bound row.num (pivot.den : ℤ) S hrow.1
        (by simpa using hpivot.2)
      exact h.trans (Nat.pow_le_pow_right (by omega) (by omega))
  have hden : (crossDenominator pivotRow current column row pivot).natAbs ≤
      2 ^ (4*S+1) := by
    cases pivotRow
    · simp only [crossDenominator, Bool.false_eq_true, ↓reduceIte]
      have h := fourFactor_bound (current.den : ℤ) (column.den : ℤ)
        pivot.num (row.den : ℤ) S
        (by simpa using hcurrent.2) (by simpa using hcolumn.2)
        hpivot.1 (by simpa using hrow.2)
      exact h.trans (Nat.pow_le_pow_right (by omega) (by omega))
    · simp only [crossDenominator, ↓reduceIte]
      have h := twoFactor_bound (row.den : ℤ) pivot.num S
        (by simpa using hrow.2) hpivot.1
      exact h.trans (Nat.pow_le_pow_right (by omega) (by omega))
  exact ⟨size_le_of_pow_bound hnum, size_le_of_pow_bound hden⟩

theorem canonicalCellPacketValue_eq_cross (pivotRow : Bool)
    (current column row pivot : ℚ) (hp : pivot ≠ 0) :
    cellPacketValue pivotRow (rawOfRat current) (rawOfRat column)
      (rawOfRat row) (rawOfRat pivot) =
      (crossNumerator pivotRow current column row pivot : ℚ) /
        (crossDenominator pivotRow current column row pivot : ℚ) := by
  rw [cellPacketValue_canonical]
  exact cellFormula_eq_cross pivotRow current column row pivot hp

end CurrentAdditive.GaussPhysical
