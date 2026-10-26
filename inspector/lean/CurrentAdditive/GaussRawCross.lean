import CurrentAdditive.GaussCellCrossFormula

namespace CurrentAdditive.GaussPhysical

open CurrentAdditive.CodeDCodec
open EthInapproximability.CurrentPaper

/-- A possibly unreduced integer fraction in the shared RawRat format.
The denominator field is positive even when the source integer is negative. -/
def rawIntDiv (N D : ℤ) : RawRat :=
  ⟨(N < 0) != (D < 0), N.natAbs.bits, D.natAbs.bits.reverse⟩

theorem rawIntDiv_valid (N D : ℤ) (hD : D ≠ 0) :
    (rawIntDiv N D).Valid := by
  simpa [rawIntDiv, RawRat.Valid, msbValue_reverse] using
    Int.natAbs_pos.mpr hD

private theorem cast_natAbs (z : ℤ) :
    ((z.natAbs : ℕ) : ℚ) = if z < 0 then -(z : ℚ) else (z : ℚ) := by
  by_cases hz : z < 0
  · simp only [hz, ↓reduceIte]
    have h := Int.ofNat_natAbs_of_nonpos (le_of_lt hz)
    exact (by simpa only [Int.cast_natCast, Int.cast_neg] using
      congrArg (fun x : ℤ => (x : ℚ)) h)
  · simp only [hz, ↓reduceIte]
    have h := Int.natAbs_of_nonneg (by omega : 0 ≤ z)
    exact (by simpa only [Int.cast_natCast] using
      congrArg (fun x : ℤ => (x : ℚ)) h)

theorem rawIntDiv_value (N D : ℤ) :
    (rawIntDiv N D).value = (N : ℚ) / (D : ℚ) := by
  simp only [rawIntDiv, RawRat.value, EncodedCommunication.bitsValue_bits,
    msbValue_reverse]
  rw [cast_natAbs N, cast_natAbs D]
  by_cases hN : N < 0 <;> by_cases hDneg : D < 0 <;>
    simp only [hN, hDneg, ↓reduceIte] <;>
    norm_num at * <;>
    ring

def crossRaw (pivotRow : Bool) (current column row pivot : ℚ) : RawRat :=
  rawIntDiv (crossNumerator pivotRow current column row pivot)
    (crossDenominator pivotRow current column row pivot)

theorem crossDenominator_ne_zero (pivotRow : Bool)
    (current column row pivot : ℚ) (hp : pivot ≠ 0) :
    crossDenominator pivotRow current column row pivot ≠ 0 := by
  have hpn : pivot.num ≠ 0 := Rat.num_ne_zero.mpr hp
  cases pivotRow <;>
    simp [crossDenominator, hpn, current.den_ne_zero,
      column.den_ne_zero, row.den_ne_zero]

theorem crossRaw_valid (pivotRow : Bool)
    (current column row pivot : ℚ) (hp : pivot ≠ 0) :
    (crossRaw pivotRow current column row pivot).Valid :=
  rawIntDiv_valid _ _ (crossDenominator_ne_zero pivotRow current column row pivot hp)

theorem crossRaw_value (pivotRow : Bool)
    (current column row pivot : ℚ) (hp : pivot ≠ 0) :
    (crossRaw pivotRow current column row pivot).value =
      cellFormula pivotRow current column row pivot := by
  rw [crossRaw, rawIntDiv_value]
  exact (cellFormula_eq_cross pivotRow current column row pivot hp).symm

theorem rawIntDiv_code_length (N D : ℤ) (E : ℕ)
    (hN : Nat.size N.natAbs ≤ E) (hD : Nat.size D.natAbs ≤ E) :
    (encodeRawRat (rawIntDiv N D)).length ≤ 4 * E + 5 := by
  rw [encodeRawRat, BitMachineBankCodec.encode_length]
  have hs :
      (if (N < 0) != (D < 0) then [true] else ([] : List Bool)).length ≤ 1 := by
    split_ifs <;> simp
  simp [rawRatBank, rawIntDiv, Fin.sum_univ_succ,
    Nat.size_eq_bits_len] at *
  omega

theorem crossRaw_code_length (pivotRow : Bool)
    (current column row pivot : ℚ) (S : ℕ)
    (hcurrent : CurrentAdditive.EliminationEntryBounds.ComponentsWithin (2 ^ S) current)
    (hcolumn : CurrentAdditive.EliminationEntryBounds.ComponentsWithin (2 ^ S) column)
    (hrow : CurrentAdditive.EliminationEntryBounds.ComponentsWithin (2 ^ S) row)
    (hpivot : CurrentAdditive.EliminationEntryBounds.ComponentsWithin (2 ^ S) pivot) :
    (encodeRawRat (crossRaw pivotRow current column row pivot)).length ≤
      4 * (4 * S + 2) + 5 := by
  have hb := cross_words_bits pivotRow current column row pivot S
    hcurrent hcolumn hrow hpivot
  exact rawIntDiv_code_length _ _ _ hb.1 hb.2

end CurrentAdditive.GaussPhysical
