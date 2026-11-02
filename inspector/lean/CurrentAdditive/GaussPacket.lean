import CurrentAdditive.CodeDCodecV2
import CurrentAdditive.EntryAdapter

/-!
The exact Code D packet layer for the eager Gauss loop. Its matrix field is a
counted list of counted rows of three-bank canonical rational packets. This
module establishes the value-level ABI; a fixed TM2 transition program and
its clock are separate obligations.
-/

namespace CurrentAdditive.GaussPhysical

open CurrentAdditive.CodeDCodec
open EthInapproximability.CurrentPaper

theorem msbValue_reverse (bits : List Bool) :
    BitMachineBinaryMultiply.msbValue bits.reverse =
      EncodedCommunication.bitsValue bits := by
  induction bits with
  | nil => rfl
  | cons b bits ih =>
      simp only [List.reverse_cons, BitMachineBinaryMultiply.msbValue,
        List.foldl_append, List.foldl_cons, List.foldl_nil,
        EncodedCommunication.bitsValue]
      rw [← BitMachineBinaryMultiply.msbValue, ih]

def rawOfRat (q : ℚ) : RawRat :=
  ⟨q.num < 0, q.num.natAbs.bits, q.den.bits.reverse⟩

theorem rawOfRat_valid (q : ℚ) : (rawOfRat q).Valid := by
  simpa [RawRat.Valid, rawOfRat, msbValue_reverse] using q.den_pos

theorem rawOfRat_value (q : ℚ) : (rawOfRat q).value = q := by
  have hv : (rawOfRat q).value = (q.num : ℚ) / (q.den : ℚ) := by
    simp only [RawRat.value, rawOfRat, EncodedCommunication.bitsValue_bits,
      msbValue_reverse]
    by_cases h : q.num < 0
    · simp only [decide_eq_true_eq, h, ↓reduceIte]
      have hh : (q.num.natAbs : ℤ) = -q.num :=
        Int.ofNat_natAbs_of_nonpos (le_of_lt h)
      have hhq : ((q.num.natAbs : ℕ) : ℚ) = -(q.num : ℚ) := by
        simpa only [Int.cast_natCast, Int.cast_neg] using
          congrArg (fun z : ℤ => (z : ℚ)) hh
      rw [hhq]
      ring
    · simp only [decide_eq_true_eq, h, ↓reduceIte]
      have hh : (q.num.natAbs : ℤ) = q.num :=
        Int.natAbs_of_nonneg (by omega)
      have hhq : ((q.num.natAbs : ℕ) : ℚ) = (q.num : ℚ) := by
        simpa only [Int.cast_natCast] using
          congrArg (fun z : ℤ => (z : ℚ)) hh
      rw [hhq]
      ring
  exact hv.trans (Rat.num_div_den q)

def encodeRow (row : List RawRat) : List Bool :=
  CodeDCodecV2.encodeItems (row.map encodeRawRat)

def decodeRow (bits : List Bool) : Option (List RawRat) := do
  let cells ← CodeDCodecV2.decodeItems bits
  cells.mapM decodeRawRat

def encodeMatrix (rows : List (List RawRat)) : List Bool :=
  CodeDCodecV2.encodeItems (rows.map encodeRow)

def decodeMatrix (bits : List Bool) : Option (List (List RawRat)) := do
  let rows ← CodeDCodecV2.decodeItems bits
  rows.mapM decodeRow

theorem decodeRow_encodeRow (row : List RawRat)
    (h : ∀ r ∈ row, r.Valid) :
    decodeRow (encodeRow row) = some row := by
  induction row with
  | nil => simp [decodeRow, encodeRow]
  | cons r row ih =>
      have hr := h r (by simp)
      have htail : ∀ x ∈ row, x.Valid := by
        intro x hx
        exact h x (by simp [hx])
      have htailMap : row.mapM (decodeRawRat ∘ encodeRawRat) = some row := by
        simpa [decodeRow, encodeRow] using ih htail
      simp [decodeRow, encodeRow, decodeRawRat_encodeRawRat r hr,
        htailMap, List.mapM_cons]

theorem decodeMatrix_encodeMatrix (rows : List (List RawRat))
    (h : ∀ row ∈ rows, ∀ r ∈ row, r.Valid) :
    decodeMatrix (encodeMatrix rows) = some rows := by
  induction rows with
  | nil => simp [decodeMatrix, encodeMatrix]
  | cons row rows ih =>
      have hrow : ∀ r ∈ row, r.Valid := h row (by simp)
      have htail : ∀ row ∈ rows, ∀ r ∈ row, r.Valid := by
        intro row hrow r hr
        exact h row (by simp [hrow]) r hr
      have htailMap : rows.mapM (decodeRow ∘ encodeRow) = some rows := by
        simpa [decodeMatrix, encodeMatrix] using ih htail
      simp [decodeMatrix, encodeMatrix, decodeRow_encodeRow row hrow,
        htailMap, List.mapM_cons]

def encodeRationalMatrix (rows : List (List ℚ)) : List Bool :=
  encodeMatrix (rows.map (·.map rawOfRat))

def matrixValues (rows : List (List RawRat)) : List (List ℚ) :=
  rows.map (·.map RawRat.value)

theorem decodeRationalMatrix (rows : List (List ℚ)) :
    (decodeMatrix (encodeRationalMatrix rows)).map matrixValues = some rows := by
  have hvalid : ∀ row ∈ rows.map (·.map rawOfRat),
      ∀ r ∈ row, r.Valid := by
    intro row hrow r hr
    obtain ⟨qrow, hqrow, rfl⟩ := List.mem_map.mp hrow
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hr
    exact rawOfRat_valid q
  simp [encodeRationalMatrix, decodeMatrix_encodeMatrix _ hvalid,
    matrixValues, List.map_map, Function.comp_def, rawOfRat_value]

end CurrentAdditive.GaussPhysical
