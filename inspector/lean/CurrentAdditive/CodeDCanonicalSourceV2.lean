import CurrentAdditive.CodeDSourceCodecV2

/-!
Canonical serialization of the actual rational, indexed output returned by
`SequentialSourceCode.sequentialMaterialized`.  This file only supplies the
byte-to-value interface.  Its carrier remains the array index; equal words
are never quotiented or combined.
-/

namespace CurrentAdditive.CodeDCanonicalSourceV2

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.EncodedCommunication
open EthInapproximability.CurrentPaper.BitMachineBinaryMultiply
open CodeDCodec CodeDSourceCodecV2

theorem msbValue_append_singleton (bits : List Bool) (b : Bool) :
    msbValue (bits ++ [b]) = Nat.bit b (msbValue bits) := by
  simp [msbValue, List.foldl_append]

theorem msbValue_reverse (bits : List Bool) :
    msbValue bits.reverse = bitsValue bits := by
  induction bits with
  | nil => rfl
  | cons b bs ih =>
      simpa [List.reverse_cons, msbValue_append_singleton, ih, bitsValue]

def rawOfRat (r : ℚ) : RawRat :=
  ⟨r.num < 0, r.num.natAbs.bits, r.den.bits.reverse⟩

theorem rawOfRat_valid (r : ℚ) : (rawOfRat r).Valid := by
  simp [RawRat.Valid, rawOfRat, msbValue_reverse, bitsValue_bits,
    Rat.den_pos]

theorem rawOfRat_value (r : ℚ) : (rawOfRat r).value = r := by
  have hbits : bitsValue r.num.natAbs.bits = r.num.natAbs := bitsValue_bits _
  have hden : msbValue r.den.bits.reverse = r.den := by
    rw [msbValue_reverse, bitsValue_bits]
  have hcast : ((r.num.natAbs : Nat) : ℚ) = |(r.num : ℚ)| := by
    simpa using congrArg (fun z : ℤ => (z : ℚ)) (Int.natCast_natAbs r.num)
  by_cases hneg : r.num < 0
  · have hneg' : (r.num : ℚ) < 0 := by exact_mod_cast hneg
    calc
      (rawOfRat r).value = (r.num : ℚ) / (r.den : ℚ) := by
        simp [RawRat.value, rawOfRat, hneg, hbits, hden, hcast,
          abs_of_neg hneg', neg_div]
      _ = r := r.num_div_den
  · have hnonneg : 0 ≤ r.num := le_of_not_gt hneg
    have hnonneg' : (0 : ℚ) ≤ r.num := by exact_mod_cast hnonneg
    calc
      (rawOfRat r).value = (r.num : ℚ) / (r.den : ℚ) := by
        simp [RawRat.value, rawOfRat, hneg, hbits, hden, hcast,
          abs_of_nonneg hnonneg']
      _ = r := r.num_div_den

def canonicalEntry {q : Nat} (entry : (Fin q → Nat) × ℚ) : Entry :=
  ⟨List.ofFn (fun j : Fin q => (entry.1 j).bits), rawOfRat entry.2⟩

theorem canonicalEntry_valid {q : Nat} (entry : (Fin q → Nat) × ℚ) :
    (canonicalEntry entry).weight.Valid := rawOfRat_valid _

theorem canonicalEntry_length {q : Nat} (entry : (Fin q → Nat) × ℚ) :
    (canonicalEntry entry).word.length = q := by
  simp [canonicalEntry]

theorem canonicalEntry_values {q : Nat} (entry : (Fin q → Nat) × ℚ) :
    (valueWord (canonicalEntry entry), valueWeight (canonicalEntry entry)) =
      (List.ofFn entry.1, entry.2) := by
  have hw : (List.ofFn (fun j : Fin q => (entry.1 j).bits)).map bitsValue =
      List.ofFn entry.1 := by
    simp only [List.map_ofFn]
    congr 1
    funext j
    exact bitsValue_bits _
  simp [canonicalEntry, valueWord, valueWeight, rawOfRat_value, hw]

def canonicalSource {q : Nat} (source : Array ((Fin q → Nat) × ℚ)) :
    List Entry := source.toList.map canonicalEntry

def encodedSource {q : Nat} (source : Array ((Fin q → Nat) × ℚ)) :
    List Bool := encodeSource (canonicalSource source)

theorem decode_encodedSource {q : Nat}
    (source : Array ((Fin q → Nat) × ℚ)) :
    decodeSource q (encodedSource source) = some (canonicalSource source) := by
  apply decodeSource_encodeSource
  · intro e he
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp he
    exact canonicalEntry_valid x
  · intro e he
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp he
    exact canonicalEntry_length x

theorem canonicalSource_values {q : Nat}
    (source : Array ((Fin q → Nat) × ℚ)) :
    (canonicalSource source).map
      (fun e => (valueWord e, valueWeight e)) =
      source.toList.map (fun entry => (List.ofFn entry.1, entry.2)) := by
  simp [canonicalSource, List.map_map, canonicalEntry_values]

#print axioms msbValue_reverse
#print axioms rawOfRat_value
#print axioms decode_encodedSource

end CurrentAdditive.CodeDCanonicalSourceV2
