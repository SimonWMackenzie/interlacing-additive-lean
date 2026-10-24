import CurrentAdditive.BinaryGCDPacket
import CurrentAdditive.CodeDCodec

/-! Semantic target for physical rational normalization. -/
namespace CurrentAdditive.BinaryGCDNormalization

open EthInapproximability.CurrentPaper
open CurrentAdditive.CodeDCodec

def numeratorValue (r : RawRat) : Nat :=
  EncodedCommunication.bitsValue r.numerator

def denominatorValue (r : RawRat) : Nat :=
  BitMachineBinaryMultiply.msbValue r.denominator

def commonDivisor (r : RawRat) : Nat :=
  Nat.gcd (numeratorValue r) (denominatorValue r)

def normalize (r : RawRat) : RawRat :=
  { negative := r.negative && decide (numeratorValue r ≠ 0)
    numerator := (numeratorValue r / commonDivisor r).bits
    denominator := (denominatorValue r / commonDivisor r).bits.reverse }

theorem commonDivisor_pos (r : RawRat) (hr : r.Valid) :
    0 < commonDivisor r := by
  unfold commonDivisor
  exact Nat.gcd_pos_of_pos_right _ (by simpa [RawRat.Valid, denominatorValue] using hr)

theorem normalize_numerator_value (r : RawRat) :
    numeratorValue (normalize r) = numeratorValue r / commonDivisor r := by
  simp [normalize, numeratorValue, EncodedCommunication.bitsValue_bits]

theorem normalize_denominator_value (r : RawRat) :
    denominatorValue (normalize r) = denominatorValue r / commonDivisor r := by
  change BitMachineBinaryDivision.msbValue
      (denominatorValue r / commonDivisor r).bits.reverse = _
  rw [PrimeSamplerBinaryDigit.msbValue_reverse]
  exact EncodedCommunication.bitsValue_bits _

theorem normalize_valid (r : RawRat) (hr : r.Valid) :
    (normalize r).Valid := by
  have hd : 0 < denominatorValue r := by
    simpa [RawRat.Valid, denominatorValue] using hr
  have hdiv : commonDivisor r ≤ denominatorValue r :=
    Nat.gcd_le_right _ hd
  have hpos := commonDivisor_pos r hr
  rw [RawRat.Valid, ← denominatorValue, normalize_denominator_value]
  exact Nat.div_pos hdiv hpos

theorem normalized_numerator_le (r : RawRat) :
    numeratorValue (normalize r) ≤ numeratorValue r := by
  rw [normalize_numerator_value]
  exact Nat.div_le_self _ _

theorem normalized_denominator_le (r : RawRat) :
    denominatorValue (normalize r) ≤ denominatorValue r := by
  rw [normalize_denominator_value]
  exact Nat.div_le_self _ _

private theorem reduced_ratio (n d : Nat) (hd : 0 < d) :
    let g := Nat.gcd n d
    ((n / g : Nat) : ℚ) / ((d / g : Nat) : ℚ) =
      (n : ℚ) / (d : ℚ) := by
  let g := Nat.gcd n d
  have hg : 0 < g := Nat.gcd_pos_of_pos_right _ hd
  have hn : n / g * g = n := Nat.div_mul_cancel (Nat.gcd_dvd_left n d)
  have hden : d / g * g = d := Nat.div_mul_cancel (Nat.gcd_dvd_right n d)
  have hgq : (g : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hg)
  have hdq : ((d / g : Nat) : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.div_pos (Nat.gcd_le_right _ hd) hg))
  have hnc : ((n / g : Nat) : ℚ) * (g : ℚ) = (n : ℚ) := by exact_mod_cast hn
  have hdc : ((d / g : Nat) : ℚ) * (g : ℚ) = (d : ℚ) := by exact_mod_cast hden
  change ((n / g : Nat) : ℚ) / ((d / g : Nat) : ℚ) =
    (n : ℚ) / (d : ℚ)
  rw [← hnc, ← hdc]
  field_simp [hgq, hdq]

theorem normalize_value (r : RawRat) (hr : r.Valid) :
    (normalize r).value = r.value := by
  have hd : 0 < denominatorValue r := by
    simpa [RawRat.Valid, denominatorValue] using hr
  have hratio := reduced_ratio (numeratorValue r) (denominatorValue r) hd
  change ((numeratorValue r / commonDivisor r : Nat) : ℚ) /
      ((denominatorValue r / commonDivisor r : Nat) : ℚ) =
    (numeratorValue r : ℚ) / (denominatorValue r : ℚ) at hratio
  by_cases hz : numeratorValue r = 0
  · have hn0 : EncodedCommunication.bitsValue (normalize r).numerator = 0 := by
      change numeratorValue (normalize r) = 0
      rw [normalize_numerator_value, hz]
      simp
    unfold RawRat.value
    rw [hn0]
    have hraw : EncodedCommunication.bitsValue r.numerator = 0 := hz
    rw [hraw]
    simp
  · have hsign : (normalize r).negative = r.negative := by
      simp [normalize, hz]
    unfold RawRat.value
    rw [hsign]
    rw [show EncodedCommunication.bitsValue (normalize r).numerator =
      numeratorValue r / commonDivisor r from normalize_numerator_value r]
    rw [show BitMachineBinaryMultiply.msbValue (normalize r).denominator =
      denominatorValue r / commonDivisor r from normalize_denominator_value r]
    change (if r.negative then -1 else 1) *
      (((numeratorValue r / commonDivisor r : Nat) : ℚ) /
        ((denominatorValue r / commonDivisor r : Nat) : ℚ)) =
      (if r.negative then -1 else 1) *
        ((numeratorValue r : ℚ) / (denominatorValue r : ℚ))
    rw [hratio]

end CurrentAdditive.BinaryGCDNormalization
