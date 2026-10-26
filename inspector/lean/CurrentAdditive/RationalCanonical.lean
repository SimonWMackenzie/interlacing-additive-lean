import CurrentAdditive.RationalNormalForm
import CurrentAdditive.CodeDCanonicalSource

namespace CurrentAdditive.BinaryGCDNormalization

open EthInapproximability.CurrentPaper
open CurrentAdditive.CodeDCodec

def signedNumerator (r : RawRat) : ℤ :=
  if r.negative then -((numeratorValue r / commonDivisor r : Nat) : ℤ)
  else ((numeratorValue r / commonDivisor r : Nat) : ℤ)

theorem signedNumerator_natAbs (r : RawRat) :
    (signedNumerator r).natAbs = numeratorValue r / commonDivisor r := by
  by_cases h : r.negative = true
  · rw [signedNumerator, if_pos h, Int.natAbs_neg, Int.natAbs_natCast]
  · rw [signedNumerator, if_neg h, Int.natAbs_natCast]

theorem normalized_coprime (r : RawRat) (hr : r.Valid) :
    Nat.Coprime (numeratorValue (normalize r))
      (denominatorValue (normalize r)) := by
  rw [normalize_numerator_value, normalize_denominator_value]
  exact Nat.coprime_div_gcd_div_gcd (commonDivisor_pos r hr)

theorem value_as_signed_div (r : RawRat) (hr : r.Valid) :
    r.value = (signedNumerator r : ℚ) /
      ((denominatorValue (normalize r) : Nat) : ℚ) := by
  have hn := normalize_numerator_value r
  have hd := normalize_denominator_value r
  have hs : (normalize r).negative =
      (r.negative && decide (numeratorValue r ≠ 0)) := rfl
  rw [← normalize_value r hr]
  change (if (normalize r).negative then (-1 : ℚ) else 1) *
      ((numeratorValue (normalize r) : ℚ) /
        (denominatorValue (normalize r) : ℚ)) = _
  rw [hn, hs]
  by_cases hz : numeratorValue r = 0
  · simp only [hz, Nat.zero_div, Nat.cast_zero, zero_div, mul_zero]
    simp [signedNumerator, hz]
  · cases hsign : r.negative
    · simp only [hsign, Bool.false_and, Bool.false_eq_true, ↓reduceIte, one_mul,
        signedNumerator, Int.cast_natCast]
    · simp only [hsign, Bool.true_and, decide_eq_true_eq, ↓reduceIte,
        signedNumerator, Int.cast_neg, Int.cast_natCast, neg_div]
      simp [hz]

theorem canonical_num_den (r : RawRat) (hr : r.Valid) :
    r.value.num = signedNumerator r ∧
      r.value.den = denominatorValue (normalize r) := by
  have hb : 0 < (denominatorValue (normalize r) : ℤ) := by
    exact_mod_cast normalize_valid r hr
  have hc : Nat.Coprime (signedNumerator r).natAbs
      (denominatorValue (normalize r) : ℤ).natAbs := by
    rw [signedNumerator_natAbs, Int.natAbs_natCast,
      ← normalize_numerator_value]
    exact normalized_coprime r hr
  have hval := value_as_signed_div r hr
  have hnum := Rat.num_div_eq_of_coprime hb hc
  have hden := Rat.den_div_eq_of_coprime hb hc
  constructor
  · rw [hval]; exact hnum
  · rw [hval]
    exact_mod_cast hden

theorem normalized_sign (r : RawRat) (hr : r.Valid) :
    (normalize r).negative = (signedNumerator r < 0) := by
  by_cases hz : numeratorValue r = 0
  · simp [normalize, signedNumerator, hz]
  · have hn : 0 < numeratorValue r := Nat.pos_of_ne_zero hz
    have hg : commonDivisor r ≤ numeratorValue r :=
      Nat.gcd_le_left _ hn
    have hdiv : 0 < numeratorValue r / commonDivisor r :=
      Nat.div_pos hg (commonDivisor_pos r hr)
    cases hsign : r.negative
    · simp only [normalize, hsign, Bool.false_and, signedNumerator,
        Bool.false_eq_true, ↓reduceIte]
      simp
      rw [← Int.natCast_div]
      exact Int.natCast_nonneg _
    · simp only [normalize, hsign, Bool.true_and, signedNumerator,
        ↓reduceIte]
      simp [hz]
      exact_mod_cast hdiv

theorem normalize_is_rawOfRat (r : RawRat) (hr : r.Valid) :
    normalize r = CurrentAdditive.CodeDCanonicalSource.rawOfRat r.value := by
  obtain ⟨hnum, hden⟩ := canonical_num_den r hr
  have hsign := normalized_sign r hr
  cases r with
  | mk sign num den =>
    simp only [normalize, CurrentAdditive.CodeDCanonicalSource.rawOfRat]
    congr 1
    · apply Bool.eq_iff_iff.mpr
      rw [hnum]
      rw [decide_eq_true_eq, ← hsign]
      rfl
    · simp [hnum, signedNumerator_natAbs]
    · rw [hden]
      exact congrArg List.reverse
        (congrArg Nat.bits (normalize_denominator_value _).symm)

theorem normalize_numerator_length_le (r : RawRat) :
    (normalize r).numerator.length ≤ r.numerator.length := by
  have hv : numeratorValue r < 2 ^ r.numerator.length :=
    BitMachineBinarySubtract.bitsValue_lt_pow r.numerator
  have hsize : (numeratorValue r).size ≤ r.numerator.length :=
    Nat.size_le.mpr hv
  have hdiv := normalized_numerator_le r
  have hmono : (numeratorValue (normalize r)).size ≤
      (numeratorValue r).size := Nat.size_le_size hdiv
  rw [normalize_numerator_value] at hmono
  change (numeratorValue r / commonDivisor r).bits.length ≤ r.numerator.length
  rw [Nat.size_eq_bits_len]
  exact hmono.trans hsize

theorem normalize_denominator_length_le (r : RawRat) :
    (normalize r).denominator.length ≤ r.denominator.length := by
  have hv : denominatorValue r < 2 ^ r.denominator.length := by
    have hrev : denominatorValue r =
        EncodedCommunication.bitsValue r.denominator.reverse := by
      simpa [denominatorValue] using
        (PrimeSamplerBinaryDigit.msbValue_reverse r.denominator.reverse)
    rw [hrev]
    simpa using BitMachineBinarySubtract.bitsValue_lt_pow r.denominator.reverse
  have hsize : (denominatorValue r).size ≤ r.denominator.length :=
    Nat.size_le.mpr hv
  have hdiv := normalized_denominator_le r
  have hmono : (denominatorValue (normalize r)).size ≤
      (denominatorValue r).size := Nat.size_le_size hdiv
  rw [normalize_denominator_value] at hmono
  change (denominatorValue r / commonDivisor r).bits.reverse.length ≤
    r.denominator.length
  simp only [List.length_reverse]
  rw [Nat.size_eq_bits_len]
  exact hmono.trans hsize


end CurrentAdditive.BinaryGCDNormalization
