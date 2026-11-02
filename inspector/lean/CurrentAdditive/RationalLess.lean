import CurrentAdditive.RationalStrictNegative
import CurrentAdditive.RationalSubtractSerialized
import CurrentAdditive.RationalSubtractTotalWitness
import CurrentAdditive.CodeDZeroWordV2
import EthInapproximability.CurrentPaper.BitMachineComposition
import Mathlib.Tactic

/-! A fixed physical strict rational comparator on nested two-RawRat packets.
The first stage is the literal nested-pair subtraction program; the next two
stages serialize its sign and numerator, and the last stage emits a strict
Boolean bit. The all-word result is total, including malformed packets. -/

namespace CurrentAdditive.RationalLess

open EthInapproximability.CurrentPaper
open CurrentAdditive.CodeDCodec

noncomputable def result (input : List Bool) : List Bool :=
  RationalStrictNegative.result (RationalSubtractSerialized.result input)

theorem polytime : BitMachine.Polytime result := by
  simpa only [result, Function.comp_def] using
    BitMachineComposition.polytime_comp
      RationalSubtractSerialized.polytime RationalStrictNegative.polytime

/- The `polytime_comp` witness is built by physical machine composition from
the checked subtraction, serialization, and strict-sign programs. This names
one fixed witness, rather than an input-dependent choice of programs. -/
noncomputable def machine : BitMachine.Machine := Classical.choose polytime
noncomputable def coefficient : Nat := Classical.choose (Classical.choose_spec polytime)
noncomputable def exponent : Nat :=
  Classical.choose (Classical.choose_spec (Classical.choose_spec polytime))

theorem outputs (input : List Bool) :
    machine.OutputsWithin input (result input)
      (coefficient * (input.length+1)^exponent) :=
  (Classical.choose_spec (Classical.choose_spec
    (Classical.choose_spec polytime))) input

private theorem any_iff_value_pos (word : List Bool) :
    word.any id = true ↔ 0 < EncodedCommunication.bitsValue word := by
  have hz := CurrentAdditive.CodeDZeroWordV2.output_true_iff_zero word
  constructor
  · intro h
    have hn : EncodedCommunication.bitsValue word ≠ 0 := by
      intro he
      have hf : word.any id = false := by
        have := hz.mpr he
        cases hw : word.any id <;> simp_all
      simp [hf] at h
    omega
  · intro h
    have hn : word.any id ≠ false := by
      intro he
      have hv := hz.mp (by simp [he])
      omega
    cases hw : word.any id <;> simp_all

private theorem strict_sign (r : RawRat) (hr : r.Valid) :
    (r.negative && r.numerator.any id) = decide (r.value < 0) := by
  have hd : (0 : ℚ) < BitMachineBinaryMultiply.msbValue r.denominator := by
    exact_mod_cast hr
  have hnum := any_iff_value_pos r.numerator
  cases hs : r.negative <;> cases hn : r.numerator.any id
  · have hz : EncodedCommunication.bitsValue r.numerator = 0 := by
      have hnot : ¬ 0 < EncodedCommunication.bitsValue r.numerator := by
        intro hp
        have := hnum.mpr hp
        simp [hn] at this
      omega
    simp [RawRat.value, hs, hz]
  · have hp : (0 : ℚ) < EncodedCommunication.bitsValue r.numerator := by
      exact_mod_cast hnum.mp hn
    have hq : 0 < (EncodedCommunication.bitsValue r.numerator : ℚ) /
        BitMachineBinaryMultiply.msbValue r.denominator := div_pos hp hd
    simp [RawRat.value, hs, not_lt.mpr (le_of_lt hq)]
  · have hz : EncodedCommunication.bitsValue r.numerator = 0 := by
      have hnot : ¬ 0 < EncodedCommunication.bitsValue r.numerator := by
        intro hp
        have := hnum.mpr hp
        simp [hn] at this
      omega
    simp [RawRat.value, hs, hz]
  · have hp : (0 : ℚ) < EncodedCommunication.bitsValue r.numerator := by
      exact_mod_cast hnum.mp hn
    have hq : 0 < (EncodedCommunication.bitsValue r.numerator : ℚ) /
        BitMachineBinaryMultiply.msbValue r.denominator := div_pos hp hd
    simp [RawRat.value, hs, hq]

theorem result_pair (a b : RawRat) (ha : a.Valid) (hb : b.Valid) :
    result (CodeDPairProductTargetV2.pairBytes a b) =
      (if a.value < b.value then [true] else []) := by
  let r := RationalSubtractSpec.outputRat a b
  have hv : r.Valid := RationalSubtractSpec.output_valid a b ha hb
  have hvalue : r.value = a.value - b.value :=
    RationalSubtractSpec.output_value a b ha hb
  have hs := strict_sign r hv
  unfold result
  change RationalStrictNegative.result
    (RationalSubtractSerialized.result
      (RationalSubtractPairMachine.pairBytes a b)) = _
  rw [RationalSubtractSerialized.result_pair]
  change RationalStrictNegative.result (BitMachineBankCodec.encode (rawRatBank r)) = _
  simp only [RationalStrictNegative.result_encode]
  have hraw : ((rawRatBank r) 0).headD false = r.negative := by
    cases hs : r.negative <;> simp [rawRatBank, hs]
  have hnum : (rawRatBank r) 1 = r.numerator := by simp [rawRatBank]
  rw [hraw, hnum]
  change (if r.negative && r.numerator.any id then [true] else []) = _
  rw [hs, hvalue]
  simp

#print axioms outputs
#print axioms result_pair

end CurrentAdditive.RationalLess
