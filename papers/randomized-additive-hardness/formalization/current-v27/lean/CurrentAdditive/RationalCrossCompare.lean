import CurrentAdditive.UnsignedComparePacket
import CurrentAdditive.RationalProductAdapter
import CurrentAdditive.CodeDCodec

/-!
Comparison of two positive encoded rationals by two physical multiplications
followed by a physical variable-width unsigned comparison. The transfer
between packet formats is an explicit semantic adapter here; its own machine
is a separate controller obligation.
-/

namespace EthInapproximability.CurrentPaper.RationalCrossCompare

open CurrentAdditive.CodeDCodec

def words (a b : RawRat) : Fin 4 → List Bool :=
  RationalProductAdapter.fourWords a.numerator b.numerator
    b.denominator.reverse a.denominator.reverse

def productInput (a b : RawRat) : List Bool :=
  RationalProductAdapter.physicalInput (words a b)

def productOutput (a b : RawRat) : List Bool :=
  RationalProductPacket.result (productInput a b)

def compareInput (a b : RawRat) : Option (List Bool) := do
  let S ← BitMachineBankCodec.decode 12 (productOutput a b)
  pure (UnsignedComparePacket.packedInput (S 0) (S 6))

def crossBorrow (a b : RawRat) : Option Bool := do
  let packet ← compareInput a b
  UnsignedComparePacket.decodeBorrow (UnsignedComparePacket.result packet)

theorem product_values (a b : RawRat) :
    RationalProductPacket.decodeProducts (productOutput a b) =
      some (EncodedCommunication.bitsValue a.numerator *
          BitMachineBinaryMultiply.msbValue b.denominator,
        EncodedCommunication.bitsValue b.numerator *
          BitMachineBinaryMultiply.msbValue a.denominator) := by
  have h := RationalProductAdapter.four_product a.numerator b.numerator
    b.denominator.reverse a.denominator.reverse
  have hb := RationalProductAdapter.msbValue_reverse b.denominator.reverse
  have ha := RationalProductAdapter.msbValue_reverse a.denominator.reverse
  simp only [List.reverse_reverse] at hb ha
  simpa only [productOutput, productInput, words, ← hb, ← ha] using h

theorem crossBorrow_correct (a b : RawRat) :
    crossBorrow a b = some
      (decide (EncodedCommunication.bitsValue a.numerator *
            BitMachineBinaryMultiply.msbValue b.denominator <
          EncodedCommunication.bitsValue b.numerator *
            BitMachineBinaryMultiply.msbValue a.denominator)) := by
  unfold crossBorrow compareInput
  have hp := product_values a b
  unfold RationalProductPacket.decodeProducts at hp
  cases hs : BitMachineBankCodec.decode 12 (productOutput a b) with
  | none => simp [hs] at hp
  | some S =>
      simp only [hs, Option.bind_some, Option.pure_def, Option.map_some] at hp
      have hpair := Option.some.inj hp
      have hn := congrArg Prod.fst hpair
      have hd := congrArg Prod.snd hpair
      simp only at hn hd
      simp [hs, UnsignedComparePacket.packed_borrow, hn, hd]

theorem crossBorrow_lt (a b : RawRat)
    (ha : a.Valid) (hb : b.Valid)
    (hsa : a.negative = false) (hsb : b.negative = false) :
    crossBorrow a b = some (decide (a.value < b.value)) := by
  rw [crossBorrow_correct]
  have hiff :
      EncodedCommunication.bitsValue a.numerator *
          BitMachineBinaryMultiply.msbValue b.denominator <
        EncodedCommunication.bitsValue b.numerator *
          BitMachineBinaryMultiply.msbValue a.denominator ↔
      a.value < b.value := by
    simp only [RawRat.value, hsa, hsb, Bool.false_eq_true, ↓reduceIte,
      one_mul]
    have hda : (0 : ℚ) < BitMachineBinaryMultiply.msbValue a.denominator := by
      exact_mod_cast ha
    have hdb : (0 : ℚ) < BitMachineBinaryMultiply.msbValue b.denominator := by
      exact_mod_cast hb
    rw [div_lt_div_iff₀ hda hdb]
    exact_mod_cast (Iff.rfl :
      EncodedCommunication.bitsValue a.numerator *
          BitMachineBinaryMultiply.msbValue b.denominator <
        EncodedCommunication.bitsValue b.numerator *
          BitMachineBinaryMultiply.msbValue a.denominator ↔ _)
  by_cases h : EncodedCommunication.bitsValue a.numerator *
      BitMachineBinaryMultiply.msbValue b.denominator <
    EncodedCommunication.bitsValue b.numerator *
      BitMachineBinaryMultiply.msbValue a.denominator
  · simp [h, hiff.mp h]
  · simp [h, (not_iff_not.mpr hiff).mp h]

#print axioms crossBorrow_correct
#print axioms crossBorrow_lt

end EthInapproximability.CurrentPaper.RationalCrossCompare
