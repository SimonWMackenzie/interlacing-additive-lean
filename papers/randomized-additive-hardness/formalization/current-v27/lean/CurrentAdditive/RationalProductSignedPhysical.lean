import CurrentAdditive.RationalProductSignedRepack
import CurrentAdditive.RationalProductPhysical

/-!
Signed RawRat multiplication and quotient packet primitives.  The first
source word carries the intended output sign in its length parity; a single
high-order zero bit adjusts parity without changing its unsigned value.
The product machine preserves that source word in field 3.  The signed
repacker physically counts its bits, writes the sign field, reverses the
denominator, and serializes the three-field Code D packet.
-/

namespace EthInapproximability.CurrentPaper.RationalProductSignedPhysical

open RationalProductPacket RationalProductSignedRepack

noncomputable def machine : BitMachine.Machine :=
  BitMachineComposition.composition RationalProductPacket.machine
    RationalProductSignedRepack.machine

def result : List Bool → List Bool :=
  RationalProductSignedRepack.result ∘ RationalProductPacket.result

theorem outputs (input : List Bool) :
    machine.OutputsWithin input (result input)
      (1300*(input.length+1)^2) := by
  let middle := RationalProductPacket.result input
  have ha : RationalProductPacket.machine.OutputsWithin input middle
      (200*(input.length+1)^2) := by
    apply BitMachine.outputsWithin_mono RationalProductPacket.machine
      (RationalProductPacket.outputs input)
    have hp : 1 ≤ input.length+1 := by omega
    nlinarith
  have h := BitMachineComposition.composition_outputsWithin
    RationalProductPacket.machine RationalProductSignedRepack.machine
    ha (RationalProductSignedRepack.outputs middle)
  change machine.OutputsWithin input (result input)
    (200*(input.length+1)^2 + 2*middle.length+2 + 50*(middle.length+1)) at h
  apply BitMachine.outputsWithin_mono machine h
  have hm : middle.length ≤ 20*(input.length+1) :=
    RationalProductPhysical.middle_length input
  have hp : 1 ≤ input.length+1 := by omega
  nlinarith

theorem polytime : BitMachine.Polytime result := by
  refine ⟨machine, 1300, 2, ?_⟩
  intro input
  exact outputs input

def parityPad (w : List Bool) (s : Bool) : List Bool :=
  if signParity w == s then w else w ++ [false]

theorem signParity_append_false (w : List Bool) :
    signParity (w ++ [false]) = !signParity w := by
  induction w with
  | nil => rfl
  | cons b w ih => simp [signParity, ih]

theorem parityPad_parity (w : List Bool) (s : Bool) :
    signParity (parityPad w s) = s := by
  cases hs : signParity w <;> cases s <;>
    simp [parityPad, signParity_append_false, hs]

theorem parityPad_value (w : List Bool) (s : Bool) :
    EncodedCommunication.bitsValue (parityPad w s) =
      EncodedCommunication.bitsValue w := by
  unfold parityPad
  split
  · rfl
  · rw [BitMachineBinaryAdd.bitsValue_append_high]
    simp

theorem parityPad_length (w : List Bool) (s : Bool) :
    (parityPad w s).length ≤ w.length+1 := by
  unfold parityPad
  split <;> simp

def productInput (x y : CurrentAdditive.CodeDCodec.RawRat) : List Bool :=
  RationalProductPacket.packedInput
    (parityPad x.numerator (x.negative != y.negative))
    x.denominator.reverse y.numerator.reverse y.denominator

def quotientInput (x y : CurrentAdditive.CodeDCodec.RawRat) : List Bool :=
  RationalProductPacket.packedInput
    (parityPad x.numerator (x.negative != y.negative))
    x.denominator.reverse y.denominator y.numerator.reverse

def outputRat (a b c d : List Bool) : CurrentAdditive.CodeDCodec.RawRat :=
  ⟨signParity a,
    (RationalProductCore.outputBank a b c d) 0,
    ((RationalProductCore.outputBank a b c d) 6).reverse⟩

theorem result_packet (a b c d : List Bool) :
    result (RationalProductPacket.packedInput a b c d) =
      CurrentAdditive.CodeDCodec.encodeRawRat (outputRat a b c d) := by
  change RationalProductSignedRepack.result
    (RationalProductPacket.result (RationalProductPacket.packedInput a b c d)) = _
  rw [RationalProductPacket.packed_output]
  rw [RationalProductSignedRepack.result_eq_rawRat]
  have hs : RationalProductCore.outputBank a b c d 3 = a := by
    rfl
  simp only [outputRat, hs]

theorem result_product (x y : CurrentAdditive.CodeDCodec.RawRat) :
    result (productInput x y) =
      CurrentAdditive.CodeDCodec.encodeRawRat
        (outputRat (parityPad x.numerator (x.negative != y.negative))
          x.denominator.reverse y.numerator.reverse y.denominator) := by
  exact result_packet _ _ _ _

theorem result_quotient (x y : CurrentAdditive.CodeDCodec.RawRat) :
    result (quotientInput x y) =
      CurrentAdditive.CodeDCodec.encodeRawRat
        (outputRat (parityPad x.numerator (x.negative != y.negative))
          x.denominator.reverse y.denominator y.numerator.reverse) := by
  exact result_packet _ _ _ _

def productRat (x y : CurrentAdditive.CodeDCodec.RawRat) :
    CurrentAdditive.CodeDCodec.RawRat :=
  outputRat (parityPad x.numerator (x.negative != y.negative))
    x.denominator.reverse y.numerator.reverse y.denominator

def quotientRat (x y : CurrentAdditive.CodeDCodec.RawRat) :
    CurrentAdditive.CodeDCodec.RawRat :=
  outputRat (parityPad x.numerator (x.negative != y.negative))
    x.denominator.reverse y.denominator y.numerator.reverse

theorem productRat_sign (x y : CurrentAdditive.CodeDCodec.RawRat) :
    (productRat x y).negative = (x.negative != y.negative) := by
  exact parityPad_parity _ _

theorem quotientRat_sign (x y : CurrentAdditive.CodeDCodec.RawRat) :
    (quotientRat x y).negative = (x.negative != y.negative) := by
  exact parityPad_parity _ _

theorem productRat_numerator (x y : CurrentAdditive.CodeDCodec.RawRat) :
    EncodedCommunication.bitsValue (productRat x y).numerator =
      EncodedCommunication.bitsValue x.numerator *
        EncodedCommunication.bitsValue y.numerator := by
  change EncodedCommunication.bitsValue (RationalProductCore.outputBank
    (parityPad x.numerator (x.negative != y.negative))
    x.denominator.reverse y.numerator.reverse y.denominator 0) = _
  rw [RationalProductCore.numerator_value,
    RationalProductAdapter.msbValue_reverse, parityPad_value]

theorem productRat_denominator (x y : CurrentAdditive.CodeDCodec.RawRat) :
    BitMachineBinaryMultiply.msbValue (productRat x y).denominator =
      BitMachineBinaryMultiply.msbValue x.denominator *
        BitMachineBinaryMultiply.msbValue y.denominator := by
  change BitMachineBinaryMultiply.msbValue
    ((RationalProductCore.outputBank
      (parityPad x.numerator (x.negative != y.negative))
      x.denominator.reverse y.numerator.reverse y.denominator 6).reverse) = _
  rw [RationalProductAdapter.msbValue_reverse,
    RationalProductCore.denominator_value,
    RationalProductRawRat.bitsValue_reverse]

theorem quotientRat_numerator (x y : CurrentAdditive.CodeDCodec.RawRat) :
    EncodedCommunication.bitsValue (quotientRat x y).numerator =
      EncodedCommunication.bitsValue x.numerator *
        BitMachineBinaryMultiply.msbValue y.denominator := by
  change EncodedCommunication.bitsValue (RationalProductCore.outputBank
    (parityPad x.numerator (x.negative != y.negative))
    x.denominator.reverse y.denominator y.numerator.reverse 0) = _
  rw [RationalProductCore.numerator_value, parityPad_value]

theorem quotientRat_denominator (x y : CurrentAdditive.CodeDCodec.RawRat) :
    BitMachineBinaryMultiply.msbValue (quotientRat x y).denominator =
      BitMachineBinaryMultiply.msbValue x.denominator *
        EncodedCommunication.bitsValue y.numerator := by
  change BitMachineBinaryMultiply.msbValue
    ((RationalProductCore.outputBank
      (parityPad x.numerator (x.negative != y.negative))
      x.denominator.reverse y.denominator y.numerator.reverse 6).reverse) = _
  rw [RationalProductAdapter.msbValue_reverse,
    RationalProductCore.denominator_value,
    RationalProductRawRat.bitsValue_reverse,
    RationalProductAdapter.msbValue_reverse]

theorem productRat_valid (x y : CurrentAdditive.CodeDCodec.RawRat)
    (hx : x.Valid) (hy : y.Valid) : (productRat x y).Valid := by
  rw [CurrentAdditive.CodeDCodec.RawRat.Valid, productRat_denominator]
  exact Nat.mul_pos hx hy

theorem quotientRat_valid (x y : CurrentAdditive.CodeDCodec.RawRat)
    (hx : x.Valid) (hy : 0 < EncodedCommunication.bitsValue y.numerator) :
    (quotientRat x y).Valid := by
  rw [CurrentAdditive.CodeDCodec.RawRat.Valid, quotientRat_denominator]
  exact Nat.mul_pos hx hy

theorem productRat_value (x y : CurrentAdditive.CodeDCodec.RawRat) :
    (productRat x y).value = x.value * y.value := by
  simp only [CurrentAdditive.CodeDCodec.RawRat.value,
    productRat_sign, productRat_numerator, productRat_denominator,
    Nat.cast_mul, div_mul_div_comm]
  cases x.negative <;> cases y.negative <;> norm_num <;> ring

theorem quotientRat_value (x y : CurrentAdditive.CodeDCodec.RawRat)
    (hx : x.Valid) (hy : y.Valid)
    (hyn : 0 < EncodedCommunication.bitsValue y.numerator) :
    (quotientRat x y).value = x.value / y.value := by
  have hxd : (BitMachineBinaryMultiply.msbValue x.denominator : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hx)
  have hyd : (BitMachineBinaryMultiply.msbValue y.denominator : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hy)
  have hyn' : (EncodedCommunication.bitsValue y.numerator : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hyn)
  simp only [CurrentAdditive.CodeDCodec.RawRat.value,
    quotientRat_sign, quotientRat_numerator, quotientRat_denominator,
    Nat.cast_mul]
  cases x.negative <;> cases y.negative <;>
    simp <;> field_simp <;> ring

theorem product_decoded (x y : CurrentAdditive.CodeDCodec.RawRat)
    (hx : x.Valid) (hy : y.Valid) :
    CurrentAdditive.CodeDCodec.decodeRawRat (result (productInput x y)) =
      some (productRat x y) ∧
    (productRat x y).value = x.value * y.value := by
  constructor
  · rw [result_product]
    exact CurrentAdditive.CodeDCodec.decodeRawRat_encodeRawRat _
      (productRat_valid x y hx hy)
  · exact productRat_value x y

theorem quotient_decoded (x y : CurrentAdditive.CodeDCodec.RawRat)
    (hx : x.Valid) (hy : y.Valid)
    (hyn : 0 < EncodedCommunication.bitsValue y.numerator) :
    CurrentAdditive.CodeDCodec.decodeRawRat (result (quotientInput x y)) =
      some (quotientRat x y) ∧
    (quotientRat x y).value = x.value / y.value := by
  constructor
  · rw [result_quotient]
    exact CurrentAdditive.CodeDCodec.decodeRawRat_encodeRawRat _
      (quotientRat_valid x y hx hyn)
  · exact quotientRat_value x y hx hy hyn

theorem product_outputs (x y : CurrentAdditive.CodeDCodec.RawRat) :
    machine.OutputsWithin (productInput x y)
      (CurrentAdditive.CodeDCodec.encodeRawRat (productRat x y))
      (1300*((productInput x y).length+1)^2) := by
  have h := outputs (productInput x y)
  rw [result_product] at h
  simpa only [productRat] using h

theorem quotient_outputs (x y : CurrentAdditive.CodeDCodec.RawRat) :
    machine.OutputsWithin (quotientInput x y)
      (CurrentAdditive.CodeDCodec.encodeRawRat (quotientRat x y))
      (1300*((quotientInput x y).length+1)^2) := by
  have h := outputs (quotientInput x y)
  rw [result_quotient] at h
  simpa only [quotientRat] using h

end EthInapproximability.CurrentPaper.RationalProductSignedPhysical
