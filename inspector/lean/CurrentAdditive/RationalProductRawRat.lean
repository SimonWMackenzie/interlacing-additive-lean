import CurrentAdditive.RationalProductAdapter

/-!
Semantic bridge to the current Code D three-field positive-rational ABI.
`RawRat` uses sign `[]`, little-endian numerator, and MSB-first positive
denominator. This module proves the exact reinterpretation of the product
machine's twelve-field output. Reversing the output denominator into a
three-field packet is a separate physical controller operation.
-/

namespace EthInapproximability.CurrentPaper.RationalProductRawRat

open RationalProductAdapter RationalProductPacket RationalProductCore

abbrev RawRat := Fin 3 → List Bool

def positive (x : RawRat) : Prop :=
  x 0 = [] ∧ 0 < EncodedCommunication.bitsValue (x 1) ∧
    0 < BitMachineBinaryMultiply.msbValue (x 2)

def value (x : RawRat) : ℚ :=
  (EncodedCommunication.bitsValue (x 1) : ℚ) /
    (BitMachineBinaryMultiply.msbValue (x 2) : ℚ)

def physicalInput (x y : RawRat) : List Bool :=
  RationalProductPacket.packedInput (x 1) (x 2).reverse
    (y 1).reverse (y 2)

theorem bitsValue_reverse (bits : List Bool) :
    EncodedCommunication.bitsValue bits.reverse =
      BitMachineBinaryMultiply.msbValue bits := by
  simpa using (RationalProductAdapter.msbValue_reverse bits.reverse).symm

theorem product_numbers (x y : RawRat) :
    decodeProducts (RationalProductPacket.result (physicalInput x y)) =
      some (EncodedCommunication.bitsValue (x 1) *
          EncodedCommunication.bitsValue (y 1),
        BitMachineBinaryMultiply.msbValue (x 2) *
          BitMachineBinaryMultiply.msbValue (y 2)) := by
  simp only [physicalInput, RationalProductPacket.decode_packed_output,
    bitsValue_reverse, RationalProductAdapter.msbValue_reverse]

theorem product_denominator_pos (x y : RawRat)
    (hx : positive x) (hy : positive y) :
    ∃ n d, decodeProducts (RationalProductPacket.result (physicalInput x y)) =
      some (n,d) ∧ 0 < d := by
  refine ⟨EncodedCommunication.bitsValue (x 1) *
      EncodedCommunication.bitsValue (y 1),
    BitMachineBinaryMultiply.msbValue (x 2) *
      BitMachineBinaryMultiply.msbValue (y 2), product_numbers x y, ?_⟩
  exact Nat.mul_pos hx.2.2 hy.2.2

theorem product_value (x y : RawRat)
    (hx : positive x) (hy : positive y) :
    RationalProductAdapter.decodedValue
        (RationalProductPacket.result (physicalInput x y)) =
      some (value x * value y) := by
  have hpos := Nat.mul_pos hx.2.2 hy.2.2
  simp [RationalProductAdapter.decodedValue, product_numbers,
    hpos.ne', value, Nat.cast_mul, div_mul_div_comm]

/-- Pure reading of a twelve-field product output as a three-field `RawRat`.
The reversal in field 2 is explicit; no claim is made that this projection is
already a physical machine instruction. -/
def reinterpret (packet : List Bool) : Option RawRat := do
  let S ← BitMachineBankCodec.decode 12 packet
  pure (![[], S 0, (S 6).reverse] : RawRat)

theorem reinterpret_product (x y : RawRat) :
    reinterpret (RationalProductPacket.result (physicalInput x y)) =
      some (![[], (outputBank (x 1) (x 2).reverse (y 1).reverse (y 2)) 0,
          ((outputBank (x 1) (x 2).reverse (y 1).reverse (y 2)) 6).reverse] : RawRat) := by
  simp [reinterpret, physicalInput, RationalProductPacket.packed_output]

theorem reinterpret_value (x y : RawRat)
    (hx : positive x) (hy : positive y) :
    ∃ z, reinterpret (RationalProductPacket.result (physicalInput x y)) =
      some z ∧ positive z ∧ value z = value x * value y := by
  let z : RawRat := ![[],
    (outputBank (x 1) (x 2).reverse (y 1).reverse (y 2)) 0,
    ((outputBank (x 1) (x 2).reverse (y 1).reverse (y 2)) 6).reverse]
  refine ⟨z, reinterpret_product x y, ?_, ?_⟩
  · constructor
    · rfl
    constructor
    · change 0 < EncodedCommunication.bitsValue
        (outputBank (x 1) (x 2).reverse (y 1).reverse (y 2) 0)
      rw [RationalProductCore.numerator_value,
        RationalProductAdapter.msbValue_reverse]
      exact Nat.mul_pos hx.2.1 hy.2.1
    · change 0 < BitMachineBinaryMultiply.msbValue
        ((outputBank (x 1) (x 2).reverse (y 1).reverse (y 2) 6).reverse)
      rw [RationalProductAdapter.msbValue_reverse,
        RationalProductCore.denominator_value, bitsValue_reverse]
      exact Nat.mul_pos hx.2.2 hy.2.2
  · change (EncodedCommunication.bitsValue
        (outputBank (x 1) (x 2).reverse (y 1).reverse (y 2) 0) : ℚ) /
        (BitMachineBinaryMultiply.msbValue
          ((outputBank (x 1) (x 2).reverse (y 1).reverse (y 2) 6).reverse) : ℚ) =
        value x * value y
    simp [RationalProductCore.numerator_value,
      RationalProductCore.denominator_value,
      RationalProductAdapter.msbValue_reverse,
      bitsValue_reverse, value, Nat.cast_mul, div_mul_div_comm]

end EthInapproximability.CurrentPaper.RationalProductRawRat
