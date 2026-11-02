import CurrentAdditive.RationalProductPacket

/-!
Four logical little-endian operand words inside the physical twelve-field
packet. The second factor of each multiplication is reversed in the packet,
so the machine's MSB scan computes the intended natural-number product.
-/

namespace EthInapproximability.CurrentPaper.RationalProductAdapter

open RationalProductPacket RationalProductCore

def fourWords (a b c d : List Bool) : Fin 4 → List Bool := ![a,b,c,d]

def physicalInput (words : Fin 4 → List Bool) : List Bool :=
  packedInput (words 0) (words 1) (words 2).reverse (words 3).reverse

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

theorem physical_output (words : Fin 4 → List Bool) :
    RationalProductPacket.decodeProducts
        (RationalProductPacket.result (physicalInput words)) =
      some (EncodedCommunication.bitsValue (words 0) *
          EncodedCommunication.bitsValue (words 2),
        EncodedCommunication.bitsValue (words 1) *
          EncodedCommunication.bitsValue (words 3)) := by
  simp only [physicalInput, RationalProductPacket.decode_packed_output,
    msbValue_reverse]

theorem four_product (a b c d : List Bool) :
    RationalProductPacket.decodeProducts
        (RationalProductPacket.result (physicalInput (fourWords a b c d))) =
      some (EncodedCommunication.bitsValue a * EncodedCommunication.bitsValue c,
        EncodedCommunication.bitsValue b * EncodedCommunication.bitsValue d) := by
  simpa [fourWords] using physical_output (fourWords a b c d)

theorem positive_denominator (words : Fin 4 → List Bool)
    (hb : 0 < EncodedCommunication.bitsValue (words 1))
    (hd : 0 < EncodedCommunication.bitsValue (words 3)) :
    ∃ n d, RationalProductPacket.decodeProducts
        (RationalProductPacket.result (physicalInput words)) = some (n,d) ∧
      0 < d := by
  refine ⟨EncodedCommunication.bitsValue (words 0) *
      EncodedCommunication.bitsValue (words 2),
    EncodedCommunication.bitsValue (words 1) *
      EncodedCommunication.bitsValue (words 3), physical_output words, ?_⟩
  exact Nat.mul_pos hb hd

theorem physical_outputs (words : Fin 4 → List Bool) :
    RationalProductPacket.machine.OutputsWithin
      (physicalInput words)
      (RationalProductPacket.result (physicalInput words))
      (200 * ((physicalInput words).length + 1) ^ 2) := by
  unfold physicalInput
  rw [RationalProductPacket.packed_output]
  exact RationalProductPacket.packed_outputs
    (words 0) (words 1) (words 2).reverse (words 3).reverse

/-- Semantic reading of a pair of natural-number words as a rational. The
machine itself keeps the unreduced numerator and denominator. -/
def value (numerator denominator : List Bool) : ℚ :=
  (EncodedCommunication.bitsValue numerator : ℚ) /
    (EncodedCommunication.bitsValue denominator : ℚ)

def decodedValue (packet : List Bool) : Option ℚ := do
  let (n, d) ← RationalProductPacket.decodeProducts packet
  if d = 0 then none else some ((n : ℚ) / (d : ℚ))

theorem decodedValue_product (words : Fin 4 → List Bool)
    (hb : 0 < EncodedCommunication.bitsValue (words 1))
    (hd : 0 < EncodedCommunication.bitsValue (words 3)) :
    decodedValue (RationalProductPacket.result (physicalInput words)) =
      some (value (words 0) (words 1) * value (words 2) (words 3)) := by
  have hpos := Nat.mul_pos hb hd
  simp [decodedValue, physical_output, hpos.ne', value,
    Nat.cast_mul, div_mul_div_comm]

theorem decodedValue_product_four (a b c d : List Bool)
    (hb : 0 < EncodedCommunication.bitsValue b)
    (hd : 0 < EncodedCommunication.bitsValue d) :
    decodedValue (RationalProductPacket.result
        (physicalInput (fourWords a b c d))) =
      some (value a b * value c d) := by
  simpa [fourWords] using decodedValue_product (fourWords a b c d) hb hd

end EthInapproximability.CurrentPaper.RationalProductAdapter
