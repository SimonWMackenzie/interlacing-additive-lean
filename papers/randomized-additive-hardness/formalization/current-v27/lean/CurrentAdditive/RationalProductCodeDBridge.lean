import CurrentAdditive.RationalProductRawRat
import CurrentAdditive.CodeDCodec

/-!
Semantic bridge from the frozen Code D `RawRat` structure to the physical
twelve-field rational-product packet. Output denominator reversal into the
three-field `RawRat` ABI is exposed here as a pure reading function; the
controller must implement that reversal with bit operations.
-/

namespace EthInapproximability.CurrentPaper.RationalProductCodeDBridge

open RationalProductPacket RationalProductRawRat

def Positive (r : CurrentAdditive.CodeDCodec.RawRat) : Prop :=
  r.negative = false ∧
    0 < EncodedCommunication.bitsValue r.numerator ∧
    r.Valid

def physicalInput (x y : CurrentAdditive.CodeDCodec.RawRat) : List Bool :=
  RationalProductRawRat.physicalInput
    (CurrentAdditive.CodeDCodec.rawRatBank x)
    (CurrentAdditive.CodeDCodec.rawRatBank y)

theorem bank_positive (r : CurrentAdditive.CodeDCodec.RawRat)
    (hr : Positive r) :
    RationalProductRawRat.positive (CurrentAdditive.CodeDCodec.rawRatBank r) := by
  rcases hr with ⟨hs, hn, hd⟩
  refine ⟨?_, ?_, ?_⟩
  · simp [CurrentAdditive.CodeDCodec.rawRatBank, hs]
  · simpa [CurrentAdditive.CodeDCodec.rawRatBank] using hn
  · simpa [CurrentAdditive.CodeDCodec.rawRatBank,
      CurrentAdditive.CodeDCodec.RawRat.Valid] using hd

theorem bank_value (r : CurrentAdditive.CodeDCodec.RawRat)
    (hr : Positive r) :
    RationalProductRawRat.value (CurrentAdditive.CodeDCodec.rawRatBank r) =
      r.value := by
  simp [RationalProductRawRat.value, CurrentAdditive.CodeDCodec.RawRat.value,
    CurrentAdditive.CodeDCodec.rawRatBank, hr.1]

theorem product_value (x y : CurrentAdditive.CodeDCodec.RawRat)
    (hx : Positive x) (hy : Positive y) :
    RationalProductAdapter.decodedValue
        (RationalProductPacket.result (physicalInput x y)) =
      some (x.value * y.value) := by
  have h := RationalProductRawRat.product_value
    (CurrentAdditive.CodeDCodec.rawRatBank x)
    (CurrentAdditive.CodeDCodec.rawRatBank y)
    (bank_positive x hx) (bank_positive y hy)
  simpa only [physicalInput, bank_value x hx, bank_value y hy] using h

/-- Semantic reading of the packed product as a Code D `RawRat`. This is
not yet a physical three-field repacking machine. -/
def readOutput (packet : List Bool) :
    Option CurrentAdditive.CodeDCodec.RawRat := do
  let S ← BitMachineBankCodec.decode 12 packet
  pure ⟨false, S 0, (S 6).reverse⟩

theorem readOutput_eq_map (packet : List Bool) :
    readOutput packet =
      (RationalProductRawRat.reinterpret packet).map
        (fun z => (⟨false, z 1, z 2⟩ : CurrentAdditive.CodeDCodec.RawRat)) := by
  unfold readOutput RationalProductRawRat.reinterpret
  cases h : BitMachineBankCodec.decode 12 packet <;> simp

theorem readOutput_product (x y : CurrentAdditive.CodeDCodec.RawRat)
    (hx : Positive x) (hy : Positive y) :
    ∃ z, readOutput (RationalProductPacket.result (physicalInput x y)) =
      some z ∧ z.Valid ∧ z.value = x.value * y.value := by
  obtain ⟨z, hz, hzp, hzv⟩ := RationalProductRawRat.reinterpret_value
    (CurrentAdditive.CodeDCodec.rawRatBank x)
    (CurrentAdditive.CodeDCodec.rawRatBank y)
    (bank_positive x hx) (bank_positive y hy)
  let out : CurrentAdditive.CodeDCodec.RawRat := ⟨false, z 1, z 2⟩
  refine ⟨out, ?_, ?_, ?_⟩
  · rw [readOutput_eq_map]
    unfold physicalInput
    rw [hz]
    rfl
  · exact hzp.2.2
  · rw [bank_value x hx, bank_value y hy] at hzv
    simpa [out, RationalProductRawRat.value,
      CurrentAdditive.CodeDCodec.RawRat.value] using hzv

end EthInapproximability.CurrentPaper.RationalProductCodeDBridge
