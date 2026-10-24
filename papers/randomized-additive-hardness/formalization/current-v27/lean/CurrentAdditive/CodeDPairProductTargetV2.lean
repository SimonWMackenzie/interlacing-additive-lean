import CurrentAdditive.CodeDAppendTargetV2
import CurrentAdditive.RationalProductSignedPhysical

/-!
Exact two-rational operand packet expected by the physical signed product
primitive.  The Bank2-to-productInput routing program is a separate open
physical obligation; this file only identifies its input/output bytes and
checks the downstream machine/value interface.
-/

namespace CurrentAdditive.CodeDPairProductTargetV2

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineBankCodec
open CodeDCodec
open RationalProductSignedPhysical

def pairBank (x y : RawRat) : Bank 2 :=
  fun i => if i = 0 then encodeRawRat x else encodeRawRat y

def pairBytes (x y : RawRat) : List Bool := encode (pairBank x y)

def decodePair (input : List Bool) : Option (RawRat × RawRat) := do
  let S ← decode 2 input
  let x ← decodeRawRat (S 0)
  let y ← decodeRawRat (S 1)
  pure (x, y)

theorem decodePair_pairBytes (x y : RawRat) (hx : x.Valid) (hy : y.Valid) :
    decodePair (pairBytes x y) = some (x, y) := by
  simp [decodePair, pairBytes, pairBank,
    decodeRawRat_encodeRawRat, hx, hy]

def productPacket (input : List Bool) : List Bool :=
  match decodePair input with
  | none => []
  | some (x, y) => productInput x y

def quotientPacket (input : List Bool) : List Bool :=
  match decodePair input with
  | none => []
  | some (x, y) => quotientInput x y

theorem productPacket_pairBytes (x y : RawRat) (hx : x.Valid) (hy : y.Valid) :
    productPacket (pairBytes x y) = productInput x y := by
  simp [productPacket, decodePair_pairBytes x y hx hy]

theorem quotientPacket_pairBytes (x y : RawRat) (hx : x.Valid) (hy : y.Valid) :
    quotientPacket (pairBytes x y) = quotientInput x y := by
  simp [quotientPacket, decodePair_pairBytes x y hx hy]

theorem signed_product_after_packet (x y : RawRat)
    (hx : x.Valid) (hy : y.Valid) :
    RationalProductSignedPhysical.machine.OutputsWithin
      (productPacket (pairBytes x y))
      (encodeRawRat (productRat x y))
      (1300*((productPacket (pairBytes x y)).length+1)^2) ∧
    (productRat x y).value = x.value*y.value := by
  rw [productPacket_pairBytes x y hx hy]
  exact ⟨product_outputs x y, productRat_value x y⟩

#print axioms decodePair_pairBytes
#print axioms signed_product_after_packet

end CurrentAdditive.CodeDPairProductTargetV2
