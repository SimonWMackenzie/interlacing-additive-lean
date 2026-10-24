import CurrentAdditive.RationalRouterProductJoin
import CurrentAdditive.RationalRouterQuotientJoin

namespace CurrentAdditive.RationalRouterTargetBridge

open EthInapproximability.CurrentPaper
open CodeDCodec
open CodeDPairProductTargetV2

theorem product_packet_outputs (x y : RawRat) (hx : x.Valid) (hy : y.Valid) :
    RationalRouterProductJoin.packetMachine.OutputsWithin
      (pairBytes x y) (productPacket (pairBytes x y))
      (120*((pairBytes x y).length+1)) := by
  rw [productPacket_pairBytes x y hx hy]
  exact RationalRouterProductJoin.packet_outputs x y

theorem quotient_packet_outputs (x y : RawRat) (hx : x.Valid) (hy : y.Valid) :
    RationalRouterQuotientJoin.packetMachine.OutputsWithin
      (pairBytes x y) (quotientPacket (pairBytes x y))
      (120*((pairBytes x y).length+1)) := by
  rw [quotientPacket_pairBytes x y hx hy]
  exact RationalRouterQuotientJoin.packet_outputs x y

theorem product_encoded_outputs (x y : RawRat) :
    RationalRouterProductJoin.signedProductMachine.OutputsWithin
      (pairBytes x y)
      (encodeRawRat (RationalProductSignedPhysical.productRat x y))
      (15000*((pairBytes x y).length+1)^2) ∧
      (RationalProductSignedPhysical.productRat x y).value =
        x.value*y.value := by
  exact ⟨RationalRouterProductJoin.signed_product_outputs x y,
    RationalProductSignedPhysical.productRat_value x y⟩

theorem quotient_encoded_outputs (x y : RawRat) (hx : x.Valid)
    (hy : y.Valid) (hnum : 0 < EncodedCommunication.bitsValue y.numerator) :
    RationalRouterQuotientJoin.signedQuotientMachine.OutputsWithin
      (pairBytes x y)
      (encodeRawRat (RationalProductSignedPhysical.quotientRat x y))
      (15000*((pairBytes x y).length+1)^2) ∧
      (RationalProductSignedPhysical.quotientRat x y).value =
        x.value/y.value := by
  exact ⟨RationalRouterQuotientJoin.signed_quotient_outputs x y,
    RationalProductSignedPhysical.quotientRat_value x y hx hy hnum⟩

#print axioms product_packet_outputs
#print axioms quotient_packet_outputs
#print axioms product_encoded_outputs
#print axioms quotient_encoded_outputs

end CurrentAdditive.RationalRouterTargetBridge
