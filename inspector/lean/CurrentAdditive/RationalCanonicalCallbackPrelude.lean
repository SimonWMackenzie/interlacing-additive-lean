import CurrentAdditive.RationalRouterAllInputJoin
import CurrentAdditive.CodeDCanonicalSource
import EthInapproximability.CurrentPaper.BitMachineCompositionArithmetic

namespace CurrentAdditive.RationalCanonicalCallbackPrelude

open EthInapproximability.CurrentPaper
open CodeDCodec
open CodeDPairProductTargetV2

noncomputable def productMachine (N : BitMachine.Machine) :
    BitMachine.Machine :=
  BitMachineComposition.composition
    RationalRouterProductJoin.signedProductMachine N

noncomputable def quotientMachine (N : BitMachine.Machine) :
    BitMachine.Machine :=
  BitMachineComposition.composition
    RationalRouterQuotientJoin.signedQuotientMachine N

theorem product_outputs_all (N : BitMachine.Machine)
    (normalize : List Bool → List Bool) (a c d : Nat)
    (hrouter : ∀ input,
      RationalRouterProductJoin.signedProductMachine.OutputsWithin input
        (RationalRouterAllInputJoin.productResult input)
        (a*(input.length+1)^15))
    (hnorm : ∀ input, N.OutputsWithin input (normalize input)
      (c*(input.length+1)^d))
    (input : List Bool) :
    (productMachine N).OutputsWithin input
      (normalize (RationalRouterAllInputJoin.productResult input))
      ((a + 2*(a*RationalRouterProductJoin.signedProductMachine.pushBound+1) +
        c*(a*RationalRouterProductJoin.signedProductMachine.pushBound+1)^d) *
        (input.length+1)^((15+1)*(d+1))) := by
  have hraw := BitMachineComposition.composition_outputsWithin
    RationalRouterProductJoin.signedProductMachine N
    (hrouter input)
    (hnorm (RationalRouterAllInputJoin.productResult input))
  have hlen := BitMachine.output_length_bound
    RationalRouterProductJoin.signedProductMachine (hrouter input)
  apply BitMachine.outputsWithin_mono _ hraw
  exact BitMachineCompositionArithmetic.composition_time_bound
    input.length a 15 c d
    RationalRouterProductJoin.signedProductMachine.pushBound
    (RationalRouterAllInputJoin.productResult input).length hlen

theorem quotient_outputs_all (N : BitMachine.Machine)
    (normalize : List Bool → List Bool) (a c d : Nat)
    (hrouter : ∀ input,
      RationalRouterQuotientJoin.signedQuotientMachine.OutputsWithin input
        (RationalRouterAllInputJoin.quotientResult input)
        (a*(input.length+1)^15))
    (hnorm : ∀ input, N.OutputsWithin input (normalize input)
      (c*(input.length+1)^d))
    (input : List Bool) :
    (quotientMachine N).OutputsWithin input
      (normalize (RationalRouterAllInputJoin.quotientResult input))
      ((a + 2*(a*RationalRouterQuotientJoin.signedQuotientMachine.pushBound+1) +
        c*(a*RationalRouterQuotientJoin.signedQuotientMachine.pushBound+1)^d) *
        (input.length+1)^((15+1)*(d+1))) := by
  have hraw := BitMachineComposition.composition_outputsWithin
    RationalRouterQuotientJoin.signedQuotientMachine N
    (hrouter input)
    (hnorm (RationalRouterAllInputJoin.quotientResult input))
  have hlen := BitMachine.output_length_bound
    RationalRouterQuotientJoin.signedQuotientMachine (hrouter input)
  apply BitMachine.outputsWithin_mono _ hraw
  exact BitMachineCompositionArithmetic.composition_time_bound
    input.length a 15 c d
    RationalRouterQuotientJoin.signedQuotientMachine.pushBound
    (RationalRouterAllInputJoin.quotientResult input).length hlen

theorem product_canonical_pair
    (normalize : List Bool → List Bool)
    (hcanon : ∀ r : RawRat, r.Valid →
      normalize (encodeRawRat r) =
        encodeRawRat (CodeDCanonicalSource.rawOfRat r.value))
    (x y : RawRat) (hx : x.Valid) (hy : y.Valid) :
    normalize (RationalRouterAllInputJoin.productResult (pairBytes x y)) =
      encodeRawRat (CodeDCanonicalSource.rawOfRat (x.value*y.value)) := by
  rw [RationalRouterAllInputJoin.product_result_pair,
    hcanon _ (RationalProductSignedPhysical.productRat_valid x y hx hy),
    RationalProductSignedPhysical.productRat_value]

theorem quotient_canonical_pair
    (normalize : List Bool → List Bool)
    (hcanon : ∀ r : RawRat, r.Valid →
      normalize (encodeRawRat r) =
        encodeRawRat (CodeDCanonicalSource.rawOfRat r.value))
    (x y : RawRat) (hx : x.Valid) (hy : y.Valid)
    (hnum : 0 < EncodedCommunication.bitsValue y.numerator) :
    normalize (RationalRouterAllInputJoin.quotientResult (pairBytes x y)) =
      encodeRawRat (CodeDCanonicalSource.rawOfRat (x.value/y.value)) := by
  rw [RationalRouterAllInputJoin.quotient_result_pair,
    hcanon _ (RationalProductSignedPhysical.quotientRat_valid x y hx hnum),
    RationalProductSignedPhysical.quotientRat_value x y hx hy hnum]

#print axioms product_outputs_all
#print axioms quotient_outputs_all
#print axioms product_canonical_pair
#print axioms quotient_canonical_pair

end CurrentAdditive.RationalCanonicalCallbackPrelude
