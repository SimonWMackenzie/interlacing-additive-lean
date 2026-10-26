import CurrentAdditive.RationalCanonicalCallbackPrelude
import CurrentAdditive.RawRatPacketTotal

namespace CurrentAdditive.RationalCanonicalCallback

open EthInapproximability.CurrentPaper
open CodeDCodec CodeDPairProductTargetV2

noncomputable def productMachine : BitMachine.Machine :=
  RationalCanonicalCallbackPrelude.productMachine RawRatPacketTotal.machine

noncomputable def quotientMachine : BitMachine.Machine :=
  RationalCanonicalCallbackPrelude.quotientMachine RawRatPacketTotal.machine

noncomputable def productResult : List Bool → List Bool :=
  RawRatPacketTotal.result ∘ RationalRouterAllInputJoin.productResult

noncomputable def quotientResult : List Bool → List Bool :=
  RawRatPacketTotal.result ∘ RationalRouterAllInputJoin.quotientResult

theorem product_outputs_all :
    ∃ c : Nat, ∀ input : List Bool,
      productMachine.OutputsWithin input (productResult input)
        (c*(input.length+1)^96) := by
  have hex : ∃ a : Nat, ∀ input,
      RationalRouterProductJoin.signedProductMachine.OutputsWithin input
        (RationalRouterAllInputJoin.productResult input)
        (a*(input.length+1)^15) := by
    exact ⟨_, RationalRouterAllInputJoin.product_outputs_all⟩
  obtain ⟨a,ha⟩ := hex
  refine ⟨a + 2*(a*RationalRouterProductJoin.signedProductMachine.pushBound+1) +
    RawRatPacketTotal.polynomialCoefficient *
      (a*RationalRouterProductJoin.signedProductMachine.pushBound+1)^5, ?_⟩
  intro input
  simpa [productMachine, productResult, Function.comp_def] using
    (RationalCanonicalCallbackPrelude.product_outputs_all
      RawRatPacketTotal.machine RawRatPacketTotal.result
      a RawRatPacketTotal.polynomialCoefficient 5 ha
      RawRatPacketTotal.outputsWithin input)

theorem quotient_outputs_all :
    ∃ c : Nat, ∀ input : List Bool,
      quotientMachine.OutputsWithin input (quotientResult input)
        (c*(input.length+1)^96) := by
  have hex : ∃ a : Nat, ∀ input,
      RationalRouterQuotientJoin.signedQuotientMachine.OutputsWithin input
        (RationalRouterAllInputJoin.quotientResult input)
        (a*(input.length+1)^15) := by
    exact ⟨_, RationalRouterAllInputJoin.quotient_outputs_all⟩
  obtain ⟨a,ha⟩ := hex
  refine ⟨a + 2*(a*RationalRouterQuotientJoin.signedQuotientMachine.pushBound+1) +
    RawRatPacketTotal.polynomialCoefficient *
      (a*RationalRouterQuotientJoin.signedQuotientMachine.pushBound+1)^5, ?_⟩
  intro input
  simpa [quotientMachine, quotientResult, Function.comp_def] using
    (RationalCanonicalCallbackPrelude.quotient_outputs_all
      RawRatPacketTotal.machine RawRatPacketTotal.result
      a RawRatPacketTotal.polynomialCoefficient 5 ha
      RawRatPacketTotal.outputsWithin input)

theorem product_polytime : BitMachine.Polytime productResult := by
  obtain ⟨c,h⟩ := product_outputs_all
  exact ⟨productMachine,c,96,h⟩

theorem quotient_polytime : BitMachine.Polytime quotientResult := by
  obtain ⟨c,h⟩ := quotient_outputs_all
  exact ⟨quotientMachine,c,96,h⟩

theorem product_result_pair (x y : RawRat)
    (hx : x.Valid) (hy : y.Valid) :
    productResult (pairBytes x y) =
      encodeRawRat (CodeDCanonicalSource.rawOfRat (x.value*y.value)) := by
  exact RationalCanonicalCallbackPrelude.product_canonical_pair
    RawRatPacketTotal.result RawRatPacketTotal.canonical_result x y hx hy

theorem quotient_result_pair (x y : RawRat)
    (hx : x.Valid) (hy : y.Valid)
    (hnum : 0 < EncodedCommunication.bitsValue y.numerator) :
    quotientResult (pairBytes x y) =
      encodeRawRat (CodeDCanonicalSource.rawOfRat (x.value/y.value)) := by
  exact RationalCanonicalCallbackPrelude.quotient_canonical_pair
    RawRatPacketTotal.result RawRatPacketTotal.canonical_result
    x y hx hy hnum

theorem product_outputs_pair (x y : RawRat)
    (hx : x.Valid) (hy : y.Valid) :
    ∃ c : Nat, productMachine.OutputsWithin (pairBytes x y)
      (encodeRawRat (CodeDCanonicalSource.rawOfRat (x.value*y.value)))
      (c*((pairBytes x y).length+1)^96) := by
  obtain ⟨c,h⟩ := product_outputs_all
  exact ⟨c,by simpa only [product_result_pair x y hx hy] using
    (h (pairBytes x y))⟩

theorem quotient_outputs_pair (x y : RawRat)
    (hx : x.Valid) (hy : y.Valid)
    (hnum : 0 < EncodedCommunication.bitsValue y.numerator) :
    ∃ c : Nat, quotientMachine.OutputsWithin (pairBytes x y)
      (encodeRawRat (CodeDCanonicalSource.rawOfRat (x.value/y.value)))
      (c*((pairBytes x y).length+1)^96) := by
  obtain ⟨c,h⟩ := quotient_outputs_all
  exact ⟨c,by simpa only [quotient_result_pair x y hx hy hnum] using
    (h (pairBytes x y))⟩

#print axioms product_outputs_all
#print axioms quotient_outputs_all
#print axioms product_polytime
#print axioms quotient_polytime
#print axioms product_result_pair
#print axioms quotient_result_pair
#print axioms product_outputs_pair
#print axioms quotient_outputs_pair

end CurrentAdditive.RationalCanonicalCallback
