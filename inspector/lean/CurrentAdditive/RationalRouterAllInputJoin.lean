import CurrentAdditive.RationalRouterTotal
import CurrentAdditive.RationalRouterQuotientTotal
import CurrentAdditive.RationalRouterTargetBridge
import EthInapproximability.CurrentPaper.BitMachineCompositionArithmetic

namespace CurrentAdditive.RationalRouterAllInputJoin

open EthInapproximability.CurrentPaper
open CodeDCodec
open CodeDPairProductTargetV2
open EthInapproximability.CurrentPaper.RationalProductNestedFlat

private def firstCoeff (A : BitMachine.Machine) (r : Nat) : Nat :=
  40 + 2*(40*A.pushBound+1) + r*(40*A.pushBound+1)

private noncomputable def finalCoeff (A B : BitMachine.Machine) (r : Nat) : Nat :=
  let P := BitMachineComposition.composition A B
  let c := firstCoeff A r
  c + 2*(c*P.pushBound+1) + 1300*(c*P.pushBound+1)^2

private theorem three_stage_outputs (A B C : BitMachine.Machine)
    (f g h : List Bool → List Bool) (r : Nat)
    (ha : ∀ input, A.OutputsWithin input (f input)
      (40*(input.length+1)))
    (hb : ∀ input, B.OutputsWithin input (g input)
      (r*(input.length+1)))
    (hc : ∀ input, C.OutputsWithin input (h input)
      (1300*(input.length+1)^2))
    (input : List Bool) :
    (BitMachineComposition.composition
      (BitMachineComposition.composition A B) C).OutputsWithin input
      (h (g (f input)))
      (finalCoeff A B r * (input.length+1)^15) := by
  let P := BitMachineComposition.composition A B
  let c := firstCoeff A r
  have habRaw := BitMachineComposition.composition_outputsWithin A B
    (ha input) (hb (f input))
  have hlenA := BitMachine.output_length_bound A (ha input)
  have hboundA := BitMachineCompositionArithmetic.composition_time_bound
    input.length 40 1 r 1 A.pushBound (f input).length
    (by simpa only [pow_one] using hlenA)
  have hab : P.OutputsWithin input (g (f input))
      (c*(input.length+1)^4) := by
    apply BitMachine.outputsWithin_mono P habRaw
    simpa [c, firstCoeff, P, pow_one] using hboundA
  have habcRaw := BitMachineComposition.composition_outputsWithin P C
    hab (hc (g (f input)))
  have hlenP := BitMachine.output_length_bound P hab
  have hboundP := BitMachineCompositionArithmetic.composition_time_bound
    input.length c 4 1300 2 P.pushBound (g (f input)).length hlenP
  apply BitMachine.outputsWithin_mono _ habcRaw
  simpa [finalCoeff, c, P] using hboundP

def productResult : List Bool → List Bool :=
  RationalProductSignedPhysical.result ∘
    RationalRouterProduct.productRouteResult ∘
      RationalNestedFlatTotal.result

def quotientResult : List Bool → List Bool :=
  RationalProductSignedPhysical.result ∘
    RationalRouterQuotient.quotientRouteResult ∘
      RationalNestedFlatTotal.result

theorem product_outputs_all (input : List Bool) :
    RationalRouterProductJoin.signedProductMachine.OutputsWithin input
      (productResult input)
      (finalCoeff RationalProductNestedFlat.machine
        RationalRouterProduct.productRouteMachine
        (25+100+2*RationalRouterTotal.productSizeConstant+4) *
          (input.length+1)^15) := by
  simpa [RationalRouterProductJoin.signedProductMachine,
    RationalRouterProductJoin.packetMachine, productResult,
    Function.comp_def] using
    (three_stage_outputs RationalProductNestedFlat.machine
      RationalRouterProduct.productRouteMachine
      RationalProductSignedPhysical.machine
      RationalNestedFlatTotal.result
      RationalRouterProduct.productRouteResult
      RationalProductSignedPhysical.result
      (25+100+2*RationalRouterTotal.productSizeConstant+4)
      RationalNestedFlatTotal.outputs
      RationalRouterTotal.product_route_outputs_all
      RationalProductSignedPhysical.outputs input)

theorem quotient_outputs_all (input : List Bool) :
    RationalRouterQuotientJoin.signedQuotientMachine.OutputsWithin input
      (quotientResult input)
      (finalCoeff RationalProductNestedFlat.machine
        RationalRouterQuotient.quotientRouteMachine
        (25+100+2*RationalRouterTotal.quotientSizeConstant+4) *
          (input.length+1)^15) := by
  simpa [RationalRouterQuotientJoin.signedQuotientMachine,
    RationalRouterQuotientJoin.packetMachine, quotientResult,
    Function.comp_def] using
    (three_stage_outputs RationalProductNestedFlat.machine
      RationalRouterQuotient.quotientRouteMachine
      RationalProductSignedPhysical.machine
      RationalNestedFlatTotal.result
      RationalRouterQuotient.quotientRouteResult
      RationalProductSignedPhysical.result
      (25+100+2*RationalRouterTotal.quotientSizeConstant+4)
      RationalNestedFlatTotal.outputs
      RationalRouterTotal.quotient_route_outputs_all
      RationalProductSignedPhysical.outputs input)

theorem product_polytime : BitMachine.Polytime productResult := by
  refine ⟨RationalRouterProductJoin.signedProductMachine,
    finalCoeff RationalProductNestedFlat.machine
      RationalRouterProduct.productRouteMachine
      (25+100+2*RationalRouterTotal.productSizeConstant+4), 15, ?_⟩
  exact product_outputs_all

theorem quotient_polytime : BitMachine.Polytime quotientResult := by
  refine ⟨RationalRouterQuotientJoin.signedQuotientMachine,
    finalCoeff RationalProductNestedFlat.machine
      RationalRouterQuotient.quotientRouteMachine
      (25+100+2*RationalRouterTotal.quotientSizeConstant+4), 15, ?_⟩
  exact quotient_outputs_all

theorem product_result_pair (x y : RawRat) :
    productResult (pairBytes x y) =
      encodeRawRat (RationalProductSignedPhysical.productRat x y) :=
  BitMachine.outputsWithin_unique _ (product_outputs_all (pairBytes x y))
    (RationalRouterProductJoin.signed_product_outputs x y)

theorem quotient_result_pair (x y : RawRat) :
    quotientResult (pairBytes x y) =
      encodeRawRat (RationalProductSignedPhysical.quotientRat x y) :=
  BitMachine.outputsWithin_unique _ (quotient_outputs_all (pairBytes x y))
    (RationalRouterQuotientJoin.signed_quotient_outputs x y)

#print axioms product_outputs_all
#print axioms quotient_outputs_all
#print axioms product_result_pair
#print axioms quotient_result_pair
#print axioms product_polytime
#print axioms quotient_polytime

end CurrentAdditive.RationalRouterAllInputJoin
