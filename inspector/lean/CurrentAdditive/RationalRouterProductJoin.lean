import CurrentAdditive.RationalNestedFlatClosure
import CurrentAdditive.RationalRouterProduct
import EthInapproximability.CurrentPaper.BitMachineComposition

namespace CurrentAdditive.RationalRouterProductJoin

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.RationalProductNestedFlat
open EthInapproximability.CurrentPaper.RationalNestedFlatClosure
open RationalRouterProduct
open CodeDCodec
open CodeDPairProductTargetV2

noncomputable def packetMachine : BitMachine.Machine :=
  BitMachineComposition.composition RationalProductNestedFlat.machine
    productRouteMachine

theorem packet_outputs (x y : RawRat) :
    packetMachine.OutputsWithin (pairBytes x y)
      (RationalProductSignedPhysical.productInput x y)
      (120*((pairBytes x y).length+1)) := by
  have h := BitMachineComposition.composition_outputsWithin
    RationalProductNestedFlat.machine productRouteMachine
    (pair_outputs x y) (productRoute_outputs x y)
  apply BitMachine.outputsWithin_mono packetMachine h
  have hf := flat_length_le_pair x y
  omega

noncomputable def signedProductMachine : BitMachine.Machine :=
  BitMachineComposition.composition packetMachine
    RationalProductSignedPhysical.machine

theorem signed_product_outputs (x y : RawRat) :
    signedProductMachine.OutputsWithin (pairBytes x y)
      (encodeRawRat (RationalProductSignedPhysical.productRat x y))
      (15000*((pairBytes x y).length+1)^2) := by
  have h := BitMachineComposition.composition_outputsWithin
    packetMachine RationalProductSignedPhysical.machine
    (packet_outputs x y) (RationalProductSignedPhysical.product_outputs x y)
  apply BitMachine.outputsWithin_mono signedProductMachine h
  have hf := flat_length_le_pair x y
  have hp := productInput_length_le x y
  have hbase : 1 ≤ (pairBytes x y).length+1 := by omega
  have hL : (RationalProductSignedPhysical.productInput x y).length+1 ≤
      3*((pairBytes x y).length+1) := by omega
  nlinarith

#print axioms packet_outputs
#print axioms signed_product_outputs

end CurrentAdditive.RationalRouterProductJoin
