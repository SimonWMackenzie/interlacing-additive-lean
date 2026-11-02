import CurrentAdditive.RationalNestedFlatClosure
import CurrentAdditive.RationalRouterQuotient
import EthInapproximability.CurrentPaper.BitMachineComposition

namespace CurrentAdditive.RationalRouterQuotientJoin

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.RationalProductNestedFlat
open EthInapproximability.CurrentPaper.RationalNestedFlatClosure
open RationalRouterQuotient
open CodeDCodec
open CodeDPairProductTargetV2

noncomputable def packetMachine : BitMachine.Machine :=
  BitMachineComposition.composition RationalProductNestedFlat.machine
    quotientRouteMachine

theorem packet_outputs (x y : RawRat) :
    packetMachine.OutputsWithin (pairBytes x y)
      (RationalProductSignedPhysical.quotientInput x y)
      (120*((pairBytes x y).length+1)) := by
  have h := BitMachineComposition.composition_outputsWithin
    RationalProductNestedFlat.machine quotientRouteMachine
    (pair_outputs x y) (quotientRoute_outputs x y)
  apply BitMachine.outputsWithin_mono packetMachine h
  have hf := flat_length_le_pair x y
  omega

noncomputable def signedQuotientMachine : BitMachine.Machine :=
  BitMachineComposition.composition packetMachine
    RationalProductSignedPhysical.machine

theorem signed_quotient_outputs (x y : RawRat) :
    signedQuotientMachine.OutputsWithin (pairBytes x y)
      (encodeRawRat (RationalProductSignedPhysical.quotientRat x y))
      (15000*((pairBytes x y).length+1)^2) := by
  have h := BitMachineComposition.composition_outputsWithin
    packetMachine RationalProductSignedPhysical.machine
    (packet_outputs x y) (RationalProductSignedPhysical.quotient_outputs x y)
  apply BitMachine.outputsWithin_mono signedQuotientMachine h
  have hf := flat_length_le_pair x y
  have hp := quotientInput_length_le x y
  have hbase : 1 ≤ (pairBytes x y).length+1 := by omega
  have hL : (RationalProductSignedPhysical.quotientInput x y).length+1 ≤
      3*((pairBytes x y).length+1) := by omega
  nlinarith

#print axioms packet_outputs
#print axioms signed_quotient_outputs

end CurrentAdditive.RationalRouterQuotientJoin
