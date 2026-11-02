import CurrentAdditive.RationalSubtractRouteClock
import CurrentAdditive.RationalNestedFlatTotal
import EthInapproximability.CurrentPaper.BitMachineBankWrapper

namespace EthInapproximability.CurrentPaper.RationalSubtractPairMachine

set_option maxRecDepth 4096

open RationalSubtractRoute RationalSubtractRouteRun
open CurrentAdditive.CodeDCodec

abbrev Bank := RationalSubtractCore.Bank

noncomputable def routedBank (S : Bank) : Bank := routed (precleared S)

noncomputable def machine : BitMachine.Machine :=
  BitMachineBankWrapper.machine program start initial

noncomputable def result (input : List Bool) : List Bool :=
  BitMachineBankWrapper.result routedBank input

theorem extended_result (a b : RawRat) :
    result (BitMachineBankCodec.encode
      (RationalFlatPad32.extendedFlatBank a b)) =
      RationalSubtractSpec.canonicalPacket a b := by
  simp [result, BitMachineBankWrapper.result, routedBank,
    BitMachineBankCodec.decode_encode,
    RationalSubtractRouteSpec.full_routed_flat_eq_canonical,
    RationalSubtractSpec.canonicalPacket]

theorem extended_outputs (a b : RawRat) :
    machine.OutputsWithin
      (BitMachineBankCodec.encode (RationalFlatPad32.extendedFlatBank a b))
      (RationalSubtractSpec.canonicalPacket a b)
      (65*((BitMachineBankCodec.encode
        (RationalFlatPad32.extendedFlatBank a b)).length+1) +
       (23*(BitMachineBankCodec.encode
        (RationalFlatPad32.extendedFlatBank a b)).length+45) +
       2*(RationalSubtractSpec.canonicalPacket a b).length+4) := by
  have h := BitMachineBankWrapper.outputs program start initial routedBank
    (BitMachineBankCodec.encode (RationalFlatPad32.extendedFlatBank a b))
    (23*(BitMachineBankCodec.encode
      (RationalFlatPad32.extendedFlatBank a b)).length+45)
    (RationalSubtractSpec.canonicalPacket a b).length
    (by
      intro S hd
      obtain ⟨t,ht,hr⟩ := full_run S
      refine ⟨t, ⟨none, initial, routedBank S⟩, ?_, hr, rfl, rfl⟩
      have he := BitMachineBankCodec.encode_decode hd
      rw [← he]
      exact ht.trans (by omega))
    (by
      intro S hd
      have hs : S = RationalFlatPad32.extendedFlatBank a b := by
        have he := BitMachineBankCodec.decode_encode
          (RationalFlatPad32.extendedFlatBank a b)
        exact Option.some.inj (hd.symm.trans he)
      subst S
      simp [routedBank, RationalSubtractRouteSpec.full_routed_flat_eq_canonical,
        RationalSubtractSpec.canonicalPacket])
  change (BitMachineBankWrapper.machine program start initial).OutputsWithin
    (BitMachineBankCodec.encode (RationalFlatPad32.extendedFlatBank a b))
    (result (BitMachineBankCodec.encode
      (RationalFlatPad32.extendedFlatBank a b))) _ at h
  rw [extended_result] at h
  simpa only [machine, show 2*32+1=65 from by norm_num] using h

noncomputable def pairRouteMachine : BitMachine.Machine :=
  BitMachineComposition.composition
    (BitMachineComposition.composition
      RationalProductNestedFlat.machine RationalFlatPad32.machine)
    machine

noncomputable def pairSubtractMachine : BitMachine.Machine :=
  BitMachineComposition.composition pairRouteMachine
    RationalSubtractClock.machine

def pairBytes (a b : RawRat) : List Bool :=
  CurrentAdditive.CodeDPairProductTargetV2.pairBytes a b

def flatBytes (a b : RawRat) : List Bool :=
  RationalProductNestedFlat.flatBytes a b

def extendedBytes (a b : RawRat) : List Bool :=
  BitMachineBankCodec.encode (RationalFlatPad32.extendedFlatBank a b)

def parserTime (a b : RawRat) : Nat :=
  40*((pairBytes a b).length+1) +
    2*(flatBytes a b).length+2 + (2*(flatBytes a b).length+24)

def routeTime (a b : RawRat) : Nat :=
  65*((extendedBytes a b).length+1) +
    (23*(extendedBytes a b).length+45) +
    2*(RationalSubtractSpec.canonicalPacket a b).length+4

def subtractionTime (a b : RawRat) : Nat :=
  65*((RationalSubtractSpec.canonicalPacket a b).length+1) +
    100000000000000*((RationalSubtractSpec.canonicalPacket a b).length+1)^2 +
    2*(150000000000000*((RationalSubtractSpec.canonicalPacket a b).length+1)) + 4

theorem pair_route_outputs (a b : RawRat) :
    pairRouteMachine.OutputsWithin (pairBytes a b)
      (RationalSubtractSpec.canonicalPacket a b)
      (parserTime a b + 2*(extendedBytes a b).length+2 + routeTime a b) := by
  simpa only [pairRouteMachine, pairBytes, parserTime, flatBytes,
    extendedBytes, routeTime] using BitMachineComposition.composition_outputsWithin
    (BitMachineComposition.composition
      RationalProductNestedFlat.machine RationalFlatPad32.machine)
    machine
    (by simpa only [pairBytes, parserTime, flatBytes, extendedBytes] using
      RationalFlatPad32.nested_pair_to_extended a b)
    (by simpa only [routeTime, extendedBytes] using extended_outputs a b)

theorem pair_subtract_outputs (a b : RawRat) :
    pairSubtractMachine.OutputsWithin (pairBytes a b)
      (RationalSubtractClock.result (RationalSubtractSpec.canonicalPacket a b))
      ((parserTime a b + 2*(extendedBytes a b).length+2 + routeTime a b) +
        2*(RationalSubtractSpec.canonicalPacket a b).length+2 +
        subtractionTime a b) := by
  simpa only [pairSubtractMachine] using BitMachineComposition.composition_outputsWithin
    pairRouteMachine RationalSubtractClock.machine
    (pair_route_outputs a b)
    (by simpa only [subtractionTime] using
      RationalSubtractSpec.canonical_machine_outputs a b)

theorem pair_exact_subtract (a b : RawRat) (ha : a.Valid) (hb : b.Valid) :
    ∃ r, RationalSubtractSpec.decodeResultRat
      (RationalSubtractClock.result (RationalSubtractSpec.canonicalPacket a b)) =
        some r ∧ r.Valid ∧ r.value = a.value - b.value :=
  RationalSubtractSpec.canonical_exact_subtract a b ha hb

noncomputable def totalResult : List Bool → List Bool :=
  RationalSubtractClock.result ∘
    RationalSubtractRouteClock.result ∘
    (fun input => input ++ List.replicate 20 false) ∘
    RationalNestedFlatTotal.result

theorem total_polytime : BitMachine.Polytime totalResult := by
  have hp := BitMachineComposition.polytime_comp
    RationalNestedFlatTotal.polytime RationalFlatPad32.polytime
  have hr := BitMachineComposition.polytime_comp hp
    RationalSubtractRouteClock.polytime
  have hs := BitMachineComposition.polytime_comp hr
    RationalSubtractClock.polytime
  simpa only [totalResult, Function.comp_assoc] using hs

theorem total_result_pair (a b : RawRat) :
    totalResult (pairBytes a b) =
      RationalSubtractClock.result (RationalSubtractSpec.canonicalPacket a b) := by
  have hflat : RationalNestedFlatTotal.result (pairBytes a b) =
      flatBytes a b := by
    exact BitMachine.outputsWithin_unique RationalProductNestedFlat.machine
      (RationalNestedFlatTotal.outputs (pairBytes a b))
      (by simpa only [pairBytes, flatBytes] using
        RationalNestedFlatClosure.pair_outputs a b)
  have hroute : RationalSubtractRouteClock.result (extendedBytes a b) =
      RationalSubtractSpec.canonicalPacket a b := by
    simpa only [RationalSubtractRouteClock.result, result, routedBank] using
      extended_result a b
  simp only [totalResult, Function.comp_apply, hflat]
  change RationalSubtractClock.result
    (RationalSubtractRouteClock.result
      (RationalProductNestedFlat.flatBytes a b ++ List.replicate 20 false)) = _
  rw [← RationalFlatPad32.extendedFlat_bytes]
  exact congrArg RationalSubtractClock.result hroute

theorem total_exact_subtract (a b : RawRat) (ha : a.Valid) (hb : b.Valid) :
    ∃ r, RationalSubtractSpec.decodeResultRat
      (totalResult (pairBytes a b)) = some r ∧
      r.Valid ∧ r.value = a.value - b.value := by
  rw [total_result_pair]
  exact pair_exact_subtract a b ha hb

end EthInapproximability.CurrentPaper.RationalSubtractPairMachine
