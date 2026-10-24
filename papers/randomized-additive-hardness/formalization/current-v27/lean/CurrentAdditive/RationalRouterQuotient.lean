import CurrentAdditive.RationalProductNestedFlat
import CurrentAdditive.CodeDQuotientRouteFixed

set_option maxHeartbeats 1000000

namespace CurrentAdditive.RationalRouterQuotient

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineBankCodec
open EthInapproximability.CurrentPaper.RationalProductNestedFlat
open CodeDQuotientRouteFixed
open CodeDCodec
open Turing TM2.Stmt
open BitMachineEncoding

theorem route_flatBank (x y : RawRat) :
    CodeDQuotientRouteFixed.outputBank (flatBank x y) =
      RationalProductCore.inputBank
        (RationalProductSignedPhysical.parityPad x.numerator
          (x.negative != y.negative))
        x.denominator.reverse y.denominator y.numerator.reverse := by
  funext i
  cases hp : RationalProductSignedRepack.signParity x.numerator <;>
    cases hx : x.negative <;> cases hy : y.negative <;>
  fin_cases i <;>
    simp [CodeDQuotientRouteFixed.outputBank, CodeDQuotientRouteFixed.paddedNum,
      CodeDQuotientRouteFixed.scannedNum,
      CodeDQuotientRouteFixed.transferredOperands,
      CodeDQuotientRouteFixed.dropSigns, CodeDBankTransferV2.transferred,
      flatBank, RationalProductCore.inputBank,
      RationalProductSignedPhysical.parityPad,
      RationalProductCore.firstBank, BitMachineBinaryMultiply.finBank,
      BitMachineBinaryMultiply.finStack,
      BitMachineBinaryMultiply.initialBank,
      BitMachineBinaryMultiply.cfg, BitMachineBinaryMultiply.rightBank,
      BitMachineBinaryAddAny.bank, BitMachineBinaryAdd.bank,
      RationalProductCore.firstStacks, finSumFinEquiv, Fin.addCases,
      hx, hy, hp, List.reverse_reverse]

theorem routeTime_flat_le (x y : RawRat) :
    CodeDQuotientRouteFixed.routeTime (flatBank x y) ≤
      30*((flatBytes x y).length+1) := by
  cases hp : RationalProductSignedRepack.signParity x.numerator <;>
    cases hx : x.negative <;> cases hy : y.negative <;>
  simp [CodeDQuotientRouteFixed.routeTime,
    CodeDQuotientRouteFixed.preTime, CodeDQuotientRouteFixed.needsPad,
    CodeDQuotientRouteFixed.paddedNum,
    CodeDQuotientRouteFixed.scannedNum,
    CodeDQuotientRouteFixed.transferredOperands,
    CodeDQuotientRouteFixed.dropSigns, CodeDBankTransferV2.transferred,
    flatBank, flatBytes, BitMachineBankCodec.encode_length,
    Fin.sum_univ_succ, hx, hy, hp, List.reverse_reverse]
  all_goals omega

theorem quotientInput_length_le (x y : RawRat) :
    (RationalProductSignedPhysical.quotientInput x y).length ≤
      (flatBytes x y).length + 2 := by
  cases hp : RationalProductSignedRepack.signParity x.numerator <;>
    cases hx : x.negative <;> cases hy : y.negative <;>
  simp [RationalProductSignedPhysical.quotientInput,
    RationalProductSignedPhysical.parityPad,
    RationalProductPacket.packedInput,
    RationalProductCore.inputBank,
    RationalProductCore.firstBank,
    BitMachineBinaryMultiply.initialBank, BitMachineBinaryMultiply.finBank,
    BitMachineBinaryMultiply.finStack, BitMachineBinaryMultiply.cfg,
    BitMachineBinaryMultiply.rightBank, BitMachineBinaryAddAny.bank,
    BitMachineBinaryAdd.bank, RationalProductCore.firstStacks,
    finSumFinEquiv, Fin.addCases,
    flatBytes, flatBank, BitMachineBankCodec.encode_length,
    Fin.sum_univ_succ, hx, hy, hp]
  all_goals omega

noncomputable def quotientRouteMachine : BitMachine.Machine :=
  BitMachineBankWrapper.machine CodeDQuotientRouteFixed.program
    CodeDQuotientRouteFixed.Label.signX CodeDQuotientRouteFixed.initial

def quotientRouteResult (input : List Bool) : List Bool :=
  BitMachineBankWrapper.result CodeDQuotientRouteFixed.outputBank input

theorem quotientRouteResult_flat (x y : RawRat) :
    quotientRouteResult (flatBytes x y) =
      RationalProductSignedPhysical.quotientInput x y := by
  simp only [quotientRouteResult, BitMachineBankWrapper.result,
    flatBytes, BitMachineBankCodec.decode_encode]
  rw [route_flatBank]
  rfl

theorem quotientRoute_outputs (x y : RawRat) :
    quotientRouteMachine.OutputsWithin (flatBytes x y)
      (RationalProductSignedPhysical.quotientInput x y)
      (70*((flatBytes x y).length+1)) := by
  let input := flatBytes x y
  let F := CodeDQuotientRouteFixed.outputBank
  have hlocal : ∀ S, BitMachineBankCodec.decode 12 input = some S →
      ∃ (t : Nat) (c : TM2.Cfg (fun _ : Fin 12 => Bool)
        CodeDQuotientRouteFixed.Label CodeDQuotientRouteFixed.Control),
        t ≤ 30*(input.length+1) ∧
        ((advance CodeDQuotientRouteFixed.program)^[t])
          ⟨some CodeDQuotientRouteFixed.Label.signX,
            CodeDQuotientRouteFixed.initial,S⟩ = c ∧
        c.l = none ∧ c.stk = F S := by
    intro S hd
    have he : S = flatBank x y := by
      have := hd
      simp [input, flatBytes] at this
      exact this.symm
    subst S
    refine ⟨CodeDQuotientRouteFixed.routeTime (flatBank x y),
      CodeDQuotientRouteFixed.cfg none
        (⟨(flatBank x y 0).headD false,
          (flatBank x y 6).headD false,
          RationalProductSignedRepack.signParity (flatBank x y 1)⟩,none)
        (F (flatBank x y)), routeTime_flat_le x y, ?_, rfl, rfl⟩
    exact CodeDQuotientRouteFixed.local_run (flatBank x y)
  have hsize : ∀ S, BitMachineBankCodec.decode 12 input = some S →
      (BitMachineBankCodec.encode (F S)).length ≤ input.length+2 := by
    intro S hd
    have he : S = flatBank x y := by
      have := hd
      simp [input, flatBytes] at this
      exact this.symm
    subst S
    dsimp [F]
    rw [route_flatBank]
    exact quotientInput_length_le x y
  have h := BitMachineBankWrapper.outputs CodeDQuotientRouteFixed.program
    CodeDQuotientRouteFixed.Label.signX CodeDQuotientRouteFixed.initial
    F input (30*(input.length+1)) (input.length+2) hlocal hsize
  change quotientRouteMachine.OutputsWithin input (quotientRouteResult input)
    (25*(input.length+1)+30*(input.length+1)+2*(input.length+2)+4) at h
  rw [quotientRouteResult_flat] at h
  apply BitMachine.outputsWithin_mono quotientRouteMachine h
  dsimp [input]
  omega

#print axioms quotientRoute_outputs

end CurrentAdditive.RationalRouterQuotient
