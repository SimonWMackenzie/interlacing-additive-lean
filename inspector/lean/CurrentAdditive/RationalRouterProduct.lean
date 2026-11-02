import CurrentAdditive.RationalProductNestedFlat
import CurrentAdditive.CodeDProductRouteFixed

set_option maxHeartbeats 1000000

namespace CurrentAdditive.RationalRouterProduct

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineBankCodec
open EthInapproximability.CurrentPaper.RationalProductNestedFlat
open CodeDProductRouteFixed
open CodeDCodec
open Turing TM2.Stmt
open BitMachineEncoding

theorem route_flatBank (x y : RawRat) :
    CodeDProductRouteFixed.outputBank (flatBank x y) =
      RationalProductCore.inputBank
        (RationalProductSignedPhysical.parityPad x.numerator
          (x.negative != y.negative))
        x.denominator.reverse y.numerator.reverse y.denominator := by
  funext i
  cases hp : RationalProductSignedRepack.signParity x.numerator <;>
    cases hx : x.negative <;> cases hy : y.negative <;>
  fin_cases i <;>
    simp [CodeDProductRouteFixed.outputBank, CodeDProductRouteFixed.paddedNum,
      CodeDProductRouteFixed.scannedNum,
      CodeDProductRouteFixed.transferredOperands,
      CodeDProductRouteFixed.dropSigns, CodeDBankTransferV2.transferred,
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
    CodeDProductRouteFixed.routeTime (flatBank x y) ≤
      30*((flatBytes x y).length+1) := by
  cases hp : RationalProductSignedRepack.signParity x.numerator <;>
    cases hx : x.negative <;> cases hy : y.negative <;>
  simp [CodeDProductRouteFixed.routeTime,
    CodeDProductRouteFixed.preTime, CodeDProductRouteFixed.needsPad,
    CodeDProductRouteFixed.paddedNum,
    CodeDProductRouteFixed.scannedNum,
    CodeDProductRouteFixed.transferredOperands,
    CodeDProductRouteFixed.dropSigns, CodeDBankTransferV2.transferred,
    flatBank, flatBytes, BitMachineBankCodec.encode_length,
    Fin.sum_univ_succ, hx, hy, hp, List.reverse_reverse]
  all_goals omega

theorem productInput_length_le (x y : RawRat) :
    (RationalProductSignedPhysical.productInput x y).length ≤
      (flatBytes x y).length + 2 := by
  cases hp : RationalProductSignedRepack.signParity x.numerator <;>
    cases hx : x.negative <;> cases hy : y.negative <;>
  simp [RationalProductSignedPhysical.productInput,
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

noncomputable def productRouteMachine : BitMachine.Machine :=
  BitMachineBankWrapper.machine CodeDProductRouteFixed.program
    CodeDProductRouteFixed.Label.signX CodeDProductRouteFixed.initial

def productRouteResult (input : List Bool) : List Bool :=
  BitMachineBankWrapper.result CodeDProductRouteFixed.outputBank input

theorem productRouteResult_flat (x y : RawRat) :
    productRouteResult (flatBytes x y) =
      RationalProductSignedPhysical.productInput x y := by
  simp only [productRouteResult, BitMachineBankWrapper.result,
    flatBytes, BitMachineBankCodec.decode_encode]
  rw [route_flatBank]
  rfl

theorem productRoute_outputs (x y : RawRat) :
    productRouteMachine.OutputsWithin (flatBytes x y)
      (RationalProductSignedPhysical.productInput x y)
      (70*((flatBytes x y).length+1)) := by
  let input := flatBytes x y
  let F := CodeDProductRouteFixed.outputBank
  have hlocal : ∀ S, BitMachineBankCodec.decode 12 input = some S →
      ∃ (t : Nat) (c : TM2.Cfg (fun _ : Fin 12 => Bool)
        CodeDProductRouteFixed.Label CodeDProductRouteFixed.Control),
        t ≤ 30*(input.length+1) ∧
        ((advance CodeDProductRouteFixed.program)^[t])
          ⟨some CodeDProductRouteFixed.Label.signX,
            CodeDProductRouteFixed.initial,S⟩ = c ∧
        c.l = none ∧ c.stk = F S := by
    intro S hd
    have he : S = flatBank x y := by
      have := hd
      simp [input, flatBytes] at this
      exact this.symm
    subst S
    refine ⟨CodeDProductRouteFixed.routeTime (flatBank x y),
      CodeDProductRouteFixed.cfg none
        (⟨(flatBank x y 0).headD false,
          (flatBank x y 6).headD false,
          RationalProductSignedRepack.signParity (flatBank x y 1)⟩,none)
        (F (flatBank x y)), routeTime_flat_le x y, ?_, rfl, rfl⟩
    exact CodeDProductRouteFixed.local_run (flatBank x y)
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
    exact productInput_length_le x y
  have h := BitMachineBankWrapper.outputs CodeDProductRouteFixed.program
    CodeDProductRouteFixed.Label.signX CodeDProductRouteFixed.initial
    F input (30*(input.length+1)) (input.length+2) hlocal hsize
  change productRouteMachine.OutputsWithin input (productRouteResult input)
    (25*(input.length+1)+30*(input.length+1)+2*(input.length+2)+4) at h
  rw [productRouteResult_flat] at h
  apply BitMachine.outputsWithin_mono productRouteMachine h
  dsimp [input]
  omega

#print axioms productRoute_outputs

end CurrentAdditive.RationalRouterProduct
