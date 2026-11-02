import CurrentAdditive.RationalNestedFlatTotal
import CurrentAdditive.RationalRouterProduct
import CurrentAdditive.RationalRouterQuotient
import EthInapproximability.CurrentPaper.BitMachineStackGrowth

namespace CurrentAdditive.RationalRouterTotal

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineBankCodec
open EthInapproximability.CurrentPaper.RationalProductNestedFlat
open EthInapproximability.CurrentPaper.RationalNestedFlatTotal
open BitMachineEncoding
open Turing TM2.Stmt

theorem product_routeTime_le (S : Bank 12) :
    CodeDProductRouteFixed.routeTime S ≤
      100*((encode S).length+1) := by
  have hlen := BitMachineBankCodec.encode_length S
  have h0 := BitMachineBankCodec.word_length_le_encode S (0 : Fin 12)
  have h1 := BitMachineBankCodec.word_length_le_encode S (1 : Fin 12)
  have h2 := BitMachineBankCodec.word_length_le_encode S (2 : Fin 12)
  have h3 := BitMachineBankCodec.word_length_le_encode S (3 : Fin 12)
  have h4 := BitMachineBankCodec.word_length_le_encode S (4 : Fin 12)
  have h5 := BitMachineBankCodec.word_length_le_encode S (5 : Fin 12)
  have h6 := BitMachineBankCodec.word_length_le_encode S (6 : Fin 12)
  have h7 := BitMachineBankCodec.word_length_le_encode S (7 : Fin 12)
  have h8 := BitMachineBankCodec.word_length_le_encode S (8 : Fin 12)
  have h9 := BitMachineBankCodec.word_length_le_encode S (9 : Fin 12)
  have h10 := BitMachineBankCodec.word_length_le_encode S (10 : Fin 12)
  have h11 := BitMachineBankCodec.word_length_le_encode S (11 : Fin 12)
  simp [Fin.sum_univ_succ] at hlen
  simp [CodeDProductRouteFixed.routeTime, CodeDProductRouteFixed.preTime,
    CodeDProductRouteFixed.paddedNum, CodeDProductRouteFixed.scannedNum,
    CodeDProductRouteFixed.transferredOperands,
    CodeDProductRouteFixed.dropSigns, CodeDBankTransferV2.transferred]
  all_goals split_ifs <;> simp_all <;> omega

def productSizeConstant : Nat :=
  1 + 2400 * BitMachineStackGrowth.perStep CodeDProductRouteFixed.program

theorem product_output_size (S : Bank 12) :
    (encode (CodeDProductRouteFixed.outputBank S)).length ≤
      productSizeConstant*((encode S).length+1) := by
  let t := CodeDProductRouteFixed.routeTime S
  let p := BitMachineStackGrowth.perStep CodeDProductRouteFixed.program
  have hlocal := CodeDProductRouteFixed.local_run S
  have hpoint (i : Fin 12) :
      (CodeDProductRouteFixed.outputBank S i).length ≤
        (S i).length + p*t := by
    have h := BitMachineStackGrowth.run_growth
      CodeDProductRouteFixed.program
      (CodeDProductRouteFixed.cfg (some .signX)
        CodeDProductRouteFixed.initial S) t i
    rw [← CodeDProductRouteFixed.run, hlocal] at h
    simpa [CodeDProductRouteFixed.cfg, t, p] using h
  have hsum : (∑ i : Fin 12,
      (CodeDProductRouteFixed.outputBank S i).length) ≤
      (∑ i : Fin 12, (S i).length) + 12*(p*t) := by
    calc
      _ ≤ ∑ i : Fin 12, ((S i).length + p*t) := by
        apply Finset.sum_le_sum
        intro i _
        exact hpoint i
      _ = (∑ i : Fin 12, (S i).length) + 12*(p*t) := by
        simp [Finset.sum_add_distrib]
  have ht := product_routeTime_le S
  have hp : p*t ≤ p*(100*((encode S).length+1)) :=
    Nat.mul_le_mul_left p ht
  have hbound : 24*(p*t) ≤
      2400*p*((encode S).length+1) := by
    calc
      24*(p*t) ≤ 24*(p*(100*((encode S).length+1))) :=
        Nat.mul_le_mul_left 24 hp
      _ = 2400*p*((encode S).length+1) := by ring
  have hlen := BitMachineBankCodec.encode_length S
  have hlenOut := BitMachineBankCodec.encode_length
    (CodeDProductRouteFixed.outputBank S)
  dsimp [productSizeConstant]
  calc
    (encode (CodeDProductRouteFixed.outputBank S)).length =
        2*(∑ i : Fin 12,
          (CodeDProductRouteFixed.outputBank S i).length)+12 := hlenOut
    _ ≤ 2*((∑ i : Fin 12, (S i).length)+12*(p*t))+12 := by
      omega
    _ = (encode S).length + 24*(p*t) := by omega
    _ ≤ (encode S).length +
        2400*p*((encode S).length+1) := Nat.add_le_add_left hbound _
    _ ≤ (1+2400*p)*((encode S).length+1) := by
      simp only [Nat.add_mul, one_mul]
      omega

theorem product_route_outputs_all (input : List Bool) :
    RationalRouterProduct.productRouteMachine.OutputsWithin input
      (RationalRouterProduct.productRouteResult input)
      ((25 + 100 + 2*productSizeConstant + 4)*(input.length+1)) := by
  let F := CodeDProductRouteFixed.outputBank
  have hlocal : ∀ S, decode 12 input = some S →
      ∃ (t : Nat) (c : TM2.Cfg (fun _ : Fin 12 => Bool)
        CodeDProductRouteFixed.Label CodeDProductRouteFixed.Control),
        t ≤ 100*(input.length+1) ∧
        ((advance CodeDProductRouteFixed.program)^[t])
          ⟨some CodeDProductRouteFixed.Label.signX,
            CodeDProductRouteFixed.initial,S⟩ = c ∧
        c.l = none ∧ c.stk = F S := by
    intro S hd
    have he := BitMachineBankCodec.encode_decode hd
    refine ⟨CodeDProductRouteFixed.routeTime S,
      CodeDProductRouteFixed.cfg none
        (⟨(S 0).headD false,(S 6).headD false,
          RationalProductSignedRepack.signParity (S 1)⟩,none)
        (F S), ?_, CodeDProductRouteFixed.local_run S, rfl, rfl⟩
    simpa [← he] using product_routeTime_le S
  have hsize : ∀ S, decode 12 input = some S →
      (encode (F S)).length ≤ productSizeConstant*(input.length+1) := by
    intro S hd
    have he := BitMachineBankCodec.encode_decode hd
    simpa [F, ← he] using product_output_size S
  have h := BitMachineBankWrapper.outputs CodeDProductRouteFixed.program
    CodeDProductRouteFixed.Label.signX CodeDProductRouteFixed.initial
    F input (100*(input.length+1))
      (productSizeConstant*(input.length+1)) hlocal hsize
  change RationalRouterProduct.productRouteMachine.OutputsWithin input
    (RationalRouterProduct.productRouteResult input)
    (25*(input.length+1)+100*(input.length+1)+
      2*(productSizeConstant*(input.length+1))+4) at h
  apply BitMachine.outputsWithin_mono _ h
  have hbase : 1 ≤ input.length+1 := by omega
  nlinarith

theorem product_route_polytime :
    BitMachine.Polytime RationalRouterProduct.productRouteResult := by
  refine ⟨RationalRouterProduct.productRouteMachine,
    25 + 100 + 2*productSizeConstant + 4, 1, ?_⟩
  intro input
  simpa only [pow_one] using product_route_outputs_all input

#print axioms product_route_outputs_all
#print axioms product_route_polytime

end CurrentAdditive.RationalRouterTotal
