import CurrentAdditive.RationalNestedFlatTotal
import CurrentAdditive.RationalRouterQuotient
import CurrentAdditive.RationalRouterQuotient
import EthInapproximability.CurrentPaper.BitMachineStackGrowth

namespace CurrentAdditive.RationalRouterTotal

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineBankCodec
open EthInapproximability.CurrentPaper.RationalProductNestedFlat
open EthInapproximability.CurrentPaper.RationalNestedFlatTotal
open BitMachineEncoding
open Turing TM2.Stmt

theorem quotient_routeTime_le (S : Bank 12) :
    CodeDQuotientRouteFixed.routeTime S ≤
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
  simp [CodeDQuotientRouteFixed.routeTime, CodeDQuotientRouteFixed.preTime,
    CodeDQuotientRouteFixed.paddedNum, CodeDQuotientRouteFixed.scannedNum,
    CodeDQuotientRouteFixed.transferredOperands,
    CodeDQuotientRouteFixed.dropSigns, CodeDBankTransferV2.transferred]
  all_goals split_ifs <;> simp_all <;> omega

def quotientSizeConstant : Nat :=
  1 + 2400 * BitMachineStackGrowth.perStep CodeDQuotientRouteFixed.program

theorem quotient_output_size (S : Bank 12) :
    (encode (CodeDQuotientRouteFixed.outputBank S)).length ≤
      quotientSizeConstant*((encode S).length+1) := by
  let t := CodeDQuotientRouteFixed.routeTime S
  let p := BitMachineStackGrowth.perStep CodeDQuotientRouteFixed.program
  have hlocal := CodeDQuotientRouteFixed.local_run S
  have hpoint (i : Fin 12) :
      (CodeDQuotientRouteFixed.outputBank S i).length ≤
        (S i).length + p*t := by
    have h := BitMachineStackGrowth.run_growth
      CodeDQuotientRouteFixed.program
      (CodeDQuotientRouteFixed.cfg (some .signX)
        CodeDQuotientRouteFixed.initial S) t i
    rw [← CodeDQuotientRouteFixed.run, hlocal] at h
    simpa [CodeDQuotientRouteFixed.cfg, t, p] using h
  have hsum : (∑ i : Fin 12,
      (CodeDQuotientRouteFixed.outputBank S i).length) ≤
      (∑ i : Fin 12, (S i).length) + 12*(p*t) := by
    calc
      _ ≤ ∑ i : Fin 12, ((S i).length + p*t) := by
        apply Finset.sum_le_sum
        intro i _
        exact hpoint i
      _ = (∑ i : Fin 12, (S i).length) + 12*(p*t) := by
        simp [Finset.sum_add_distrib]
  have ht := quotient_routeTime_le S
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
    (CodeDQuotientRouteFixed.outputBank S)
  dsimp [quotientSizeConstant]
  calc
    (encode (CodeDQuotientRouteFixed.outputBank S)).length =
        2*(∑ i : Fin 12,
          (CodeDQuotientRouteFixed.outputBank S i).length)+12 := hlenOut
    _ ≤ 2*((∑ i : Fin 12, (S i).length)+12*(p*t))+12 := by
      omega
    _ = (encode S).length + 24*(p*t) := by omega
    _ ≤ (encode S).length +
        2400*p*((encode S).length+1) := Nat.add_le_add_left hbound _
    _ ≤ (1+2400*p)*((encode S).length+1) := by
      simp only [Nat.add_mul, one_mul]
      omega

theorem quotient_route_outputs_all (input : List Bool) :
    RationalRouterQuotient.quotientRouteMachine.OutputsWithin input
      (RationalRouterQuotient.quotientRouteResult input)
      ((25 + 100 + 2*quotientSizeConstant + 4)*(input.length+1)) := by
  let F := CodeDQuotientRouteFixed.outputBank
  have hlocal : ∀ S, decode 12 input = some S →
      ∃ (t : Nat) (c : TM2.Cfg (fun _ : Fin 12 => Bool)
        CodeDQuotientRouteFixed.Label CodeDQuotientRouteFixed.Control),
        t ≤ 100*(input.length+1) ∧
        ((advance CodeDQuotientRouteFixed.program)^[t])
          ⟨some CodeDQuotientRouteFixed.Label.signX,
            CodeDQuotientRouteFixed.initial,S⟩ = c ∧
        c.l = none ∧ c.stk = F S := by
    intro S hd
    have he := BitMachineBankCodec.encode_decode hd
    refine ⟨CodeDQuotientRouteFixed.routeTime S,
      CodeDQuotientRouteFixed.cfg none
        (⟨(S 0).headD false,(S 6).headD false,
          RationalProductSignedRepack.signParity (S 1)⟩,none)
        (F S), ?_, CodeDQuotientRouteFixed.local_run S, rfl, rfl⟩
    simpa [← he] using quotient_routeTime_le S
  have hsize : ∀ S, decode 12 input = some S →
      (encode (F S)).length ≤ quotientSizeConstant*(input.length+1) := by
    intro S hd
    have he := BitMachineBankCodec.encode_decode hd
    simpa [F, ← he] using quotient_output_size S
  have h := BitMachineBankWrapper.outputs CodeDQuotientRouteFixed.program
    CodeDQuotientRouteFixed.Label.signX CodeDQuotientRouteFixed.initial
    F input (100*(input.length+1))
      (quotientSizeConstant*(input.length+1)) hlocal hsize
  change RationalRouterQuotient.quotientRouteMachine.OutputsWithin input
    (RationalRouterQuotient.quotientRouteResult input)
    (25*(input.length+1)+100*(input.length+1)+
      2*(quotientSizeConstant*(input.length+1))+4) at h
  apply BitMachine.outputsWithin_mono _ h
  have hbase : 1 ≤ input.length+1 := by omega
  nlinarith

theorem quotient_route_polytime :
    BitMachine.Polytime RationalRouterQuotient.quotientRouteResult := by
  refine ⟨RationalRouterQuotient.quotientRouteMachine,
    25 + 100 + 2*quotientSizeConstant + 4, 1, ?_⟩
  intro input
  simpa only [pow_one] using quotient_route_outputs_all input

#print axioms quotient_route_outputs_all
#print axioms quotient_route_polytime

end CurrentAdditive.RationalRouterTotal
