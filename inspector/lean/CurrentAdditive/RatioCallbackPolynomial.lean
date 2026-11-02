import CurrentAdditive.RatioPhysicalFold
import EthInapproximability.CurrentPaper.EntryClockPolyFrame

set_option maxHeartbeats 800000
set_option maxSynthPendingDepth 100
set_option maxRecDepth 10000

/-! Uniform input-only polynomial time for the concrete arithmetic callback,
including every scratch cell physically cleared after one comparison. -/

namespace CurrentAdditive.RatioCallbackPolynomial

open Turing EthInapproximability.CurrentPaper BitMachineEncoding
open MinimumRatioCallbackLayout MinimumRatioContext
open EntryClockPoly

noncomputable def quotientCap (W : Nat) : Nat :=
  W + MinimumRatioCallbackCalls.quotientCoefficient*(W+1)^96 *
    RationalCanonicalCallback.quotientMachine.pushBound

noncomputable def pairCap (W B : Nat) : Nat := 2*quotientCap W+2*B+2

noncomputable def invokeLength (M : BitMachine.Machine) (L T : Nat) : Nat :=
  MachineInvokeFull.uniformBound M (List.replicate L false) T

noncomputable def itemCap (W B : Nat) : Nat :=
  ((invokeLength MinimumRatioPositiveMachine.machine W (50*(W+1)) +
    invokeLength RationalCanonicalCallback.quotientMachine W
      (MinimumRatioCallbackCalls.quotientCoefficient*(W+1)^96) + 1 +
    (2*B+4)+1) +
    ((1+4*BitMachineStackGrowth.perStep (RawRatPairLift.program extraCount))*
        (6*(quotientCap W+B+2))+7 +
      invokeLength RationalLess.machine (pairCap W B)
        (RationalLess.coefficient*(pairCap W B+1)^RationalLess.exponent)+1)+1) +
    (3+B+1+(2*quotientCap W+2)+1)+1

theorem quotient_length (word : List Bool) (W : Nat) (hW : word.length ≤ W) :
    (RationalCanonicalCallback.quotientResult word).length ≤ quotientCap W := by
  have h := BitMachine.output_length_bound _
    (MinimumRatioCallbackCalls.quotient_outputs word)
  apply h.trans
  unfold quotientCap
  gcongr

theorem pair_length (word best : List Bool) (W B : Nat)
    (hW : word.length ≤ W) (hB : best.length ≤ B) :
    (RawRatPairAssembler.pairWord
      (RationalCanonicalCallback.quotientResult word) best.tail).length ≤
        pairCap W B := by
  have hq := quotient_length word W hW
  have ht : best.tail.length ≤ B := (by simpa only [List.length_tail] using (Nat.sub_le best.length 1).trans hB)
  simp only [RawRatPairAssembler.pairWord,BitMachineBankSerialize.encode,
    List.flatMap_cons,List.flatMap_nil,List.append_nil,List.length_append,
    EncodedCommunication.field_length]
  unfold pairCap
  omega

theorem itemClock_le (S : Bank) (word best : List Bool) (W B : Nat)
    (h9 : S (low 9) = best) (hW : word.length ≤ W) (hB : best.length ≤ B) :
    MinimumRatioCallbackPhysical.itemClock S word best ≤ itemCap W B := by
  have hq := quotient_length word W hW
  have hp := pair_length word best W B hW hB
  have ht : best.tail.length ≤ B := (by simpa only [List.length_tail] using (Nat.sub_le best.length 1).trans hB)
  have hpost9 : MinimumRatioCallbackPhysical.postCompareBank S word best (low 9) = best := by
    simp [MinimumRatioCallbackPhysical.postCompareBank,
      Function.update_apply,Fin.ext_iff,low,Fin.ofNat]
    exact h9
  have hpost16 : MinimumRatioCallbackPhysical.postCompareBank S word best (low 16) =
      RationalCanonicalCallback.quotientResult word := by
    simp [MinimumRatioCallbackPhysical.postCompareBank,
      Function.update_apply,Fin.ext_iff,low,Fin.ofNat]
  dsimp only [MinimumRatioCallbackPhysical.itemClock]
  rw [hpost9,hpost16]
  unfold itemCap invokeLength MachineInvokeFull.uniformBound RawRatPairFull.linearBound
  simp only [List.length_replicate]
  gcongr

noncomputable def growth : Nat :=
  BitMachineStackGrowth.perStep MinimumRatioCallbackFull.itemProgram

theorem callbackBound_le (S : Bank) (word best : List Bool) (W B : Nat)
    (h6 : S (low 6) = word) (h9 : S (low 9) = best)
    (hscratch : MinimumRatioCallbackFull.ScratchEmpty S)
    (hW : word.length ≤ W) (hB : best.length ≤ B) :
    RatioPhysicalFold.callbackBound S word best ≤
      (1+17*growth)*itemCap W B+20 := by
  classical
  obtain ⟨t,ht,hr⟩ := MinimumRatioCallbackPhysical.item_run_api S word best
    h6 h9 hscratch
  have hg (j : Fin 17) :
      ((MinimumRatioCallbackPhysical.postItemBank S word best)
        (MinimumRatioExtraClear.extraBank j)).length ≤
      growth*MinimumRatioCallbackPhysical.itemClock S word best := by
    have h := BitMachineStackGrowth.run_growth MinimumRatioCallbackFull.itemProgram
      (⟨some MinimumRatioCallbackPhysical.itemStart,
        MinimumRatioCallbackPhysical.itemControl,S⟩ :
        TM2.Cfg (fun _ : Stack => Bool) _ _) t
      (MinimumRatioExtraClear.extraBank j)
    rw [hr] at h
    have hzero : S (MinimumRatioExtraClear.extraBank j) = [] := by
      exact hscratch.1 ⟨15+j.val, by have := j.isLt; omega⟩
        (by change 15 ≤ 15+j.val; omega)
    simp only [hzero,List.length_nil,Nat.zero_add] at h
    exact h.trans (Nat.mul_le_mul_left _ ht)
  have hsum := Finset.sum_le_sum (s := Finset.univ)
    (fun j (_ : j ∈ Finset.univ) => hg j)
  simp only [Finset.sum_const,Finset.card_fin,nsmul_eq_mul] at hsum
  have hi := itemClock_le S word best W B h9 hW hB
  unfold RatioPhysicalFold.callbackBound
  calc
    _ ≤ (1+17*growth)*MinimumRatioCallbackPhysical.itemClock S word best+20 := by
      nlinarith
    _ ≤ (1+17*growth)*itemCap W B+20 := by gcongr

theorem quotientCap_poly {ι : Type*} {U f : ι → Nat}
    (hf : PolyIn U f) : PolyIn U (fun i => quotientCap (f i)) := by
  unfold quotientCap
  exact hf.add (((PolyIn.const _).mul ((hf.add (PolyIn.const 1)).pow 96)).mul
    (PolyIn.const _))

theorem pairCap_poly {ι : Type*} {U f g : ι → Nat}
    (hf : PolyIn U f) (hg : PolyIn U g) :
    PolyIn U (fun i => pairCap (f i) (g i)) := by
  unfold pairCap
  exact (((PolyIn.const 2).mul (quotientCap_poly hf)).add
    ((PolyIn.const 2).mul hg)).add (PolyIn.const 2)

theorem invokeLength_poly {ι : Type*} {U L T : ι → Nat}
    (M : BitMachine.Machine) (hL : PolyIn U L) (hT : PolyIn U T) :
    PolyIn U (fun i => invokeLength M (L i) (T i)) := by
  unfold invokeLength MachineInvokeFull.uniformBound
  simp only [List.length_replicate]
  have hB := hL.add (hT.mul (PolyIn.const M.pushBound))
  exact ((((PolyIn.const 2).mul hL).add (PolyIn.const 2)).add hT).add
    (((PolyIn.const 2).mul hB).add (PolyIn.const 2)) |>.add
      ((((PolyIn.const M.stackCount).mul hB).add
        (PolyIn.const M.stackCount)).add (PolyIn.const 2)) |>.add (PolyIn.const 3)

theorem itemCap_poly {ι : Type*} {U f g : ι → Nat}
    (hf : PolyIn U f) (hg : PolyIn U g) :
    PolyIn U (fun i => itemCap (f i) (g i)) := by
  have hq := quotientCap_poly hf
  have hp := pairCap_poly hf hg
  have hpos := invokeLength_poly MinimumRatioPositiveMachine.machine hf
    ((PolyIn.const 50).mul (hf.add (PolyIn.const 1)))
  have hquot := invokeLength_poly RationalCanonicalCallback.quotientMachine hf
    ((PolyIn.const MinimumRatioCallbackCalls.quotientCoefficient).mul
      ((hf.add (PolyIn.const 1)).pow 96))
  have hpair := ((PolyIn.const
    (1+4*BitMachineStackGrowth.perStep (RawRatPairLift.program extraCount))).mul
      ((PolyIn.const 6).mul ((hq.add hg).add (PolyIn.const 2)))).add
        (PolyIn.const 7)
  have hless := invokeLength_poly RationalLess.machine hp
    ((PolyIn.const RationalLess.coefficient).mul
      ((hp.add (PolyIn.const 1)).pow RationalLess.exponent))
  unfold itemCap
  exact (((((hpos.add hquot).add (PolyIn.const 1)).add
      (((PolyIn.const 2).mul hg).add (PolyIn.const 4))).add
        (PolyIn.const 1)).add
      (((hpair.add hless).add (PolyIn.const 1)))).add (PolyIn.const 1) |>.add
      (((((PolyIn.const 3).add hg).add (PolyIn.const 1)).add
        (((PolyIn.const 2).mul hq).add (PolyIn.const 2))).add
          (PolyIn.const 1)) |>.add (PolyIn.const 1)

theorem cap_polynomial : PolyIn (fun n : Nat => n)
    (fun n => (1+17*growth)*itemCap n n+20) := by
  exact ((PolyIn.const (1+17*growth)).mul
    (itemCap_poly PolyIn.self PolyIn.self)).add (PolyIn.const 20)

/-- One pair of constants bounds every actual callback frame, independent of
all words, banks and rational values. Both scratch use and scratch clearing
are included. -/
theorem callback_polynomial : ∃ C e : Nat, ∀ (S : Bank) (word best : List Bool),
    S (low 6) = word → S (low 9) = best →
    MinimumRatioCallbackFull.ScratchEmpty S →
    RatioPhysicalFold.callbackBound S word best ≤
      C*(word.length+best.length+1)^e := by
  obtain ⟨C,e,h⟩ := cap_polynomial
  refine ⟨C,e,?_⟩
  intro S word best h6 h9 hscratch
  exact (callbackBound_le S word best _ _ h6 h9 hscratch
    (Nat.le_add_right _ _) (Nat.le_add_left _ _)).trans
    (h (word.length+best.length))

#print axioms callback_polynomial

end CurrentAdditive.RatioCallbackPolynomial
