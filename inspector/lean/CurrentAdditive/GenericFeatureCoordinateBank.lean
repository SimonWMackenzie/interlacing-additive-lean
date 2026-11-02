import CurrentAdditive.GenericFeatureCoordinateStage
import CurrentAdditive.FeatureCoordinateBank96

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option synthInstance.maxSize 65536
set_option maxRecDepth 2048
namespace CurrentAdditive.GenericFeatureCoordinateBank
open Turing EthInapproximability.CurrentPaper BitMachineEncoding
open GenericFeatureCoordinateStage GenericFeatureOldDescriptorFrame GenericFeatureOldDescriptorSemantics
open CurrentAdditive.Wide96ContextListScheduler
export FeatureCoordinateBank96 (low frame_low frame_high)

theorem final_banks (depth : Nat) (j : Nat) (ys : List Nat) (cs : List (List (Nat × Nat)))
    (qfuel jUnary carry : List Bool) :
    let S := finalBank depth j ys cs qfuel jUnary carry
    S 12=List.replicate (next depth j ys cs).length true ∧ S 13=[] ∧
      S 15=j.bits ∧ S 19=[] := by
  dsimp only
  have h12 := frame_low (SourceListEncoding.encode (words cs))
    (SourceListEncoding.fields (words (next depth j ys cs)))
    (List.replicate (next depth j ys cs).length true) cs.length 0
    (extra j ys qfuel jUnary carry) 12
  have h13 := frame_low (SourceListEncoding.encode (words cs))
    (SourceListEncoding.fields (words (next depth j ys cs)))
    (List.replicate (next depth j ys cs).length true) cs.length 0
    (extra j ys qfuel jUnary carry) 13
  have hh (k : Fin 96) (hk : 15 ≤ k.val) := frame_high
    (SourceListEncoding.encode (words cs))
    (SourceListEncoding.fields (words (next depth j ys cs)))
    (List.replicate (next depth j ys cs).length true) cs.length 0
    (extra j ys qfuel jUnary carry) k hk
  refine ⟨?_,?_,?_,?_⟩
  · simpa [finalBank,beforeHeader,low] using h12
  · simpa [finalBank,beforeHeader,low] using h13
  · simpa [finalBank,beforeHeader,extra] using hh 15 (by decide)
  · simpa [finalBank,beforeHeader,extra] using hh 19 (by decide)

theorem advance_exact (depth : Nat) (j : Nat) (ys : List Nat) (cs : List (List (Nat × Nat)))
    (qfuel jUnary carry : List Bool) :
    FeatureBankAdvance96.result (finalBank depth j ys cs qfuel jUnary carry)
      (List.replicate (next depth j ys cs).length true) j=
    initialBank (j+1) ys (next depth j ys cs) qfuel jUnary carry := by
  classical
  have hlow (i : Fin 15) :
      FeatureBankAdvance96.result (finalBank depth j ys cs qfuel jUnary carry)
        (List.replicate (next depth j ys cs).length true) j (low i)=
      GenericFeatureCoordinateStage.initialBank (j+1) ys (next depth j ys cs)
        qfuel jUnary carry (low i) := by
    simp only [FeatureBankAdvance96.result,finalBank,beforeHeader,
      GenericFeatureCoordinateStage.initialBank,FeatureCoordinateStage96.initialBank,
      Function.update_apply,frame_low]
    fin_cases i <;> rfl
  funext k
  by_cases hk : k.val<15
  · exact hlow ⟨k.val,hk⟩
  · have hk' : 15 ≤ k.val := by omega
    have h8 : k≠8 := by intro h; subst k; omega
    have h10 : k≠10 := by intro h; subst k; omega
    have h13 : k≠13 := by intro h; subst k; omega
    simp only [FeatureBankAdvance96.result,Function.update_apply,finalBank,
      beforeHeader,GenericFeatureCoordinateStage.initialBank,FeatureCoordinateStage96.initialBank]
    by_cases h15 : k=15
    · subst k
      simp [frame_high,extra]
    · simp [h8,h10,h13,h15,frame_high _ _ _ _ _ _ k hk',extra]

#print axioms advance_exact
end CurrentAdditive.GenericFeatureCoordinateBank
