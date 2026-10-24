import CurrentAdditive.FeatureBankAdvance96

/-! Exact bank identification for reusing one coordinate stage. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxSize 65536
set_option maxRecDepth 2048
namespace CurrentAdditive.FeatureCoordinateBank96
open Turing EthInapproximability.CurrentPaper BitMachineEncoding
open CurrentAdditive.FeatureCoordinateStage96
open CurrentAdditive.FeatureOldDescriptorFrame96
open CurrentAdditive.FeatureOldDescriptorSemantics96
open CurrentAdditive.Wide96ContextListScheduler

def low (k : Fin 15) : Fin 96 := ⟨k.val,by omega⟩

theorem frame_low (source body count : List Bool) (index fuel : Nat)
    (extra : Fin 96 → List Bool) (k : Fin 15) :
    frame source body count index fuel extra (low k)=
      (![[],[],[],[],[],[],[],[],source,body,List.replicate index true,[],
        count,List.replicate fuel true,[]] : Fin 15 → List Bool) k := by
  let F := foreignBank body count fuel extra
  let C := CylinderContextScanStep.initial source index
  have hi (i : Fin 12) := Wide96ContextPreservingScan.frame_bank F C i
  have ho := Wide96ContextPreservingScan.output_preserved F C
  have hc := Wide96ContextPreservingScan.context_preserved F C
  fin_cases k
  · exact hi 0
  · exact hi 1
  · exact hi 2
  · exact hi 3
  · exact hi 4
  · exact hi 5
  · exact hi 6
  · exact hi 7
  · exact hi 8
  · simpa [frame,F,foreignBank] using ho
  · exact hi 10
  · exact hi 11
  · simpa [frame,F,foreignBank] using hc.1
  · simpa [frame,F,foreignBank] using hc.2
  · exact hi 9

theorem frame_high (source body count : List Bool) (index fuel : Nat)
    (extra : Fin 96 → List Bool) (k : Fin 96) (hk : 15 ≤ k.val) :
    frame source body count index fuel extra k=extra k :=
  frame_extra source body count index fuel extra k hk

theorem final_banks (j : Nat) (ys : List Nat) (cs : List (List (Nat × Nat)))
    (qfuel jUnary carry : List Bool) :
    let S := finalBank j ys cs qfuel jUnary carry
    S 12=List.replicate (next j ys cs).length true ∧ S 13=[] ∧
      S 15=j.bits ∧ S 19=[] := by
  dsimp only
  have h12 := frame_low (SourceListEncoding.encode (words cs))
    (SourceListEncoding.fields (words (next j ys cs)))
    (List.replicate (next j ys cs).length true) cs.length 0
    (extra j ys qfuel jUnary carry) 12
  have h13 := frame_low (SourceListEncoding.encode (words cs))
    (SourceListEncoding.fields (words (next j ys cs)))
    (List.replicate (next j ys cs).length true) cs.length 0
    (extra j ys qfuel jUnary carry) 13
  have hh (k : Fin 96) (hk : 15 ≤ k.val) := frame_high
    (SourceListEncoding.encode (words cs))
    (SourceListEncoding.fields (words (next j ys cs)))
    (List.replicate (next j ys cs).length true) cs.length 0
    (extra j ys qfuel jUnary carry) k hk
  refine ⟨?_,?_,?_,?_⟩
  · simpa [finalBank,beforeHeader,low] using h12
  · simpa [finalBank,beforeHeader,low] using h13
  · simpa [finalBank,beforeHeader,extra] using hh 15 (by decide)
  · simpa [finalBank,beforeHeader,extra] using hh 19 (by decide)

theorem advance_exact (j : Nat) (ys : List Nat) (cs : List (List (Nat × Nat)))
    (qfuel jUnary carry : List Bool) :
    FeatureBankAdvance96.result (finalBank j ys cs qfuel jUnary carry)
      (List.replicate (next j ys cs).length true) j=
    initialBank (j+1) ys (next j ys cs) qfuel jUnary carry := by
  classical
  have hlow (i : Fin 15) :
      FeatureBankAdvance96.result (finalBank j ys cs qfuel jUnary carry)
        (List.replicate (next j ys cs).length true) j (low i)=
      FeatureCoordinateStage96.initialBank (j+1) ys (next j ys cs)
        qfuel jUnary carry (low i) := by
    simp only [FeatureBankAdvance96.result,finalBank,beforeHeader,
      FeatureCoordinateStage96.initialBank,Function.update_apply,frame_low]
    fin_cases i <;> rfl
  funext k
  by_cases hk : k.val<15
  · exact hlow ⟨k.val,hk⟩
  · have hk' : 15 ≤ k.val := by omega
    have h8 : k≠8 := by intro h; subst k; omega
    have h10 : k≠10 := by intro h; subst k; omega
    have h13 : k≠13 := by intro h; subst k; omega
    simp only [FeatureBankAdvance96.result,Function.update_apply,finalBank,
      beforeHeader,FeatureCoordinateStage96.initialBank]
    by_cases h15 : k=15
    · subst k
      simp [frame_high,extra]
    · simp [h8,h10,h13,h15,frame_high _ _ _ _ _ _ k hk',extra]

#print axioms frame_low
#print axioms advance_exact
end CurrentAdditive.FeatureCoordinateBank96
