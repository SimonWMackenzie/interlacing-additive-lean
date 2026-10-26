import CurrentAdditive.FeatureMapContract
import CurrentAdditive.GaussSearchClock

set_option maxHeartbeats 3000000
set_option maxRecDepth 4096

namespace CurrentAdditive.FeatureMapClock

open Turing EthInapproximability.CurrentPaper BitMachineEncoding
open CurrentAdditive.GaussListContext
open CurrentAdditive.FeatureMapPairLoader CurrentAdditive.FeatureMapInvoke

noncomputable section
variable (M : BitMachine.Machine) (framed : Bool)

def callbackCap (context word output answer : List Bool) (T : Nat) : Nat :=
 word.length+1+FeatureMapAppend.coreBudget M framed context word output answer T

def cycleCap (context header : List Bool) (f : List Bool → List Bool)
 (b : List Bool → Nat) (pre : List (List Bool)) (w : List Bool)
 (suf : List (List Bool)) : Nat :=
 StatefulListScheduler.getterBudget pre w suf +
   (callbackCap M framed context w
     (header++FeatureMapSourceScheduler.joined (FeatureMapContract.piece framed f) pre)
     (f w) (b w)+1)+1+
   ((SourceListEncoding.fields suf).length+(packet context w).length+11)+1

def sumCap (context header : List Bool) (f : List Bool → List Bool)
 (b : List Bool → Nat) (pre : List (List Bool)) (suf : List (List Bool)) : Nat :=
 match suf with
 | [] => 1
 | w::tail => 1+cycleCap M framed context header f b pre w tail+
     sumCap context header f b (pre++[w]) tail

theorem cleanup_sum (context header : List Bool) (f : List Bool → List Bool)
 (pre : List (List Bool)) (w : List Bool) (suf : List (List Bool)) :
 (∑ i : Fin 10,
   ((FeatureMapAppend.finalBank M framed
     (FeatureMapContract.selectedCut M framed context header f pre w suf)
     context w (header++FeatureMapSourceScheduler.joined (FeatureMapContract.piece framed f) pre)
     (f w)) (StatefulListScheduler.cleanBank i)).length) =
   (SourceListEncoding.fields suf).length+(packet context w).length := by
 exact FeatureMapLayout.cleanup_sum_generic _ _ _ _ _ _ _ _ _

theorem cycle_le (context header : List Bool) (f : List Bool → List Bool)
 (b : List Bool → Nat) (original : List (List Bool))
 (hM : ∀ w∈original,M.OutputsWithin (packet context w) (f w) (b w))
 (pre : List (List Bool)) (w : List Bool) (suf : List (List Bool))
 (hs : pre++w::suf=original) :
 FeatureMapSourceScheduler.cycleBudget (FeatureMapAppend.program M framed)
   .clear5 (FeatureMapAppend.initial M framed) (FeatureMapContract.piece framed f)
   header context original (FeatureMapContract.contract M framed context header f b original hM)
   pre w suf ≤ cycleCap M framed context header f b pre w suf := by
 have ht := FeatureMapContract.contract_time_le M framed context header f b original hM pre w suf hs
 have h5 : (FeatureMapContract.selectedCut M framed context header f pre w suf) (low 5) =
     List.replicate w.length true := by
   exact FeatureMapLayout.selected_five _ _ _ _ _ _ _
 have hbudget : FeatureMapAppend.callbackBudget M framed
     (FeatureMapContract.selectedCut M framed context header f pre w suf)
     context w (header++FeatureMapSourceScheduler.joined (FeatureMapContract.piece framed f) pre)
     (f w) (b w) = callbackCap M framed context w
       (header++FeatureMapSourceScheduler.joined (FeatureMapContract.piece framed f) pre)
       (f w) (b w) := by
   unfold FeatureMapAppend.callbackBudget callbackCap
   rw [h5,List.length_replicate]
 have hcap := ht.trans_eq hbudget
 clear ht
 have hsum := cleanup_sum M framed context header f pre w suf

 unfold FeatureMapSourceScheduler.cycleBudget
 dsimp only [FeatureMapContract.contract]
 simp only [FeatureMapContract.contract,dif_pos hs] at hcap
 simp only [dif_pos hs]
 rw [hsum]
 unfold cycleCap callbackCap
 unfold callbackCap at hcap

 omega

theorem remaining_le (context header : List Bool) (f : List Bool → List Bool)
 (b : List Bool → Nat) (original : List (List Bool))
 (hM : ∀ w∈original,M.OutputsWithin (packet context w) (f w) (b w))
 (pre suf : List (List Bool)) (hs : pre++suf=original) :
 FeatureMapSourceScheduler.remainingBudget (FeatureMapAppend.program M framed)
   .clear5 (FeatureMapAppend.initial M framed) (FeatureMapContract.piece framed f)
   header context original (FeatureMapContract.contract M framed context header f b original hM)
   pre suf ≤ sumCap M framed context header f b pre suf := by
 induction suf generalizing pre with
 | nil => rfl
 | cons w tail ih =>
   have hc := cycle_le M framed context header f b original hM pre w tail hs
   have hn : (pre++[w])++tail=original := by simpa [List.append_assoc] using hs
   have ht := ih (pre++[w]) hn
   simp only [FeatureMapSourceScheduler.remainingBudget,sumCap]
   omega

#print axioms remaining_le

end
end CurrentAdditive.FeatureMapClock
