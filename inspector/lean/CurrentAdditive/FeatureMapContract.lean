import CurrentAdditive.FeatureMapAppend
import CurrentAdditive.FeatureMapLayout

namespace CurrentAdditive.FeatureMapContract

open Turing EthInapproximability.CurrentPaper BitMachineEncoding
open CurrentAdditive.GaussListContext
open CurrentAdditive.FeatureMapPairLoader CurrentAdditive.FeatureMapInvoke

noncomputable section
variable (M : BitMachine.Machine) (framed : Bool)

def piece (f : List Bool → List Bool) : List Bool → List Bool :=
 fun w => FeatureMapInvoke.piece framed (f w)

def selectedCut (context header : List Bool) (f : List Bool → List Bool)
 (pre : List (List Bool)) (word : List Bool) (suffix : List (List Bool)) :
 Bank M framed → List Bool :=
 FeatureMapLayout.selected (N := count M framed)
   (SourceListEncoding.encode (pre ++ word :: suffix))
   (SourceListEncoding.fields suffix) word
   (header ++ FeatureMapSourceScheduler.joined (piece framed f) pre)
   context pre.length suffix.length

theorem physical_cut (context header : List Bool) (f : List Bool → List Bool)
 (b : List Bool → Nat)
 (pre : List (List Bool)) (word : List Bool) (suffix : List (List Bool))
 (hM : M.OutputsWithin (packet context word) (f word) (b word)) :
 ∃ t ≤ FeatureMapAppend.callbackBudget M framed
   (selectedCut M framed context header f pre word suffix)
   context word (header ++ FeatureMapSourceScheduler.joined (piece framed f) pre)
   (f word) (b word),
 ((advance (FeatureMapAppend.program M framed))^[t])
   (⟨some .clear5,FeatureMapAppend.initial M framed,
     selectedCut M framed context header f pre word suffix⟩ :
     TM2.Cfg (fun _ : Bank M framed => Bool) _ _) =
   ⟨none,FeatureMapAppend.initial M framed,
     FeatureMapAppend.finalBank M framed
       (selectedCut M framed context header f pre word suffix)
       context word (header ++ FeatureMapSourceScheduler.joined (piece framed f) pre)
       (f word)⟩ := by
 apply FeatureMapAppend.callback_run M framed
   (selectedCut M framed context header f pre word suffix)
   context word _ _ _
 all_goals first
 | exact hM
 | (intro i
    apply FeatureMapLayout.selected_high
    change 15 ≤ 32+i.val
    omega)
 | simp [selectedCut,FeatureMapLayout.selected,FeatureMapLayout.boundary,
     StatefulListScheduler.initialBank,FeatureMapLayout.blank,Function.update_apply,
     low,Fin.ext_iff,Fin.ofNat]

def contract (context header : List Bool) (f : List Bool → List Bool)
 (b : List Bool → Nat) (original : List (List Bool))
 (hM : ∀ w∈original,M.OutputsWithin (packet context w) (f w) (b w)) :
 FeatureMapSourceScheduler.SourceCallbackContract
   (FeatureMapAppend.program M framed) .clear5 (FeatureMapAppend.initial M framed)
   (piece framed f) header context original where
 extra := FeatureMapLayout.blank
 time := fun pre w suf => if h : pre++w::suf=original then
   Classical.choose (physical_cut M framed context header f b pre w suf
     (hM w (by rw [←h];simp))) else 0
 control := fun _ _ _ => FeatureMapAppend.initial M framed
 state := fun pre w suf => FeatureMapAppend.finalBank M framed
   (selectedCut M framed context header f pre w suf)
   context w (header++FeatureMapSourceScheduler.joined (piece framed f) pre) (f w)
 callback_run := by
   intro pre w suf hs
   simp only [dif_pos hs]
   have hr := (Classical.choose_spec (physical_cut M framed context header f b pre w suf
     (hM w (by rw [←hs];simp)))).2
   simpa only [FeatureMapLayout.frame_selected,selectedCut,hs] using hr
 post := by
   intro pre w suf hs
   dsimp only
   unfold FeatureMapAppend.finalBank selectedCut
   rw [FeatureMapLayout.cleanup_mapped,FeatureMapLayout.increment_boundary]
   rw [FeatureMapLayout.frame_initial]
   congr 1 <;>
     simp [hs,FeatureMapSourceScheduler.joined_append_one,piece,List.append_assoc]

theorem contract_time_le (context header : List Bool) (f : List Bool → List Bool)
 (b : List Bool → Nat) (original : List (List Bool))
 (hM : ∀ w∈original,M.OutputsWithin (packet context w) (f w) (b w))
 (pre : List (List Bool)) (w : List Bool) (suf : List (List Bool))
 (hs : pre++w::suf=original) :
 (contract M framed context header f b original hM).time pre w suf ≤
 FeatureMapAppend.callbackBudget M framed
   (selectedCut M framed context header f pre w suf)
   context w (header++FeatureMapSourceScheduler.joined (piece framed f) pre)
   (f w) (b w) := by
 simp only [contract,dif_pos hs]
 exact (Classical.choose_spec (physical_cut M framed context header f b pre w suf
   (hM w (by rw [←hs];simp)))).1

#print axioms physical_cut
#print axioms contract

end
end CurrentAdditive.FeatureMapContract
