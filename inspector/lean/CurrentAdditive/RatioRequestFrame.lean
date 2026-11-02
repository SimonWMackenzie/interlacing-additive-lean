import CurrentAdditive.RatioPhysicalFold

set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

namespace CurrentAdditive.RatioRequestFrame
open Turing EthInapproximability.CurrentPaper BitMachineEncoding
open MinimumRatioCallbackLayout CurrentAdditive.GaussListContext

noncomputable def extra (lambda : List Bool) : Bank :=
  Function.update RatioPhysicalFold.blank (low 25) lambda
noncomputable def boundary (source output context lambda : List Bool)
    (index fuel : Nat) : Bank :=
  Function.update (RatioPhysicalFold.boundary source output context index fuel)
    (low 25) lambda
noncomputable def selected (source suffix word output context lambda : List Bool)
    (index fuel : Nat) : Bank :=
  Function.update (RatioPhysicalFold.selected source suffix word output context index fuel)
    (low 25) lambda

private theorem locate_ne25 (k : CylinderContextScanStep.Stack) :
    StatefulPreservingScan.locate (N := extraCount) k ≠ low 25 := by
  intro he
  have hv := congrArg Fin.val he
  fin_cases k <;> norm_num [StatefulPreservingScan.locate,
    LargeContextPreservingScan.locate,low] at hv

private theorem foreign_scalar (output context lambda : List Bool) (fuel : Nat) :
    StatefulListScheduler.foreignBank output context fuel (extra lambda) =
      Function.update
        (StatefulListScheduler.foreignBank output context fuel RatioPhysicalFold.blank)
        (low 25) lambda := by
  unfold StatefulListScheduler.foreignBank extra
  rw [Function.update_comm (show low 25 ≠ (9 : Stack) by
        simp [low,Fin.ext_iff,Fin.ofNat]),
      Function.update_comm (show low 25 ≠ (12 : Stack) by
        simp [low,Fin.ext_iff,Fin.ofNat]),
      Function.update_comm (show low 25 ≠ (13 : Stack) by
        simp [low,Fin.ext_iff,Fin.ofNat])]

private theorem frame_scalar (output context lambda : List Bool) (fuel : Nat)
    (c : CylinderContextScanStep.Config) :
    (StatefulPreservingScan.frame
      (StatefulListScheduler.foreignBank output context fuel (extra lambda)) c).stk =
      Function.update
        (StatefulPreservingScan.frame
          (StatefulListScheduler.foreignBank output context fuel RatioPhysicalFold.blank) c).stk
        (low 25) lambda := by
  funext j
  by_cases hj : ∃ k, StatefulPreservingScan.locate k=j
  · obtain ⟨k,rfl⟩ := hj
    rw [StatefulPreservingScan.frame_bank,
      Function.update_of_ne (locate_ne25 k),StatefulPreservingScan.frame_bank]
  · rw [StatefulPreservingScan.frame_foreign _ _ _ hj,foreign_scalar]
    by_cases he : j=low 25
    · subst j; simp
    · rw [Function.update_of_ne he,Function.update_of_ne he,
        StatefulPreservingScan.frame_foreign _ _ _ hj]

theorem frame_initial (source output context lambda : List Bool) (index fuel : Nat) :
    (StatefulPreservingScan.frame
      (StatefulListScheduler.foreignBank output context fuel (extra lambda))
      (CylinderContextScanStep.initial source index)).stk =
      boundary source output context lambda index fuel := by
  rw [frame_scalar,RatioPhysicalFold.frame_initial]
  rfl

theorem frame_selected (source suffix word output context lambda : List Bool)
    (index fuel : Nat) :
    (StatefulPreservingScan.frame
      (StatefulListScheduler.foreignBank output context fuel (extra lambda))
      (⟨none,
       CylinderContextScanStep.getterControl
         (PreservingV2Program.v2Control
           (IndexedV2Program.indexControl
             (SourceListMachineFields.coreControl (some true,false),none))),
       CylinderContextScanStep.selectedBank source suffix word index⟩ :
          CylinderContextScanStep.Config)).stk =
      selected source suffix word output context lambda index fuel := by
  rw [frame_scalar,RatioPhysicalFold.frame_selected]
  rfl

theorem selected_at (source suffix word output context lambda : List Bool)
    (index fuel : Nat) (j : Fin 32) (hj : j ≠ 25) :
    selected source suffix word output context lambda index fuel (low j) =
      RatioPhysicalFold.selected source suffix word output context index fuel (low j) := by
  apply Function.update_of_ne
  intro he
  apply hj
  apply Fin.ext
  exact congrArg (fun k : Stack => k.val) he

theorem selected_high (source suffix word output context lambda : List Bool)
    (index fuel : Nat) (j : Stack) (hj : 15 ≤ j.val) (hne : j ≠ low 25) :
    selected source suffix word output context lambda index fuel j = [] := by
  rw [selected,Function.update_of_ne hne]
  exact RatioPhysicalFold.selected_high _ _ _ _ _ _ _ j hj

private theorem cleared_inside {n : Nat} (b : Fin n → Stack) (S : Bank)
    (i : Fin n) (word : List Bool) :
    BitMachineClearBank.cleared b (Function.update S (b i) word) =
      BitMachineClearBank.cleared b S := by
  funext j
  by_cases hj : ∃ k,b k=j
  · simp [BitMachineClearBank.cleared,hj]
  · have hn : j ≠ b i := by intro he; exact hj ⟨i,he.symm⟩
    simp [BitMachineClearBank.cleared,hj,Function.update_of_ne hn]

private theorem cleared_outside {n : Nat} (b : Fin n → Stack) (S : Bank)
    (j : Stack) (word : List Bool) (hj : ∀ i,b i ≠ j) :
    BitMachineClearBank.cleared b (Function.update S j word) =
      Function.update (BitMachineClearBank.cleared b S) j word := by
  funext k
  by_cases hk : k=j
  · subst k; simp [BitMachineClearBank.cleared,hj]
  · simp only [Function.update_of_ne hk,BitMachineClearBank.cleared]

theorem cleanup (source suffix word output next context lambda : List Bool)
    (index fuel : Nat) :
    BitMachineClearBank.cleared StatefulListScheduler.cleanBank
      (Function.update
        (Function.update (selected source suffix word output context lambda index fuel)
          (low 6) []) (low 9) next) =
      boundary source next context lambda index fuel := by
  have h9 : ∀ i,StatefulListScheduler.cleanBank (N := extraCount) i ≠ low 9 := by
    intro i; fin_cases i <;>
      simp [StatefulListScheduler.cleanBank,LargeContextListScheduler.cleanBank,
        Fin.ext_iff,low,Fin.ofNat]
  have h25 : ∀ i,StatefulListScheduler.cleanBank (N := extraCount) i ≠ low 25 := by
    intro i; fin_cases i <;>
      simp [StatefulListScheduler.cleanBank,LargeContextListScheduler.cleanBank,
        Fin.ext_iff,low,Fin.ofNat]
  have h6 : StatefulListScheduler.cleanBank (N := extraCount) 6 = low 6 := by
    apply Fin.ext; simp [StatefulListScheduler.cleanBank,LargeContextListScheduler.cleanBank,low]
  rw [cleared_outside _ _ _ _ h9,← h6,cleared_inside]
  unfold selected
  rw [cleared_outside _ _ _ _ h25]
  have hh := RatioPhysicalFold.cleanup_selected source suffix word output next context index fuel
  rw [cleared_outside _ _ _ _ h9] at hh
  unfold boundary
  rw [← hh]
  exact Function.update_comm (β := fun _ : Stack => List Bool)
    (show low 25 ≠ low 9 by simp [low,Fin.ext_iff,Fin.ofNat]) lambda next _

theorem increment (source output context lambda : List Bool) (index fuel : Nat) :
    Function.update (boundary source output context lambda index fuel) 10
      (true :: boundary source output context lambda index fuel 10) =
      boundary source output context lambda (index+1) fuel := by
  unfold boundary
  have hne : (10 : Stack) ≠ low 25 := by simp [low,Fin.ext_iff,Fin.ofNat]
  rw [Function.update_of_ne hne,← RatioPhysicalFold.increment_boundary]
  exact Function.update_comm (β := fun _ : Stack => List Bool)
    (show low 25 ≠ (10 : Stack) by simp [low,Fin.ext_iff,Fin.ofNat]) lambda _ _

#print axioms cleanup
#print axioms frame_selected
end CurrentAdditive.RatioRequestFrame
