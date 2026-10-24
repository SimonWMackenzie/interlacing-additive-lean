import CurrentAdditive.RatioIndexedScheduler
import CurrentAdditive.RatioRequestFrame
import CurrentAdditive.RatioPairListSpec

set_option maxHeartbeats 1500000
set_option maxRecDepth 10000

/-! Literal indexed request-list producer from its explicit prepared header
and unary source count. Each item physically reads the same coefficient
position, serializes and V2-frames its request, and appends it. Equal source
records may use different coefficients. -/
noncomputable section
namespace CurrentAdditive.RatioPairList
open Turing EthInapproximability.CurrentPaper BitMachineEncoding
open MinimumRatioCallbackLayout CurrentAdditive.GaussListContext
open RatioPairListSpec

noncomputable def selectedCut (xs coeff : List (List Bool))
    (pre : List (List Bool)) (word : List Bool) (tail : List (List Bool)) : Bank :=
  RatioRequestFrame.selected (SourceListEncoding.encode (pre ++ word :: tail))
    (SourceListEncoding.fields tail) word (outputAt xs.length coeff pre)
    (SourceListEncoding.encode coeff) [] pre.length tail.length

noncomputable def postCut (xs coeff : List (List Bool))
    (pre : List (List Bool)) (word : List Bool) (tail : List (List Bool)) : Bank :=
  Function.update
    (selectedCut xs coeff pre word tail)
    (low 9) (outputAt xs.length coeff (pre ++ [word]))

theorem cut_run (xs coeff : List (List Bool))
    (hlen : coeff.length=xs.length) (pre : List (List Bool)) (word : List Bool)
    (tail : List (List Bool)) (hsplit : pre ++ word :: tail=xs) :
    ∃ t ≤ RatioPairItem.clock (coeff.take pre.length)
      (coefficient coeff pre.length) (coeff.drop (pre.length+1)) word
        (outputAt xs.length coeff pre),
      ((advance RatioPairItem.program)^[t])
        (⟨some RatioPairItem.start,RatioPairItem.control,
          selectedCut xs coeff pre word tail⟩ :
          TM2.Cfg (fun _ : Stack => Bool) _ _) =
        ⟨none,RatioPairItem.control,postCut xs coeff pre word tail⟩ := by
  have hn : pre.length < coeff.length := by
    rw [hlen,← hsplit,List.length_append,List.length_cons]
    omega
  have hp := coefficient_prefix_length coeff pre.length hn
  have hc := coefficient_split coeff pre.length hn
  have hsmall (j : Fin 32) (hj : 15 ≤ j.val) (h25 : j ≠ 25) :
      selectedCut xs coeff pre word tail (low j) = [] := by
    apply RatioRequestFrame.selected_high
    · simpa only [low,Fin.val_castAdd] using hj
    · intro he; apply h25; apply Fin.ext
      exact congrArg (fun k : Stack => k.val) he
  have hsource : selectedCut xs coeff pre word tail
      (RatioCoefficientLookup.locate 8) =
      SourceListEncoding.encode (coeff.take pre.length ++
        coefficient coeff pre.length :: coeff.drop (pre.length+1)) := by
    rw [hc]
    simp [selectedCut,RatioRequestFrame.selected,RatioPhysicalFold.selected,
      RatioPhysicalFold.boundary,StatefulListScheduler.initialBank,
      RatioCoefficientLookup.locate,RatioCoefficientLookup.localSlot,
      Function.update_apply,Fin.ext_iff,low,Fin.ofNat]
  have hindex : selectedCut xs coeff pre word tail
      (RatioCoefficientLookup.locate 10) =
      List.replicate (coeff.take pre.length).length true := by
    rw [hp]
    simp [selectedCut,RatioRequestFrame.selected,RatioPhysicalFold.selected,
      RatioPhysicalFold.boundary,StatefulListScheduler.initialBank,
      RatioCoefficientLookup.locate,RatioCoefficientLookup.localSlot,
      Function.update_apply,Fin.ext_iff,low,Fin.ofNat]
  have hlookup : ∀ j : CylinderContextScanStep.Stack, j ≠ 8 → j ≠ 10 →
      selectedCut xs coeff pre word tail (RatioCoefficientLookup.locate j) = [] := by
    intro j h8 h10
    fin_cases j <;>
      first | contradiction | exact hsmall _ (by decide) (by decide)
  have hold : selectedCut xs coeff pre word tail (low 6) = word := by
    simp [selectedCut,RatioRequestFrame.selected,RatioPhysicalFold.selected,
      Function.update_apply,Fin.ext_iff,low,Fin.ofNat]
  have hout : selectedCut xs coeff pre word tail (low 9) =
      outputAt xs.length coeff pre := by
    simp [selectedCut,RatioRequestFrame.selected,RatioPhysicalFold.selected,
      RatioPhysicalFold.boundary,StatefulListScheduler.initialBank,
      Function.update_apply,Fin.ext_iff,low,Fin.ofNat]
  have hblank : ∀ i,selectedCut xs coeff pre word tail
      ((V2FieldContext.slots extraCount).machine i) = [] := by
    intro i
    have hi : i.val < 8 := by simpa only [V2FieldContext.eight_stacks] using i.isLt
    apply RatioRequestFrame.selected_high
    · change 15 ≤ 16+i.val; omega
    · intro he; have hv := congrArg Fin.val he
      change 16+i.val=25 at hv; omega
  have hmass : ∀ i,selectedCut xs coeff pre word tail
      ((RatioMassProjection.slots extraCount).machine i) = [] := by
    intro i
    have hi : i.val < 5 := by simpa only [RatioMassProjection.five_stacks] using i.isLt
    apply RatioRequestFrame.selected_high
    · change 15 ≤ 16+i.val; omega
    · intro he; have hv := congrArg Fin.val he; change 16+i.val=25 at hv; omega
  obtain ⟨t,ht,hr⟩ := RatioPairItem.outputs
    (selectedCut xs coeff pre word tail) (coeff.take pre.length)
    (coefficient coeff pre.length) (coeff.drop (pre.length+1)) word
    (outputAt xs.length coeff pre) hsource hindex hlookup hold hout
    (hsmall 26 (by decide) (by decide)) (hsmall 27 (by decide) (by decide))
    (hsmall 28 (by decide) (by decide))
    (hsmall 30 (by decide) (by decide)) (hsmall 31 (by decide) (by decide)) hmass hblank
  refine ⟨t,ht,?_⟩
  simpa only [postCut,outputAt_append] using hr

noncomputable def cutTime (xs coeff : List (List Bool))
    (hlen : coeff.length=xs.length) (pre : List (List Bool)) (word : List Bool)
    (tail : List (List Bool)) : Nat :=
  if hs : pre ++ word :: tail=xs then
    Classical.choose (cut_run xs coeff hlen pre word tail hs) else 0

noncomputable def contract (xs coeff : List (List Bool))
    (hlen : coeff.length=xs.length) :
    RatioIndexedScheduler.CallbackContract RatioPairItem.program
      RatioPairItem.start RatioPairItem.control xs
      (outputAt xs.length coeff) (SourceListEncoding.encode coeff) where
  extra := RatioRequestFrame.extra []
  time := cutTime xs coeff hlen
  control := fun _ _ _ => RatioPairItem.control
  state := postCut xs coeff
  callback_run := by
    intro pre word tail hs
    have h := (Classical.choose_spec (cut_run xs coeff hlen pre word tail hs)).2
    simpa only [cutTime,dif_pos hs,RatioRequestFrame.frame_selected,selectedCut] using h
  post := by
    intro pre word tail hs
    have hc := RatioRequestFrame.cleanup
      (SourceListEncoding.encode (pre ++ word :: tail))
      (SourceListEncoding.fields tail) word (outputAt xs.length coeff pre)
      (outputAt xs.length coeff (pre ++ [word])) (SourceListEncoding.encode coeff) []
      pre.length tail.length
    have he : Function.update
      (Function.update (selectedCut xs coeff pre word tail) (low 6) []) (low 9)
        (outputAt xs.length coeff (pre ++ [word])) =
      Function.update (postCut xs coeff pre word tail) (low 6) [] := by
      exact Function.update_comm (by simp [low,Fin.ext_iff,Fin.ofNat]) _ _ _
    change BitMachineClearBank.cleared StatefulListScheduler.cleanBank
      (Function.update (Function.update (selectedCut xs coeff pre word tail) (low 6) [])
        (low 9) (outputAt xs.length coeff (pre ++ [word]))) = _ at hc
    rw [he] at hc
    have hclear : BitMachineClearBank.cleared StatefulListScheduler.cleanBank
        (Function.update (postCut xs coeff pre word tail) (low 6) []) =
      BitMachineClearBank.cleared StatefulListScheduler.cleanBank
        (postCut xs coeff pre word tail) := by
      funext j
      by_cases hj : ∃ i, StatefulListScheduler.cleanBank (N := extraCount) i = j
      · simp [BitMachineClearBank.cleared,hj]
      · have hn : j ≠ low 6 := by
          intro he
          apply hj
          exact ⟨6,by subst j; simp [StatefulListScheduler.cleanBank,
            LargeContextListScheduler.cleanBank,low,Fin.ext_iff,Fin.ofNat]⟩
        simp [BitMachineClearBank.cleared,hj,Function.update_of_ne hn]
    rw [hclear] at hc
    simp only [hc,RatioRequestFrame.increment,RatioRequestFrame.frame_initial]

noncomputable def program := StatefulListScheduler.program RatioPairItem.program
  RatioPairItem.start RatioPairItem.control
noncomputable def clock (xs coeff : List (List Bool))
    (hlen : coeff.length=xs.length) : Nat :=
  RatioIndexedScheduler.remainingBudget RatioPairItem.program
    RatioPairItem.start RatioPairItem.control xs
    (outputAt xs.length coeff) (SourceListEncoding.encode coeff)
    (contract xs coeff hlen) [] xs

theorem runs (xs coeff : List (List Bool))
    (hlen : coeff.length=xs.length) :
    ∃ t ≤ clock xs coeff hlen, ∃ v,
      ((advance program)^[t])
        (⟨some (.inr (.inr .check)),
          StatefulListScheduler.getterControl RatioPairItem.control
            (CylinderContextScanStep.copyControl ((),none)),
          RatioRequestFrame.boundary (SourceListEncoding.encode xs)
            (EncodedCommunication.natField xs.length) (SourceListEncoding.encode coeff)
            [] 0 xs.length⟩ : TM2.Cfg (fun _ : Stack => Bool) _ _) =
        ⟨none,v,RatioRequestFrame.boundary (SourceListEncoding.encode xs)
          (SourceListEncoding.encode (pairs xs coeff))
          (SourceListEncoding.encode coeff) [] xs.length 0⟩ := by
  classical
  obtain ⟨t,ht,v,hr⟩ := RatioIndexedScheduler.run_remaining
    RatioPairItem.program RatioPairItem.start RatioPairItem.control
    xs (outputAt xs.length coeff) (SourceListEncoding.encode coeff)
    (contract xs coeff hlen) [] xs
    (StatefulListScheduler.getterControl RatioPairItem.control
      (CylinderContextScanStep.copyControl ((),none))) (by simp)
  refine ⟨t,ht,v,?_⟩
  simpa only [StatefulListScheduler.run,program,
    contract,RatioRequestFrame.frame_initial,List.nil_append,List.length_nil,
    outputAt_nil,outputAt_all] using hr

#print axioms runs
end CurrentAdditive.RatioPairList
