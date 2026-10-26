import CurrentAdditive.RatioIndexedScheduler
import CurrentAdditive.RatioRequestFrame
import CurrentAdditive.RatioRequestListSpec

set_option maxHeartbeats 1500000
set_option maxRecDepth 10000

/-! Literal indexed request-list producer from its explicit prepared header
and unary source count. Each item physically reads the same coefficient
position, serializes and V2-frames its request, and appends it. Equal source
records may use different coefficients. -/
noncomputable section
namespace CurrentAdditive.RatioRequestList
open Turing EthInapproximability.CurrentPaper BitMachineEncoding
open MinimumRatioCallbackLayout CurrentAdditive.GaussListContext
open RatioRequestListSpec

noncomputable def selectedCut (xs coeff : List (List Bool)) (lambda : List Bool)
    (pre : List (List Bool)) (word : List Bool) (tail : List (List Bool)) : Bank :=
  RatioRequestFrame.selected (SourceListEncoding.encode (pre ++ word :: tail))
    (SourceListEncoding.fields tail) word (outputAt xs.length coeff lambda pre)
    (SourceListEncoding.encode coeff) lambda pre.length tail.length

noncomputable def postCut (xs coeff : List (List Bool)) (lambda : List Bool)
    (pre : List (List Bool)) (word : List Bool) (tail : List (List Bool)) : Bank :=
  Function.update
    (Function.update (selectedCut xs coeff lambda pre word tail) (low 6) [])
    (low 9) (outputAt xs.length coeff lambda (pre ++ [word]))

theorem cut_run (xs coeff : List (List Bool)) (lambda : List Bool)
    (hlen : coeff.length=xs.length) (pre : List (List Bool)) (word : List Bool)
    (tail : List (List Bool)) (hsplit : pre ++ word :: tail=xs) :
    ∃ t ≤ RatioUpdateAppendItem.clock (coeff.take pre.length)
      (coefficient coeff pre.length) (coeff.drop (pre.length+1)) word lambda
        (outputAt xs.length coeff lambda pre),
      ((advance RatioUpdateAppendItem.program)^[t])
        (⟨some RatioUpdateAppendItem.start,RatioUpdateAppendItem.control,
          selectedCut xs coeff lambda pre word tail⟩ :
          TM2.Cfg (fun _ : Stack => Bool) _ _) =
        ⟨none,RatioUpdateAppendItem.control,postCut xs coeff lambda pre word tail⟩ := by
  have hn : pre.length < coeff.length := by
    rw [hlen,← hsplit,List.length_append,List.length_cons]
    omega
  have hp := coefficient_prefix_length coeff pre.length hn
  have hc := coefficient_split coeff pre.length hn
  have hsmall (j : Fin 32) (hj : 15 ≤ j.val) (h25 : j ≠ 25) :
      selectedCut xs coeff lambda pre word tail (low j) = [] := by
    apply RatioRequestFrame.selected_high
    · simpa only [low,Fin.val_castAdd] using hj
    · intro he; apply h25; apply Fin.ext
      exact congrArg (fun k : Stack => k.val) he
  have hsource : selectedCut xs coeff lambda pre word tail
      (RatioCoefficientLookup.locate 8) =
      SourceListEncoding.encode (coeff.take pre.length ++
        coefficient coeff pre.length :: coeff.drop (pre.length+1)) := by
    rw [hc]
    simp [selectedCut,RatioRequestFrame.selected,RatioPhysicalFold.selected,
      RatioPhysicalFold.boundary,StatefulListScheduler.initialBank,
      RatioCoefficientLookup.locate,RatioCoefficientLookup.localSlot,
      Function.update_apply,Fin.ext_iff,low,Fin.ofNat]
  have hindex : selectedCut xs coeff lambda pre word tail
      (RatioCoefficientLookup.locate 10) =
      List.replicate (coeff.take pre.length).length true := by
    rw [hp]
    simp [selectedCut,RatioRequestFrame.selected,RatioPhysicalFold.selected,
      RatioPhysicalFold.boundary,StatefulListScheduler.initialBank,
      RatioCoefficientLookup.locate,RatioCoefficientLookup.localSlot,
      Function.update_apply,Fin.ext_iff,low,Fin.ofNat]
  have hlookup : ∀ j : CylinderContextScanStep.Stack, j ≠ 8 → j ≠ 10 →
      selectedCut xs coeff lambda pre word tail (RatioCoefficientLookup.locate j) = [] := by
    intro j h8 h10
    fin_cases j <;>
      first | contradiction | exact hsmall _ (by decide) (by decide)
  have hold : selectedCut xs coeff lambda pre word tail (low 6) = word := by
    simp [selectedCut,RatioRequestFrame.selected,RatioPhysicalFold.selected,
      Function.update_apply,Fin.ext_iff,low,Fin.ofNat]
  have hlambda : selectedCut xs coeff lambda pre word tail (low 25) = lambda := by
    simp [selectedCut,RatioRequestFrame.selected]
  have hout : selectedCut xs coeff lambda pre word tail (low 9) =
      outputAt xs.length coeff lambda pre := by
    simp [selectedCut,RatioRequestFrame.selected,RatioPhysicalFold.selected,
      RatioPhysicalFold.boundary,StatefulListScheduler.initialBank,
      Function.update_apply,Fin.ext_iff,low,Fin.ofNat]
  have hblank : ∀ i,selectedCut xs coeff lambda pre word tail
      ((V2FieldContext.slots extraCount).machine i) = [] := by
    intro i
    have hi : i.val < 8 := by simpa only [V2FieldContext.eight_stacks] using i.isLt
    apply RatioRequestFrame.selected_high
    · change 15 ≤ 16+i.val; omega
    · intro he; have hv := congrArg Fin.val he
      change 16+i.val=25 at hv; omega
  obtain ⟨t,ht,hr⟩ := RatioUpdateAppendItem.outputs
    (selectedCut xs coeff lambda pre word tail) (coeff.take pre.length)
    (coefficient coeff pre.length) (coeff.drop (pre.length+1)) word lambda
    (outputAt xs.length coeff lambda pre) hsource hindex hlookup hold hlambda hout
    (hsmall 26 (by decide) (by decide)) (hsmall 27 (by decide) (by decide))
    (hsmall 28 (by decide) (by decide)) (hsmall 29 (by decide) (by decide))
    (hsmall 30 (by decide) (by decide)) (hsmall 31 (by decide) (by decide)) hblank
  refine ⟨t,ht,?_⟩
  simpa only [postCut,outputAt_append] using hr

noncomputable def cutTime (xs coeff : List (List Bool)) (lambda : List Bool)
    (hlen : coeff.length=xs.length) (pre : List (List Bool)) (word : List Bool)
    (tail : List (List Bool)) : Nat :=
  if hs : pre ++ word :: tail=xs then
    Classical.choose (cut_run xs coeff lambda hlen pre word tail hs) else 0

noncomputable def contract (xs coeff : List (List Bool)) (lambda : List Bool)
    (hlen : coeff.length=xs.length) :
    RatioIndexedScheduler.CallbackContract RatioUpdateAppendItem.program
      RatioUpdateAppendItem.start RatioUpdateAppendItem.control xs
      (outputAt xs.length coeff lambda) (SourceListEncoding.encode coeff) where
  extra := RatioRequestFrame.extra lambda
  time := cutTime xs coeff lambda hlen
  control := fun _ _ _ => RatioUpdateAppendItem.control
  state := postCut xs coeff lambda
  callback_run := by
    intro pre word tail hs
    have h := (Classical.choose_spec (cut_run xs coeff lambda hlen pre word tail hs)).2
    simpa only [cutTime,dif_pos hs,RatioRequestFrame.frame_selected,selectedCut] using h
  post := by
    intro pre word tail hs
    simp only [postCut,selectedCut,RatioRequestFrame.cleanup,
      RatioRequestFrame.increment,RatioRequestFrame.frame_initial]

noncomputable def program := StatefulListScheduler.program RatioUpdateAppendItem.program
  RatioUpdateAppendItem.start RatioUpdateAppendItem.control
noncomputable def clock (xs coeff : List (List Bool)) (lambda : List Bool)
    (hlen : coeff.length=xs.length) : Nat :=
  RatioIndexedScheduler.remainingBudget RatioUpdateAppendItem.program
    RatioUpdateAppendItem.start RatioUpdateAppendItem.control xs
    (outputAt xs.length coeff lambda) (SourceListEncoding.encode coeff)
    (contract xs coeff lambda hlen) [] xs

theorem runs (xs coeff : List (List Bool)) (lambda : List Bool)
    (hlen : coeff.length=xs.length) :
    ∃ t ≤ clock xs coeff lambda hlen, ∃ v,
      ((advance program)^[t])
        (⟨some (.inr (.inr .check)),
          StatefulListScheduler.getterControl RatioUpdateAppendItem.control
            (CylinderContextScanStep.copyControl ((),none)),
          RatioRequestFrame.boundary (SourceListEncoding.encode xs)
            (EncodedCommunication.natField xs.length) (SourceListEncoding.encode coeff)
            lambda 0 xs.length⟩ : TM2.Cfg (fun _ : Stack => Bool) _ _) =
        ⟨none,v,RatioRequestFrame.boundary (SourceListEncoding.encode xs)
          (SourceListEncoding.encode (requests xs coeff lambda))
          (SourceListEncoding.encode coeff) lambda xs.length 0⟩ := by
  classical
  obtain ⟨t,ht,v,hr⟩ := RatioIndexedScheduler.run_remaining
    RatioUpdateAppendItem.program RatioUpdateAppendItem.start RatioUpdateAppendItem.control
    xs (outputAt xs.length coeff lambda) (SourceListEncoding.encode coeff)
    (contract xs coeff lambda hlen) [] xs
    (StatefulListScheduler.getterControl RatioUpdateAppendItem.control
      (CylinderContextScanStep.copyControl ((),none))) (by simp)
  refine ⟨t,ht,v,?_⟩
  simpa only [StatefulListScheduler.run,program,
    contract,RatioRequestFrame.frame_initial,List.nil_append,List.length_nil,
    outputAt_nil,outputAt_all] using hr

#print axioms runs
end CurrentAdditive.RatioRequestList
