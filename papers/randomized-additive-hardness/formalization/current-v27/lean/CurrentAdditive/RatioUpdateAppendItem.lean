import CurrentAdditive.RatioUpdateItem
import CurrentAdditive.RatioV2Append

set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

/-! A concrete indexed update-request callback: get the matching coefficient,
copy the scalar, serialize the triple, frame it with V2 length framing,
append it to bank9, and clear the consumed source record. -/

noncomputable section
namespace CurrentAdditive.RatioUpdateAppendItem
open Turing EthInapproximability.CurrentPaper BitMachineEncoding
open MinimumRatioCallbackLayout MinimumRatioContext

abbrev Label := BitMachineRawSequence.Label RatioUpdateItem.Label RatioV2Append.Label
abbrev Control := RatioUpdateItem.Control × RatioV2Append.Control
noncomputable def program := BitMachineRawSequence.program RatioUpdateItem.program
  RatioV2Append.program RatioV2Append.start RatioUpdateItem.control RatioV2Append.control
noncomputable def start : Label := BitMachineRawSequence.leftLabel RatioUpdateItem.start
noncomputable def control : Control := (RatioUpdateItem.control,RatioV2Append.control)
noncomputable def clock (pre : List (List Bool)) (c : List Bool)
    (tail : List (List Bool)) (old lambda output : List Bool) : Nat :=
  RatioUpdateItem.clock pre c tail old lambda +
    RatioV2Append.clock output (RatioRequestSerializer.bytes old lambda c)+1

theorem outputs (S : Bank) (pre : List (List Bool)) (c : List Bool)
    (tail : List (List Bool)) (old lambda output : List Bool)
    (hsource : S (RatioCoefficientLookup.locate 8) =
      SourceListEncoding.encode (pre ++ c :: tail))
    (hindex : S (RatioCoefficientLookup.locate 10) = List.replicate pre.length true)
    (hlookup : ∀ j : CylinderContextScanStep.Stack, j ≠ 8 → j ≠ 10 →
      S (RatioCoefficientLookup.locate j) = [])
    (hold : S (low 6) = old) (hlambda : S (low 25) = lambda)
    (houtput : S (low 9) = output)
    (h26 : S (low 26) = []) (h27 : S (low 27) = [])
    (h28 : S (low 28) = []) (h29 : S (low 29) = [])
    (h30 : S (low 30) = []) (h31 : S (low 31) = [])
    (hblank : ∀ i, S ((V2FieldContext.slots extraCount).machine i) = []) :
    ∃ t ≤ clock pre c tail old lambda output,
      ((advance program)^[t])
        (⟨some start,control,S⟩ : TM2.Cfg (fun _ : Stack => Bool) _ _) =
        ⟨none,control,Function.update (Function.update S (low 6) []) (low 9)
          (output++V2FieldContext.field (RatioRequestSerializer.bytes old lambda c))⟩ := by
  have hne (a b : Fin 32) (h : a ≠ b) : low a ≠ low b := by
    intro he
    apply h
    apply Fin.ext
    exact congrArg (fun i : Stack => i.val) he
  let request := RatioRequestSerializer.bytes old lambda c
  let S1 := Function.update (Function.update S (low 6) []) (low 28) request
  obtain ⟨a,ha,hrA⟩ := RatioUpdateItem.item_run S pre c tail old lambda
    hsource hindex hlookup hold hlambda h26 h27 h28 h29 h30
  have h9S1 : S1 (low 9) = output := by
    simp [S1,Function.update_of_ne,hne 9 28 (by decide),hne 9 6 (by decide),houtput]
  have h30S1 : S1 (low 30) = [] := by
    simp [S1,Function.update_of_ne,hne 30 28 (by decide),hne 30 6 (by decide),h30]
  have h31S1 : S1 (low 31) = [] := by
    simp [S1,Function.update_of_ne,hne 31 28 (by decide),hne 31 6 (by decide),h31]
  have h26S1 : S1 (low 26) = [] := by
    simp [S1,Function.update_of_ne,hne 26 28 (by decide),hne 26 6 (by decide),h26]
  have h27S1 : S1 (low 27) = [] := by
    simp [S1,Function.update_of_ne,hne 27 28 (by decide),hne 27 6 (by decide),h27]
  have hblankS1 : ∀ i, S1 ((V2FieldContext.slots extraCount).machine i) = [] := by
    intro i
    have hi : i.val < 8 := by simpa only [V2FieldContext.eight_stacks] using i.isLt
    have hn6 : (V2FieldContext.slots extraCount).machine i ≠ low 6 := by
      intro he; have hv := congrArg Fin.val he
      change 16+i.val=6 at hv; omega
    have hn28 : (V2FieldContext.slots extraCount).machine i ≠ low 28 := by
      intro he; have hv := congrArg Fin.val he
      change 16+i.val=28 at hv; omega
    simpa only [S1,Function.update_of_ne hn28,Function.update_of_ne hn6] using hblank i
  obtain ⟨b,hb,hrB⟩ := RatioV2Append.outputs S1 output request h9S1
    (by simp [S1]) h30S1 h31S1 h26S1 h27S1 hblankS1
  obtain ⟨t,ht,hr⟩ := BitMachineRawSequence.runs RatioUpdateItem.program
    RatioV2Append.program RatioUpdateItem.start RatioV2Append.start
    RatioUpdateItem.control RatioUpdateItem.control RatioV2Append.control RatioV2Append.control
    S S1 _ a b hrA hrB
  have hout : Function.update S1 (low 28) [] = Function.update S (low 6) [] := by
    simp only [S1,Function.update_idem]
    funext j
    by_cases he : j=low 28
    · subst j
      simp [Function.update_of_ne,hne 28 6 (by decide),h28]
    · simp only [Function.update_of_ne he]
  rw [hout] at hr
  refine ⟨t,?_,?_⟩
  · unfold clock
    dsimp only [request] at hb
    omega
  · simpa only [program,start,control,request] using hr

#print axioms outputs
end CurrentAdditive.RatioUpdateAppendItem
