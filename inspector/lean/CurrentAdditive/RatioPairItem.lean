import CurrentAdditive.RatioCoefficientLookup
import CurrentAdditive.RatioMassProjection
import CurrentAdditive.RatioPairSerializer
import CurrentAdditive.RatioV2Append

set_option maxHeartbeats 1200000
set_option maxRecDepth 10000
noncomputable section
namespace CurrentAdditive.RatioPairItem
open Turing EthInapproximability.CurrentPaper BitMachineEncoding
open MinimumRatioCallbackLayout MinimumRatioContext

abbrev MassLabel := MachineInvokeFull.LabelFull RatioMassProjection.W
abbrev MassControl := MachineInvokeFull.ControlFull RatioMassProjection.W
noncomputable def massStart : MassLabel := MachineInvokeFull.start (RatioMassProjection.slots extraCount)
noncomputable def massControl : MassControl := MachineInvokeFull.control (RatioMassProjection.slots extraCount)
noncomputable def massProgram := RatioMassProjection.program extraCount
abbrev PrepLabel := BitMachineRawSequence.Label
  (BitMachineRawSequence.Label RatioCoefficientLookup.Label RatioCoefficientLookup.ClearLabel) MassLabel
abbrev PrepControl := (RatioCoefficientLookup.Control × RatioCoefficientLookup.ClearControl) × MassControl
noncomputable def prepProgram := BitMachineRawSequence.program RatioCoefficientLookup.fullProgram
  massProgram massStart RatioCoefficientLookup.fullControl massControl
noncomputable def prepStart : PrepLabel := BitMachineRawSequence.leftLabel RatioCoefficientLookup.fullStart
noncomputable def prepControl : PrepControl := (RatioCoefficientLookup.fullControl,massControl)
abbrev BuildLabel := BitMachineRawSequence.Label PrepLabel RatioPairSerializer.Label
abbrev BuildControl := PrepControl × Option Bool
noncomputable def buildProgram := BitMachineRawSequence.program prepProgram
  RatioPairSerializer.program (.inl (.emit 0)) prepControl none
noncomputable def buildStart : BuildLabel := BitMachineRawSequence.leftLabel prepStart
noncomputable def buildControl : BuildControl := (prepControl,none)
abbrev Label := BitMachineRawSequence.Label BuildLabel RatioV2Append.Label
abbrev Control := BuildControl × RatioV2Append.Control
noncomputable def program := BitMachineRawSequence.program buildProgram
  RatioV2Append.program RatioV2Append.start buildControl RatioV2Append.control
noncomputable def start : Label := BitMachineRawSequence.leftLabel buildStart
noncomputable def control : Control := (buildControl,RatioV2Append.control)
noncomputable def massWord (old : List Bool) : List Bool := BankFieldProjection.result (1 : Fin 2) old
noncomputable def pairWord (old coeff : List Bool) : List Bool :=
  RatioPairSerializer.bytes (massWord old) coeff
noncomputable def clock (pre : List (List Bool)) (c : List Bool)
    (tail : List (List Bool)) (old output : List Bool) : Nat :=
  RatioCoefficientLookup.clock pre c tail + RatioMassProjection.clock old + 1 +
    ((massWord old).length+1+(c.length+1)+(pairWord old c).length+3)+1+
    RatioV2Append.clock output (pairWord old c)+1

theorem outputs (S : Bank) (pre : List (List Bool)) (c : List Bool)
    (tail : List (List Bool)) (old output : List Bool)
    (hsource : S (RatioCoefficientLookup.locate 8) = SourceListEncoding.encode (pre ++ c :: tail))
    (hindex : S (RatioCoefficientLookup.locate 10) = List.replicate pre.length true)
    (hlookup : ∀ j : CylinderContextScanStep.Stack,j ≠ 8 → j ≠ 10 →
      S (RatioCoefficientLookup.locate j) = [])
    (hold : S (low 6) = old) (houtput : S (low 9) = output)
    (h26 : S (low 26) = []) (h27 : S (low 27) = [])
    (h28 : S (low 28) = []) (h30 : S (low 30) = []) (h31 : S (low 31) = [])
    (hmass : ∀ i,S ((RatioMassProjection.slots extraCount).machine i) = [])
    (hframe : ∀ i,S ((V2FieldContext.slots extraCount).machine i) = []) :
    ∃ t ≤ clock pre c tail old output,
      ((advance program)^[t]) (⟨some start,control,S⟩ : TM2.Cfg (fun _ : Stack => Bool) _ _) =
      ⟨none,control,Function.update S (low 9)
        (output++V2FieldContext.field (pairWord old c))⟩ := by
  have hne (a b : Fin 32) (h : a ≠ b) : low a ≠ low b := by
    intro he; apply h; apply Fin.ext
    exact congrArg (fun i : Stack => i.val) he
  have h21 : S (low 21) = [] := by simpa only [RatioCoefficientLookup.locate,RatioCoefficientLookup.localSlot] using hlookup 6 (by decide) (by decide)
  have h24 : S (low 24) = [] := by simpa only [RatioCoefficientLookup.locate,RatioCoefficientLookup.localSlot] using hlookup 11 (by decide) (by decide)
  let S1 := Function.update S (low 21) c
  let S2 := Function.update S1 (low 24) (massWord old)
  let S3 := Function.update S (low 28) (pairWord old c)
  obtain ⟨a,ha,hrA⟩ := RatioCoefficientLookup.full_run S pre c tail hsource hindex hlookup
  have hmass6 : S1 (RatioMassProjection.slots extraCount).source = old := by
    change S1 (low 6) = old
    simp [S1,Function.update_of_ne,hne 6 21 (by decide),hold]
  have hmass24 : S1 (RatioMassProjection.slots extraCount).target = [] := by
    change S1 (low 24) = []
    simp [S1,Function.update_of_ne,hne 24 21 (by decide),h24]
  have hmass31 : S1 (RatioMassProjection.slots extraCount).scratch = [] := by
    change S1 (low 31) = []
    simp [S1,Function.update_of_ne,hne 31 21 (by decide),h31]
  have hmassS1 : ∀ i,S1 ((RatioMassProjection.slots extraCount).machine i) = [] := by
    intro i
    have hi : i.val < 5 := by simpa only [RatioMassProjection.five_stacks] using i.isLt
    have hn : (RatioMassProjection.slots extraCount).machine i ≠ low 21 := by
      intro he; have hv := congrArg Fin.val he
      change 16+i.val=21 at hv; omega
    simpa only [S1,Function.update_of_ne hn] using hmass i
  obtain ⟨b,hb,hrB⟩ := RatioMassProjection.outputs extraCount S1 old hmass6 hmass24 hmass31 hmassS1
  obtain ⟨ab,hab,hrAB⟩ := BitMachineRawSequence.runs RatioCoefficientLookup.fullProgram
    massProgram RatioCoefficientLookup.fullStart massStart
    RatioCoefficientLookup.fullControl RatioCoefficientLookup.fullControl massControl massControl
    S S1 S2 a b
    (by simpa only [S1,RatioCoefficientLookup.locate,RatioCoefficientLookup.localSlot] using hrA)
    (by simpa only [massProgram,massStart,massControl,S2,massWord,low] using hrB)
  have hx : S2 (RatioPairSerializer.locate (.inl 0)) = massWord old := by
    simp [S2,RatioPairSerializer.locate,RatioPairSerializer.localSlot]
  have hy : S2 (RatioPairSerializer.locate (.inl 1)) = c := by
    simp [S2,S1,RatioPairSerializer.locate,RatioPairSerializer.localSlot,
      Function.update_of_ne,hne 21 24 (by decide)]
  have hs : ∀ i : Fin 3,S2 (RatioPairSerializer.locate (.inr i)) = [] := by
    intro i; fin_cases i
    · change S2 (low 26) = []; simp [S2,S1,Function.update_of_ne,hne 26 24 (by decide),hne 26 21 (by decide),h26]
    · change S2 (low 27) = []; simp [S2,S1,Function.update_of_ne,hne 27 24 (by decide),hne 27 21 (by decide),h27]
    · change S2 (low 28) = []; simp [S2,S1,Function.update_of_ne,hne 28 24 (by decide),hne 28 21 (by decide),h28]
  obtain ⟨d,hd,hrD⟩ := RatioPairSerializer.serialize_request S2 (massWord old) c hx hy hs
  have hser : RatioPairSerializer.result S2 (massWord old) c = S3 := by
    funext j
    by_cases h28j : j=low 28
    · subst j; simp [RatioPairSerializer.result,RatioPairSerializer.locate,RatioPairSerializer.localSlot,S3,pairWord]
    · by_cases h21j : j=low 21
      · subst j; simp [RatioPairSerializer.result,RatioPairSerializer.locate,RatioPairSerializer.localSlot,S3,
          Function.update_of_ne,hne 21 28 (by decide),hne 21 24 (by decide),h21]
      · by_cases h24j : j=low 24
        · subst j; simp [RatioPairSerializer.result,RatioPairSerializer.locate,RatioPairSerializer.localSlot,S3,
            Function.update_of_ne,hne 24 28 (by decide),hne 24 21 (by decide),h24]
        · simp [RatioPairSerializer.result,RatioPairSerializer.locate,RatioPairSerializer.localSlot,S3,S2,S1,
            Function.update_of_ne,h28j,h21j,h24j]
  rw [hser] at hrD
  obtain ⟨abd,habd,hrABD⟩ := BitMachineRawSequence.runs prepProgram RatioPairSerializer.program
    prepStart (.inl (.emit 0)) prepControl prepControl none none S S2 S3 ab d
    (by simpa only [prepProgram,prepStart,prepControl] using hrAB) hrD
  have h9S3 : S3 (low 9) = output := by simp [S3,Function.update_of_ne,hne 9 28 (by decide),houtput]
  have h30S3 : S3 (low 30) = [] := by simp [S3,Function.update_of_ne,hne 30 28 (by decide),h30]
  have h31S3 : S3 (low 31) = [] := by simp [S3,Function.update_of_ne,hne 31 28 (by decide),h31]
  have h26S3 : S3 (low 26) = [] := by simp [S3,Function.update_of_ne,hne 26 28 (by decide),h26]
  have h27S3 : S3 (low 27) = [] := by simp [S3,Function.update_of_ne,hne 27 28 (by decide),h27]
  have hframeS3 : ∀ i,S3 ((V2FieldContext.slots extraCount).machine i) = [] := by
    intro i
    have hi : i.val < 8 := by simpa only [V2FieldContext.eight_stacks] using i.isLt
    have hn : (V2FieldContext.slots extraCount).machine i ≠ low 28 := by
      intro he; have hv := congrArg Fin.val he
      change 16+i.val=28 at hv; omega
    simpa only [S3,Function.update_of_ne hn] using hframe i
  obtain ⟨e,he,hrE⟩ := RatioV2Append.outputs S3 output (pairWord old c) h9S3
    (by simp [S3]) h30S3 h31S3 h26S3 h27S3 hframeS3
  have hrest : Function.update S3 (low 28) [] = S := by
    simp only [S3,Function.update_idem]
    exact (congrArg (fun w => Function.update S (low 28) w) h28.symm).trans
      (Function.update_eq_self _ _)
  rw [hrest] at hrE
  obtain ⟨t,ht,hr⟩ := BitMachineRawSequence.runs buildProgram RatioV2Append.program
    buildStart RatioV2Append.start buildControl buildControl RatioV2Append.control RatioV2Append.control
    S S3 _ abd e (by simpa only [buildProgram,buildStart,buildControl] using hrABD) hrE
  refine ⟨t,?_,?_⟩
  · unfold clock; dsimp only [pairWord] at *; omega
  · simpa only [program,start,control] using hr

#print axioms outputs
end CurrentAdditive.RatioPairItem
