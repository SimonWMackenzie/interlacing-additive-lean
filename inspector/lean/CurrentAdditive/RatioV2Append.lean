import CurrentAdditive.V2FieldContext
import CurrentAdditive.MinimumRatioCallbackLayout
import CurrentAdditive.CodeDAppendAtEnd15

set_option maxHeartbeats 2000000
set_option maxSynthPendingDepth 100
set_option maxRecDepth 10000

/-! The outer request list uses V2 length-and-payload fields. Frame the actual
request, append its field to bank 9, and physically remove the temporary
request. Every other ambient bank is preserved. -/

noncomputable section

namespace CurrentAdditive.RatioV2Append

open Turing EthInapproximability.CurrentPaper BitMachineEncoding
open MinimumRatioCallbackLayout MinimumRatioContext

noncomputable def appendSlots : Fin 15 ↪ Stack where
  toFun i := low (![0,1,2,3,4,30,6,7,8,9,10,26,12,13,27] i)
  inj' := by
    intro a b h
    have hh := congrArg Fin.val h
    fin_cases a <;> fin_cases b <;> simp_all [low]

def appendProgram (l : CodeDAppendAtEnd15.Label) :=
  BitMachineStackEmbedding.stackStmt appendSlots (CodeDAppendAtEnd15.program l)

private theorem advance_frame (S : Bank) (c : CodeDAppendAtEnd15.Config) :
    advance appendProgram (BitMachineStackEmbedding.stackCfg appendSlots S c) =
      BitMachineStackEmbedding.stackCfg appendSlots S
        (advance CodeDAppendAtEnd15.program c) := by
  cases c with
  | mk l v stk =>
    cases l with
    | none => rfl
    | some l =>
        exact BitMachineStackEmbedding.stack_stepAux appendSlots S (CodeDAppendAtEnd15.program l) v stk

private theorem run_frame (S : Bank) (c : CodeDAppendAtEnd15.Config) (t : Nat) :
    ((advance appendProgram)^[t]) (BitMachineStackEmbedding.stackCfg appendSlots S c) =
      BitMachineStackEmbedding.stackCfg appendSlots S
        ((advance CodeDAppendAtEnd15.program)^[t] c) := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [Function.iterate_succ_apply',ih,advance_frame,
      Function.iterate_succ_apply']

theorem append_run (S : Bank) (output payload : List Bool)
    (h9 : S (low 9) = output) (h30 : S (low 30) = payload)
    (h26 : S (low 26) = []) (h27 : S (low 27) = []) :
    ((advance appendProgram)^[4*output.length+2*payload.length+7])
      (⟨some .saveScan,((),none),S⟩ :
        TM2.Cfg (fun _ : Stack => Bool) _ _) =
      ⟨none,((),none),
        Function.update (Function.update S (low 30) []) (low 9) (output++payload)⟩ := by
  let F : Fin 15 → List Bool := fun i => S (appendSlots i)
  have hinit : CodeDAppendAtEnd15.initialBank F output payload = F := by
    have hF9 : F 9 = output := by simpa only [F,appendSlots] using h9
    have hF5 : F 5 = payload := by simpa only [F,appendSlots] using h30
    unfold CodeDAppendAtEnd15.initialBank
    rw [← hF9,Function.update_eq_self,← hF5,Function.update_eq_self]
  have hb : BitMachineStackEmbedding.bank appendSlots S F = S :=
    BitMachineStackEmbedding.bank_restrict appendSlots S
  have hr := CodeDAppendAtEnd15.append_run F output payload
    (by simpa only [F,appendSlots] using h26)
    (by simpa only [F,appendSlots] using h27)
  rw [hinit] at hr
  have he := run_frame S
    (⟨some .saveScan,((),none),F⟩ : CodeDAppendAtEnd15.Config)
    (4*output.length+2*payload.length+6)
  change CodeDAppendAtEnd15.run _ _ = _ at hr
  change _ = BitMachineStackEmbedding.stackCfg appendSlots S
    (CodeDAppendAtEnd15.run _ _) at he
  rw [hr] at he
  simp only [BitMachineStackEmbedding.stackCfg,hb,
    BitMachineStackEmbedding.bank_update] at he
  have hslots5 : appendSlots 5 = low 30 := rfl
  have hslots9 : appendSlots 9 = low 9 := rfl
  rw [hslots5,hslots9] at he
  have hbank : Function.update
      (Function.update (Function.update S (low 9) []) (low 30) [])
      (low 9) (output++payload) =
      Function.update (Function.update S (low 30) []) (low 9) (output++payload) := by
    funext j
    by_cases hj : j = low 9
    · subst j; simp
    · by_cases h30j : j = low 30
      · subst j; simp [Function.update_of_ne,hj]
      · simp [Function.update_of_ne,hj,h30j]
  rw [hbank] at he
  rw [show 4*output.length+2*payload.length+7 =
      (4*output.length+2*payload.length+6)+1 by omega,
    Function.iterate_succ_apply',he]
  rfl

def clearProgram : Bool → TM2.Stmt (fun _ : Stack => Bool) Bool (Unit × Option Bool)
  | false => BitMachineClearBank.clearStep (low 28) false true
  | true => .halt

theorem clear_run (S : Bank) (word : List Bool) (h28 : S (low 28) = word) :
    ((advance clearProgram)^[word.length+2])
      (⟨some false,((),none),S⟩ : TM2.Cfg (fun _ : Stack => Bool) _ _) =
      ⟨none,((),none),Function.update S (low 28) []⟩ := by
  have h := BitMachineClearBank.clear_one_run clearProgram (low 28) false true
    rfl () S
  rw [h28] at h
  rw [show word.length+2 = (word.length+1)+1 by omega,
    Function.iterate_succ_apply',h]
  rfl

noncomputable def frameProgram := V2FieldContext.program extraCount
abbrev FrameLabel := MachineInvokeFull.LabelFull V2FieldContext.W
abbrev FrameControl := MachineInvokeFull.ControlFull V2FieldContext.W
abbrev FirstLabel := BitMachineRawSequence.Label FrameLabel CodeDAppendAtEnd15.Label
abbrev FirstControl := FrameControl × CodeDAppendAtEnd15.Control
abbrev Label := BitMachineRawSequence.Label FirstLabel Bool
abbrev Control := FirstControl × (Unit × Option Bool)

noncomputable def frameStart : FrameLabel := MachineInvokeFull.start (V2FieldContext.slots extraCount)
noncomputable def frameControl : FrameControl := MachineInvokeFull.control (V2FieldContext.slots extraCount)

noncomputable def firstProgram := BitMachineRawSequence.program frameProgram appendProgram
  .saveScan frameControl ((),none)
noncomputable def firstStart : FirstLabel := BitMachineRawSequence.leftLabel frameStart
noncomputable def firstControl : FirstControl := (frameControl,((),none))

noncomputable def program := BitMachineRawSequence.program firstProgram clearProgram
  false firstControl ((),none)
noncomputable def start : Label := BitMachineRawSequence.leftLabel firstStart
noncomputable def control : Control := (firstControl,((),none))

noncomputable def clock (output request : List Bool) : Nat :=
  V2FieldContext.clock request +
    (4*output.length+2*(V2FieldContext.field request).length+7)+1+
    (request.length+2)+1

theorem outputs (S : Bank) (output request : List Bool)
    (h9 : S (low 9) = output) (h28 : S (low 28) = request)
    (h30 : S (low 30) = []) (h31 : S (low 31) = [])
    (h26 : S (low 26) = []) (h27 : S (low 27) = [])
    (hblank : ∀ i, S ((V2FieldContext.slots extraCount).machine i) = []) :
    ∃ t ≤ clock output request,
      ((advance program)^[t])
        (⟨some start,control,S⟩ : TM2.Cfg (fun _ : Stack => Bool) _ _) =
        ⟨none,control,Function.update (Function.update S (low 28) []) (low 9)
          (output++V2FieldContext.field request)⟩ := by
  have hne (a b : Fin 32) (h : a ≠ b) : low a ≠ low b := by
    intro he
    apply h
    apply Fin.ext
    exact congrArg (fun i : Stack => i.val) he
  let S1 := Function.update S (low 30) (V2FieldContext.field request)
  let S2 := Function.update S (low 9) (output++V2FieldContext.field request)
  obtain ⟨a,ha,hrA⟩ := V2FieldContext.outputs extraCount S request
    (by simpa only [low] using h28) (by simpa only [low] using h30)
    (by simpa only [low] using h31) hblank
  have h9S1 : S1 (low 9) = output := by
    simp [S1,Function.update_of_ne,hne 9 30 (by decide),h9]
  have h26S1 : S1 (low 26) = [] := by
    simp [S1,Function.update_of_ne,hne 26 30 (by decide),h26]
  have h27S1 : S1 (low 27) = [] := by
    simp [S1,Function.update_of_ne,hne 27 30 (by decide),h27]
  have hrB := append_run S1 output (V2FieldContext.field request) h9S1
    (by simp [S1]) h26S1 h27S1
  have hfinal : Function.update S1 (low 30) [] = S := by
    simp only [S1,Function.update_idem]
    rw [← h30,Function.update_eq_self]
  rw [hfinal] at hrB
  obtain ⟨ab,hab,hrAB⟩ := BitMachineRawSequence.runs frameProgram appendProgram
    frameStart .saveScan frameControl frameControl ((),none) ((),none)
    S S1 S2 a (4*output.length+2*(V2FieldContext.field request).length+7)
    (by simpa only [frameProgram,frameStart,frameControl,S1,low] using hrA) hrB
  have h28S2 : S2 (low 28) = request := by
    simp [S2,Function.update_of_ne,hne 28 9 (by decide),h28]
  have hrC := clear_run S2 request h28S2
  obtain ⟨t,ht,hr⟩ := BitMachineRawSequence.runs firstProgram clearProgram
    firstStart false firstControl firstControl ((),none) ((),none)
    S S2 (Function.update S2 (low 28) []) ab (request.length+2)
    (by simpa only [firstProgram,firstStart,firstControl] using hrAB) hrC
  have hout : Function.update S2 (low 28) [] =
      Function.update (Function.update S (low 28) []) (low 9)
        (output++V2FieldContext.field request) := by
    funext j
    by_cases h28j : j = low 28
    · subst j
      simp [S2,Function.update_of_ne,hne 28 9 (by decide)]
    · by_cases h9j : j = low 9
      · subst j; simp [S2,Function.update_of_ne,h28j]
      · simp [S2,Function.update_of_ne,h28j,h9j]
  rw [hout] at hr
  refine ⟨t,?_,?_⟩
  · unfold clock
    omega
  · simpa only [program,start,control] using hr

#print axioms outputs

end CurrentAdditive.RatioV2Append
