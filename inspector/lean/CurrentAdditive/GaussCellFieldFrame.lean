import CurrentAdditive.GaussFetchedArithmetic
import CurrentAdditive.V2FieldContext

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

namespace CurrentAdditive.GaussCellFieldFrame
open Turing EthInapproximability.CurrentPaper BitMachineEncoding
open CurrentAdditive.MinimumRatioContext

abbrev RawBank := GaussFetchedArithmetic.Bank
abbrev Bank := MachineInvokeCore.StackN (32+GaussFetchedArithmetic.M.stackCount+10)

noncomputable def old : RawBank ↪ Bank := ⟨fun i => ⟨i.val,by omega⟩,by
  intro i j h; exact Fin.ext (congrArg (fun z : Bank => z.val) h)⟩
noncomputable def loc (i : Fin 64) : Bank := old (GaussFetchedArithmetic.lower i)
noncomputable def fresh (i : Fin 10) : Bank :=
  ⟨64+GaussFetchedArithmetic.M.stackCount+i.val,by omega⟩

noncomputable def copySlots : Fin 3 ↪ Bank := ⟨![loc 29,loc 28,fresh 9],by
  intro i j h
  fin_cases i <;> fin_cases j <;> first
  | rfl
  | have hv:=congrArg (fun z : Bank => z.val) h
    dsimp [loc,old,GaussFetchedArithmetic.lower,fresh] at hv
    omega⟩

noncomputable abbrev W := V2FieldContext.W
noncomputable def slots : MachineInvokeCore.Slots W (32+GaussFetchedArithmetic.M.stackCount+10) where
  machine := ⟨fun i => fresh ⟨i.val,by
    have hi : i.val<8 := by simpa only [V2FieldContext.eight_stacks] using i.isLt
    omega⟩,by
      intro i j h; apply Fin.ext
      have hv:=congrArg (fun z : Bank => z.val) h
      dsimp [fresh] at hv
      omega⟩
  source := loc 28
  target := loc 29
  scratch := fresh 8
  source_target := by intro h; have hv:=congrArg (fun z : Bank => z.val) h; change (28 : Nat)=29 at hv; omega
  source_scratch := by intro h; have hv:=congrArg (fun z : Bank => z.val) h; dsimp [loc,old,GaussFetchedArithmetic.lower,fresh] at hv; omega
  target_scratch := by intro h; have hv:=congrArg (fun z : Bank => z.val) h; dsimp [loc,old,GaussFetchedArithmetic.lower,fresh] at hv; omega
  source_machine := by intro i h; have hv:=congrArg (fun z : Bank => z.val) h; dsimp [loc,old,GaussFetchedArithmetic.lower,fresh] at hv; omega
  target_machine := by intro i h; have hv:=congrArg (fun z : Bank => z.val) h; dsimp [loc,old,GaussFetchedArithmetic.lower,fresh] at hv; omega
  scratch_machine := by
    intro i h
    have hv:=congrArg (fun z : Bank => z.val) h
    dsimp [fresh] at hv
    have hi : i.val<8 := by
      simpa only [V2FieldContext.eight_stacks] using i.isLt
    omega

inductive ClearLabel where | clear | done deriving DecidableEq,Fintype
abbrev ClearControl := Unit × Option Bool
noncomputable def clearProgram (source : Bank) :
    ClearLabel → TM2.Stmt (fun _ : Bank => Bool) ClearLabel ClearControl
  | .clear => BitMachineClearBank.clearStep source .clear .done
  | .done => .halt

theorem clear_run (source : Bank) (S : Bank → List Bool) :
    ((advance (clearProgram source))^[(S source).length+2])
      (⟨some .clear,((),none),S⟩ : TM2.Cfg (fun _ : Bank => Bool) _ _) =
      ⟨none,((),none),Function.update S source []⟩ := by
  have h:=BitMachineClearBank.clear_one_run (clearProgram source) source .clear .done rfl () S
  rw [show (S source).length+2=((S source).length+1)+1 by omega,
    Function.iterate_succ_apply',h]
  rfl

noncomputable def p01 := BitMachineRawSequence.program
  (ExactParameterBranchInstall.copyProgram copySlots) (clearProgram (loc 29))
  .clear none ((),none)
noncomputable def p012 := BitMachineRawSequence.program p01
  (MachineInvokeFull.program slots) (MachineInvokeFull.start slots)
  (none,((),none)) (MachineInvokeFull.control slots)
noncomputable def program := BitMachineRawSequence.program p012
  (clearProgram (loc 28)) .clear
  ((none,((),none)),MachineInvokeFull.control slots) ((),none)

abbrev Label := BitMachineRawSequence.Label
  (BitMachineRawSequence.Label
    (BitMachineRawSequence.Label BitMachineCopy.Label ClearLabel)
    (MachineInvokeFull.LabelFull W)) ClearLabel
abbrev Control := BitMachineRawSequence.Control
  (BitMachineRawSequence.Control
    (BitMachineRawSequence.Control (Option Bool) ClearControl)
    (MachineInvokeFull.ControlFull W)) ClearControl

noncomputable def start : Label := BitMachineRawSequence.leftLabel
  (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel .scan))
noncomputable def control : Control :=
  (((none,((),none)),MachineInvokeFull.control slots),((),none))

/-- The raw cell answer is physically copied to28, framed by the fixed
length-and-payload writer in ten fresh banks, and replaced by its V2 field.
Every other stack is restored exactly. -/
theorem physical_frame (S : Bank → List Bool) (word : List Bool)
    (h29 : S (loc 29)=word) (h28 : S (loc 28)=[])
    (hblank : ∀ i : Fin 10,S (fresh i)=[]) :
    ∃ t ≤ 4*word.length+V2FieldContext.clock word+9,
      ((advance program)^[t])
        (⟨some start,control,S⟩ : TM2.Cfg (fun _ : Bank => Bool) Label Control) =
        ⟨none,control,Function.update S (loc 29) (V2FieldContext.field word)⟩ := by
  have hne : loc 29≠loc 28 := by intro h; have hv:=congrArg (fun z : Bank => z.val) h; change (29 : Nat)=28 at hv; omega
  let S1:=Function.update S (loc 28) word
  let S2:=Function.update S1 (loc 29) []
  let S3:=Function.update S2 (loc 29) (V2FieldContext.field word)
  have hword1 : S1 (loc 29)=word := by simp [S1,hne,h29]
  have hsource2 : S2 slots.source=word := by simp [S2,S1,slots,Ne.symm hne]
  have htarget2 : S2 slots.target=[] := by simp [S2,slots]
  have hfresh (a : Fin 10) : fresh a≠loc 28 ∧ fresh a≠loc 29 := by
    constructor <;> intro h <;> have hv:=congrArg (fun z : Bank => z.val) h
    all_goals dsimp [fresh,loc,old,GaussFetchedArithmetic.lower] at hv; omega
  have hS2fresh (a : Fin 10) : S2 (fresh a)=[] := by
    simp [S2,S1,(hfresh a).1,(hfresh a).2,hblank]
  obtain ⟨a,ha,hcopy⟩ := ExactParameterBranchInstall.copy_run copySlots S word
    (by simpa [copySlots] using h29) (by simpa [copySlots] using h28)
    (by simpa [copySlots] using hblank 9)
  have hclear29 : ((advance (clearProgram (loc 29)))^[word.length+2])
      (⟨some .clear,((),none),S1⟩ : TM2.Cfg (fun _ : Bank => Bool) _ _) =
      ⟨none,((),none),S2⟩ := by
    simpa only [hword1] using clear_run (loc 29) S1
  have hW : W.OutputsWithin word (V2FieldContext.field word)
      ((UnaryBinaryEncoding.coefficient+7)*(word.length+1)^2) := by
    simpa only [V2FieldContext.field,SourceListMachineWriter.result,
      Bool.true_eq_false,↓reduceIte] using SourceListMachineWriter.outputs true word
  obtain ⟨b,hb,hframe⟩ := MachineInvokeFull.invoke_run_uniform slots S2 word
    (V2FieldContext.field word) _ hsource2 htarget2 (hS2fresh 8)
    (by
      intro i
      have hi : i.val<8 := by
        simpa only [V2FieldContext.eight_stacks] using i.isLt
      exact hS2fresh ⟨i.val,by omega⟩) hW
  have hS3source : S3 (loc 28)=word := by simp [S3,S2,S1,Ne.symm hne]
  have hfinal : Function.update S3 (loc 28) []=
      Function.update S (loc 29) (V2FieldContext.field word) := by
    funext z
    by_cases hz28 : z=loc 28
    · subst z; simp [S3,S2,S1,Ne.symm hne,h28]
    by_cases hz29 : z=loc 29
    · subst z; simp [S3,S2,S1,hne]
    simp [S3,S2,S1,hz28,hz29]
  have hclear28 : ((advance (clearProgram (loc 28)))^[word.length+2])
      (⟨some .clear,((),none),S3⟩ : TM2.Cfg (fun _ : Bank => Bool) _ _) =
      ⟨none,((),none),Function.update S (loc 29) (V2FieldContext.field word)⟩ := by
    have h:=clear_run (loc 28) S3
    rw [hS3source,hfinal] at h
    exact h
  obtain ⟨u,hu,h01⟩ := BitMachineRawSequence.runs
    (ExactParameterBranchInstall.copyProgram copySlots) (clearProgram (loc 29))
    .scan .clear none none ((),none) ((),none) S S1 S2 a (word.length+2) hcopy hclear29
  obtain ⟨v,hv,h012⟩ := BitMachineRawSequence.runs p01 (MachineInvokeFull.program slots)
    (BitMachineRawSequence.leftLabel .scan) (MachineInvokeFull.start slots)
    (none,((),none)) (none,((),none)) (MachineInvokeFull.control slots)
    (MachineInvokeFull.control slots) S S2 S3 u b h01 hframe
  obtain ⟨t,ht,hfull⟩ := BitMachineRawSequence.runs p012 (clearProgram (loc 28))
    (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel .scan)) .clear
    ((none,((),none)),MachineInvokeFull.control slots)
    ((none,((),none)),MachineInvokeFull.control slots) ((),none) ((),none)
    S S3 (Function.update S (loc 29) (V2FieldContext.field word)) v (word.length+2) h012 hclear28
  have hb' : b ≤ V2FieldContext.clock word := hb
  exact ⟨t,by omega,hfull⟩

#print axioms physical_frame
end CurrentAdditive.GaussCellFieldFrame
