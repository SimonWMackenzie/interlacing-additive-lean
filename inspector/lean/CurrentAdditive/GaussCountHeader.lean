import CurrentAdditive.GaussCellFieldFrame

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

namespace CurrentAdditive.GaussCountHeader
open Turing EthInapproximability.CurrentPaper BitMachineEncoding
open CurrentAdditive.MinimumRatioContext GaussCellFieldFrame

noncomputable abbrev W := SourceListMachineWriter.framingMachine false

theorem eight_stacks : W.stackCount=8 := rfl

noncomputable def slots : MachineInvokeCore.Slots W (32+GaussFetchedArithmetic.M.stackCount+10) where
  machine := ⟨fun i => fresh ⟨i.val,by
    have hi : i.val<8 := by simpa only [eight_stacks] using i.isLt
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
    have hi : i.val<8 := by simpa only [eight_stacks] using i.isLt
    omega

inductive DrainLabel where | scan | done deriving DecidableEq,Fintype
abbrev DrainControl := Unit × Option Bool
noncomputable def drainProgram : DrainLabel → TM2.Stmt (fun _ : Bank => Bool) DrainLabel DrainControl
  | .scan => BitMachineBroadcast.scanStep (loc 29) (loc 30) .scan .done
  | .done => .halt

noncomputable def program := BitMachineRawSequence.program
  (MachineInvokeFull.program slots) drainProgram .scan
  (MachineInvokeFull.control slots) ((),none)
abbrev Label := BitMachineRawSequence.Label (MachineInvokeFull.LabelFull W) DrainLabel
abbrev Control := BitMachineRawSequence.Control (MachineInvokeFull.ControlFull W) DrainControl
noncomputable def start : Label := BitMachineRawSequence.leftLabel (MachineInvokeFull.start slots)
noncomputable def control : Control := (MachineInvokeFull.control slots,((),none))

noncomputable def clock (k : Nat) : Nat :=
  MachineInvokeFull.uniformBound W (List.replicate k true)
    ((UnaryBinaryEncoding.coefficient+7)*(k+1)^2)+
    (EncodedCommunication.natField k).length+3

/-- A physical unary counter is converted to its canonical binary count header,
then drained in reverse order into an empty buffer. The source and all other
ambient stacks are restored, including the temporary answer and fresh workspace. -/
theorem physical_header (S : Bank → List Bool) (k : Nat)
    (h28 : S (loc 28)=List.replicate k true)
    (h29 : S (loc 29)=[]) (h30 : S (loc 30)=[])
    (hblank : ∀ i : Fin 10,S (fresh i)=[]) :
    ∃ t ≤ clock k,
      ((advance program)^[t])
        (⟨some start,control,S⟩ : TM2.Cfg (fun _ : Bank => Bool) Label Control) =
        ⟨none,control,Function.update S (loc 30) ((EncodedCommunication.natField k).reverse)⟩ := by
  have hne : loc 29≠loc 30 := by
    intro h; have hv:=congrArg (fun z : Bank => z.val) h
    change (29 : Nat)=30 at hv; omega
  have hW : W.OutputsWithin (List.replicate k true) (EncodedCommunication.natField k)
      ((UnaryBinaryEncoding.coefficient+7)*(k+1)^2) := by
    simpa only [SourceListMachineWriter.result,Bool.false_eq_true,↓reduceIte,
      List.length_replicate,List.append_nil] using
      SourceListMachineWriter.outputs false (List.replicate k true)
  obtain ⟨a,ha,hrun⟩ := MachineInvokeFull.invoke_run_uniform slots S
    (List.replicate k true) (EncodedCommunication.natField k) _
    h28 h29 (hblank 8) (by
      intro i
      have hi : i.val<8 := by simpa only [eight_stacks] using i.isLt
      exact hblank ⟨i.val,by omega⟩) hW
  let S1:=Function.update S (loc 29) (EncodedCommunication.natField k)
  have hin : BitMachineBroadcast.contents (loc 29) (loc 30) S1
      (EncodedCommunication.natField k) []=S1 := by
    funext z
    by_cases h : z=loc 30
    · subst z; simp [BitMachineBroadcast.contents,S1,Ne.symm hne,h30]
    by_cases h' : z=loc 29
    · subst z; simp [BitMachineBroadcast.contents,S1,hne]
    simp [BitMachineBroadcast.contents,S1,h,h']
  have hout : BitMachineBroadcast.contents (loc 29) (loc 30) S1 []
      ((EncodedCommunication.natField k).reverse ++ [])=
      Function.update S (loc 30) ((EncodedCommunication.natField k).reverse) := by
    funext z
    by_cases h : z=loc 30
    · subst z; simp [BitMachineBroadcast.contents,S1]
    by_cases h' : z=loc 29
    · subst z; simp [BitMachineBroadcast.contents,S1,hne,h29]
    simp [BitMachineBroadcast.contents,S1,h,h']
  have hscan:=BitMachineBroadcast.scan_run drainProgram (loc 29) (loc 30) hne
    .scan .done rfl () none (EncodedCommunication.natField k) [] S1
  rw [hin,hout] at hscan
  have hdrain : ((advance drainProgram)^[(EncodedCommunication.natField k).length+2])
      (⟨some .scan,((),none),S1⟩ : TM2.Cfg (fun _ : Bank => Bool) DrainLabel DrainControl)=
      ⟨none,((),none),Function.update S (loc 30) ((EncodedCommunication.natField k).reverse)⟩ := by
    rw [show (EncodedCommunication.natField k).length+2=
      ((EncodedCommunication.natField k).length+1)+1 by omega,Function.iterate_succ_apply']
    change advance drainProgram (((advance drainProgram)^[_]) _)=_
    rw [show ((advance drainProgram)^[(EncodedCommunication.natField k).length+1])
      (⟨some DrainLabel.scan,((),none),S1⟩ : TM2.Cfg (fun _ : Bank => Bool) _ _)=_ from hscan]
    rfl
  obtain ⟨t,ht,hfull⟩ := BitMachineRawSequence.runs
    (MachineInvokeFull.program slots) drainProgram
    (MachineInvokeFull.start slots) .scan
    (MachineInvokeFull.control slots) (MachineInvokeFull.control slots)
    ((),none) ((),none) S S1
    (Function.update S (loc 30) ((EncodedCommunication.natField k).reverse))
    a ((EncodedCommunication.natField k).length+2) hrun hdrain
  exact ⟨t,by unfold clock; omega,hfull⟩

#print axioms physical_header
end CurrentAdditive.GaussCountHeader
