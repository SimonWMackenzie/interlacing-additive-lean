import CurrentAdditive.MachineInvokeFull
import EthInapproximability.CurrentPaper.BitMachineInline

namespace CurrentAdditive.OrdinaryBitBranch
noncomputable section
set_option maxRecDepth 16384
set_option maxHeartbeats 6000000
set_option synthInstance.maxSize 16384
open Turing EthInapproximability.CurrentPaper BitMachineEncoding
open MinimumRatioContext

variable (G A B : BitMachine.Machine)

def selected (b : Bool) : BitMachine.Machine := if b then B else A
abbrev N := G.stackCount+A.stackCount+B.stackCount
abbrev Bank := MachineInvokeCore.StackN (N G A B)

def low : Fin 32 ↪ Bank G A B := ⟨fun i => ⟨i.val,by have h:=i.isLt; omega⟩,by
  intro a b h; exact Fin.ext (congrArg (fun z : Bank G A B => z.val) h)⟩

def slots (M : BitMachine.Machine) (offset : Nat)
    (hoffset : offset+M.stackCount ≤ N G A B) (target : Fin 32)
    (ht0 : target ≠ 0) (ht31 : target ≠ 31) : MachineInvokeCore.Slots M (N G A B) where
  machine := ⟨fun i => ⟨32+offset+i.val,by have hi:=i.isLt; omega⟩,by
    intro a b h; apply Fin.ext; have hv:=congrArg Fin.val h; dsimp at hv; omega⟩
  source := low G A B 0
  target := low G A B target
  scratch := low G A B 31
  source_target := by intro h; exact ht0 ((low G A B).injective h).symm
  source_scratch := by intro h; have hv:=congrArg Fin.val h; change (0:Nat)=31 at hv; omega
  target_scratch := by intro h; exact ht31 ((low G A B).injective h)
  source_machine := by intro i h; have hv:=congrArg Fin.val h; change 0=32+offset+i.val at hv; omega
  target_machine := by
    intro i h; have hv:=congrArg Fin.val h
    change target.val=32+offset+i.val at hv
    have ht:=target.isLt
    omega
  scratch_machine := by intro i h; have hv:=congrArg Fin.val h; change 31=32+offset+i.val at hv; omega

def guardSlots : MachineInvokeCore.Slots G (N G A B) :=
  slots G A B G 0 (by dsimp only [N]; omega) 1 (by decide) (by decide)
def branchSlots (b : Bool) : MachineInvokeCore.Slots (selected A B b) (N G A B) :=
  slots G A B (selected A B b) (if b then G.stackCount+A.stackCount else G.stackCount)
    (by cases b <;> simp [selected,N] <;> omega) 2 (by decide) (by decide)

inductive Label where
  | guard (l : MachineInvokeFull.LabelFull G)
  | choose
  | branch (b : Bool) (l : MachineInvokeFull.LabelFull (selected A B b))
  deriving Fintype

abbrev Control := MachineInvokeFull.ControlFull G ×
  ((b : Bool) → MachineInvokeFull.ControlFull (selected A B b)) × Option Bool

def branchControls (b : Bool) := MachineInvokeFull.control (branchSlots G A B b)
def control : Control G A B := (MachineInvokeFull.control (guardSlots G A B),branchControls G A B,none)
def eGuard (v : MachineInvokeFull.ControlFull G) : Control G A B := (v,branchControls G A B,none)
def eBranch (b : Bool) (v : MachineInvokeFull.ControlFull (selected A B b)) : Control G A B :=
  (MachineInvokeFull.control (guardSlots G A B),Function.update (branchControls G A B) b v,none)
def readBranch (b : Bool) (v : Control G A B) := v.2.1 b
def setFlag (v : Control G A B) (flag : Option Bool) : Control G A B := (v.1,v.2.1,flag)

theorem eBranch_initial (b : Bool) :
    eBranch G A B b (MachineInvokeFull.control (branchSlots G A B b))=control G A B := by
  have hf : Function.update (branchControls G A B) b (branchControls G A B b)=branchControls G A B := by
    funext j
    by_cases h : j=b
    · subst j; simp
    · simp [Function.update_of_ne h]
  change (MachineInvokeFull.control (guardSlots G A B),
    Function.update (branchControls G A B) b (branchControls G A B b),none)=_
  rw [hf]
  rfl

def program : Label G A B → TM2.Stmt (fun _ : Bank G A B => Bool) (Label G A B) (Control G A B)
  | .guard l => BitMachineInline.stmt Label.guard (eGuard G A B) Prod.fst (some .choose)
      (MachineInvokeFull.program (guardSlots G A B) l)
  | .choose => .peek (low G A B 1) (setFlag G A B)
      (.branch (fun v => v.2.2.getD false)
        (.load (fun _ => control G A B) (.goto (fun _ => .branch true (MachineInvokeFull.start (branchSlots G A B true)))))
        (.load (fun _ => control G A B) (.goto (fun _ => .branch false (MachineInvokeFull.start (branchSlots G A B false))))))
  | .branch b l => BitMachineInline.stmt (Label.branch b) (eBranch G A B b) (readBranch G A B b) none
      (MachineInvokeFull.program (branchSlots G A B b) l)

def start : Label G A B := .guard (MachineInvokeFull.start (guardSlots G A B))
def machine : BitMachine.Machine := ofFinite (low G A B 0) (low G A B 2)
  (start G A B) (control G A B) (program G A B)
abbrev Config := TM2.Cfg (fun _ : Bank G A B => Bool) (Label G A B) (Control G A B)
def run (t : Nat) (c : Config G A B) := ((advance (program G A B))^[t]) c
def initialBank (x : List Bool) : Bank G A B → List Bool := fun j => if j=low G A B 0 then x else []
def invocationBound (M : BitMachine.Machine) (n t : Nat) :=
  MachineInvokeFull.uniformBound M (List.replicate n true) t

theorem choose_step (b : Bool) (S : Bank G A B → List Bool) (h : S (low G A B 1)=[b]) :
    run G A B 1 ⟨some .choose,control G A B,S⟩=
      ⟨some (.branch b (MachineInvokeFull.start (branchSlots G A B b))),control G A B,S⟩ := by
  cases b <;> simp [run,Function.iterate_one,advance,program,TM2.step,TM2.stepAux,h,setFlag]

/-- The guard runs on the original word and physically selects exactly one
of two fixed programs. All invocation scratch stacks are cleared; the other
branch is not required to halt on this input. -/
theorem outputsWithin (x y : List Bool) (b : Bool) (tg tp : Nat)
    (hg : G.OutputsWithin x [b] tg)
    (hp : (selected A B b).OutputsWithin x y tp) :
    (machine G A B).OutputsWithin x y
      (invocationBound G x.length tg+invocationBound (selected A B b) x.length tp+1) := by
  let S:=initialBank G A B x
  let S1:=Function.update S (low G A B 1) [b]
  let S2:=Function.update S1 (low G A B 2) y
  obtain ⟨a,ha,hga⟩:=MachineInvokeFull.invoke_run_uniform (guardSlots G A B) S x [b] tg
    rfl (by simp [S,initialBank,guardSlots,slots,low,Fin.ext_iff])
    (by simp [S,initialBank,guardSlots,slots,low,Fin.ext_iff])
    (by intro j; simp [S,initialBank,guardSlots,slots,low,Fin.ext_iff]) hg
  obtain ⟨a',ha',hga'⟩:=BitMachineInline.outputs Label.guard (eGuard G A B) Prod.fst
    (fun _ => rfl) (some .choose) (MachineInvokeFull.program (guardSlots G A B))
    (program G A B) (fun _ => rfl)
    (⟨some (MachineInvokeFull.start (guardSlots G A B)),MachineInvokeFull.control (guardSlots G A B),S⟩)
    a (by rw [hga])
  rw [hga] at hga'
  simp only [BitMachineInline.cfg] at hga'
  change run G A B a' (rawInit (low G A B 0) (start G A B) (control G A B) x)=
    ⟨some .choose,control G A B,S1⟩ at hga'
  have hchoice:=choose_step G A B b S1 (by simp [S1])
  obtain ⟨c,hc,hpc⟩:=MachineInvokeFull.invoke_run_uniform (branchSlots G A B b) S1 x y tp
    (by simp [S1,S,initialBank,branchSlots,slots,low,Fin.ext_iff])
    (by simp [S1,S,initialBank,branchSlots,slots,low,Fin.ext_iff])
    (by simp [S1,S,initialBank,branchSlots,slots,low,Fin.ext_iff])
    (by
      intro j
      have hj1 : (branchSlots G A B b).machine j ≠ low G A B 1 := by
        intro h
        have hv:=congrArg Fin.val h
        change 32+(if b then G.stackCount+A.stackCount else G.stackCount)+j.val=1 at hv
        omega
      have hj0 : (branchSlots G A B b).machine j ≠ low G A B 0 :=
        Ne.symm ((branchSlots G A B b).source_machine j)
      dsimp only [S1]
      rw [Function.update_of_ne hj1]
      change (if (branchSlots G A B b).machine j=low G A B 0 then x else [])=[]
      rw [if_neg hj0]) hp
  obtain ⟨c',hc',hpc'⟩:=BitMachineInline.outputs (Label.branch b) (eBranch G A B b) (readBranch G A B b)
    (fun _ => by simp [readBranch,eBranch]) none (MachineInvokeFull.program (branchSlots G A B b))
    (program G A B) (fun _ => rfl)
    (⟨some (MachineInvokeFull.start (branchSlots G A B b)),MachineInvokeFull.control (branchSlots G A B b),S1⟩)
    c (by rw [hpc])
  rw [hpc] at hpc'
  simp only [BitMachineInline.cfg,eBranch_initial] at hpc'
  have hfull : run G A B (a'+1+c') (rawInit (low G A B 0) (start G A B) (control G A B) x)=
      ⟨none,control G A B,S2⟩ := by
    dsimp only [run] at hga' hchoice ⊢
    rw [show a'+1+c'=c'+(1+a') by omega,Function.iterate_add_apply,
      Function.iterate_add_apply,hga',hchoice]
    exact hpc'
  have ha'' : a ≤ invocationBound G x.length tg := by
    simpa only [invocationBound,MachineInvokeFull.uniformBound,List.length_replicate] using ha
  have hc'' : c ≤ invocationBound (selected A B b) x.length tp := by
    simpa only [invocationBound,MachineInvokeFull.uniformBound,List.length_replicate] using hc
  apply outputsWithin_of_raw_run (low G A B 0) (low G A B 2) (start G A B) (control G A B)
    (program G A B) x y (a'+1+c') _ (by omega)
  · exact congrArg TM2.Cfg.l hfull
  · have h:=congrArg (fun z : Config G A B => z.stk (low G A B 2)) hfull
    simpa only [S2,Function.update_self] using h

#print axioms outputsWithin
end
end CurrentAdditive.OrdinaryBitBranch
