import CurrentAdditive.RatioListFullRun
import EthInapproximability.CurrentPaper.MultiMove

set_option maxHeartbeats 1500000
set_option maxRecDepth 10000
noncomputable section
namespace CurrentAdditive.RatioBranchReset
open Turing EthInapproximability.CurrentPaper BitMachineEncoding MinimumRatioCallbackLayout

def popProgram : Unit → TM2.Stmt (fun _ : Stack => Bool) Unit Unit
  | () => .pop (low 25) (fun _ _ => ()) .halt
def jobs : List (MultiMove.Job Stack) := [⟨low 9,[]⟩,⟨low 10,[]⟩,⟨low 13,[]⟩]
def clearProgram := MultiMove.program jobs (low 31)
abbrev Label := BitMachineRawSequence.Label Unit (MultiMove.Label 3)
def program := BitMachineRawSequence.program popProgram clearProgram
  (MultiMove.startLabel jobs) () MultiMove.initial
def start : Label := BitMachineRawSequence.leftLabel ()
def control := ((),MultiMove.initial)

theorem outputs (source pairPacket context scalar : List Bool) (count : Nat) :
    ∃ t ≤ 2*pairPacket.length+2*count+9,
      ((advance program)^[t])
        (⟨some start,control,RatioRequestFrame.boundary source pairPacket context
          (true :: scalar) count 0⟩ : TM2.Cfg (fun _ : Stack => Bool) _ _) =
        ⟨none,control,RatioRequestFrame.boundary source [] context scalar 0 0⟩ := by
  let S := RatioRequestFrame.boundary source pairPacket context (true :: scalar) count 0
  let S1 := Function.update S (low 25) scalar
  have hne (a b : Fin 32) (h : a ≠ b) : low a ≠ low b := by
    intro he; apply h; apply Fin.ext; exact congrArg (fun k : Stack => k.val) he
  have hrA : ((advance popProgram)^[1]) (⟨some (),(),S⟩ :
      TM2.Cfg (fun _ : Stack => Bool) _ _) = ⟨none,(),S1⟩ := by
    have h25 : S (low 25) = true :: scalar := by simp [S,RatioRequestFrame.boundary]
    change (⟨none,(),Function.update S (low 25) (S (low 25)).tail⟩ :
      TM2.Cfg (fun _ : Stack => Bool) _ _) = ⟨none,(),S1⟩
    rw [h25]
    rfl
  have hvalid : MultiMove.Valid (low 31) jobs := by
    intro j hj
    simp only [jobs,List.mem_cons,List.not_mem_nil,or_false] at hj
    rcases hj with rfl | rfl | rfl
    · exact ⟨hne 9 31 (by decide),by simp,by simp⟩
    · exact ⟨hne 10 31 (by decide),by simp,by simp⟩
    · exact ⟨hne 13 31 (by decide),by simp,by simp⟩
  have h31 : S1 (low 31) = [] := by
    simp [S1,S,RatioRequestFrame.boundary,RatioPhysicalFold.boundary,
      StatefulListScheduler.initialBank,RatioPhysicalFold.blank,
      Function.update_apply,low,Fin.ext_iff,Fin.ofNat]
  have hrB := MultiMove.run jobs (low 31) hvalid S1 h31
  have hcost : MultiMove.cost jobs S1+1=2*pairPacket.length+2*count+7 := by
    simp [MultiMove.cost,MultiMove.step,jobs,BitMachineBroadcast.prepend,S1,S,
      RatioRequestFrame.boundary,RatioPhysicalFold.boundary,StatefulListScheduler.initialBank,
      Function.update_apply,low,Fin.ext_iff,Fin.ofNat]
    omega
  rw [hcost] at hrB
  have hout : MultiMove.apply jobs S1 = RatioRequestFrame.boundary source [] context scalar 0 0 := by
    funext j
    simp [MultiMove.apply,MultiMove.step,jobs,BitMachineBroadcast.prepend,S1,S,
      RatioRequestFrame.boundary,RatioPhysicalFold.boundary,StatefulListScheduler.initialBank,
      Function.update_apply,low,Fin.ext_iff,Fin.ofNat]
    split_ifs <;> simp_all
  rw [hout] at hrB
  obtain ⟨t,ht,hr⟩ := BitMachineRawSequence.runs popProgram clearProgram ()
    (MultiMove.startLabel jobs) () () MultiMove.initial MultiMove.initial S S1 _ 1 _ hrA hrB
  exact ⟨t,by omega,by simpa only [program,start,control,S] using hr⟩

#print axioms outputs
end CurrentAdditive.RatioBranchReset
