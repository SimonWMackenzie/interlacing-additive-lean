import CurrentAdditive.RatioListFullRun
import CurrentAdditive.CodeDUpdateFullPipeline

set_option maxHeartbeats 1500000
set_option maxRecDepth 10000
noncomputable section
namespace CurrentAdditive.RatioRequestUpdateRun
open Turing EthInapproximability.CurrentPaper BitMachineEncoding
open MinimumRatioCallbackLayout MinimumRatioContext RatioCanonicalRequests

abbrev M := CodeDUpdateFullPipeline.machine
def N : Nat := extraCount+M.stackCount
abbrev WideStack := Fin (32+N)
abbrev WideBank := WideStack → List Bool
def embed : Stack ↪ WideStack where
  toFun i := ⟨i.val,by have hi := i.isLt; dsimp [N]; omega⟩
  inj' := by intro a b he; apply Fin.ext; exact congrArg (fun k : WideStack => k.val) he
def high : Fin M.stackCount ↪ WideStack where
  toFun i := ⟨32+extraCount+i.val,by have hi := i.isLt; dsimp [N]; omega⟩
  inj' := by
    intro a b he; apply Fin.ext
    have hv := congrArg Fin.val he
    change 32+extraCount+a.val=32+extraCount+b.val at hv
    omega
def slots : MachineInvokeCore.Slots M N where
  machine := high
  source := embed (low 9)
  target := embed (low 24)
  scratch := embed (low 31)
  source_target := by simp [embed,low,Fin.ext_iff]
  source_scratch := by simp [embed,low,Fin.ext_iff]
  target_scratch := by simp [embed,low,Fin.ext_iff]
  source_machine := by
    intro i he
    have hv := congrArg Fin.val he
    change 9=32+extraCount+i.val at hv; omega
  target_machine := by
    intro i he
    have hv := congrArg Fin.val he
    change 24=32+extraCount+i.val at hv; omega
  scratch_machine := by
    intro i he
    have hv := congrArg Fin.val he
    change 31=32+extraCount+i.val at hv; omega

def frame (S : Bank) : WideBank := BitMachineStackEmbedding.bank embed (fun _ => []) S
def requestProgram l := BitMachineStackEmbedding.stackStmt embed
  (RatioListFullRun.requestProgram l)
def updateProgram := MachineInvokeFull.program slots
def program := BitMachineRawSequence.program requestProgram updateProgram
  (MachineInvokeFull.start slots) RatioListFullRun.requestFullControl (MachineInvokeFull.control slots)
abbrev Label := BitMachineRawSequence.Label RatioListFullRun.RequestLabel
  (MachineInvokeFull.LabelFull M)
def start : Label := BitMachineRawSequence.leftLabel RatioListFullRun.requestFullStart
def control := (RatioListFullRun.requestFullControl,MachineInvokeFull.control slots)

theorem frame_run (c : TM2.Cfg (fun _ : Stack => Bool) _ _) (t : Nat) :
    ((advance requestProgram)^[t])
      (BitMachineStackEmbedding.stackCfg embed (fun _ => []) c) =
    BitMachineStackEmbedding.stackCfg embed (fun _ => [])
      (((advance RatioListFullRun.requestProgram)^[t]) c) := by
  have hs (c : TM2.Cfg (fun _ : Stack => Bool) _ _) :
      advance requestProgram (BitMachineStackEmbedding.stackCfg embed (fun _ => []) c) =
      BitMachineStackEmbedding.stackCfg embed (fun _ => [])
        (advance RatioListFullRun.requestProgram c) := by
    rcases c with ⟨l,v,S⟩
    cases l with
    | none => rfl
    | some l =>
        exact BitMachineStackEmbedding.stack_stepAux embed (fun _ => [])
          (RatioListFullRun.requestProgram l) v S
  induction t with
  | zero => rfl
  | succ t ih => rw [Function.iterate_succ_apply',ih,hs,Function.iterate_succ_apply']

theorem requests_update {q : Nat} (source : Array ((Fin q → Nat) × ℚ))
    (coeff : Array ℚ) (lambda : ℚ) (hsize : coeff.size=source.size)
    (hnonneg : (CodeDUpdatedArithmeticABI.candidateWeights source coeff lambda).all
      (fun w => decide (0 ≤ w)) = true) :
    let xs := records source
    let cs := coeffWords coeff
    let scalar := ratWord lambda
    let old := RatioRequestFrame.boundary (SourceListEncoding.encode xs) []
      (SourceListEncoding.encode cs) scalar 0 0
    let final := RatioRequestFrame.boundary (SourceListEncoding.encode xs)
      (CodeDUpdateRequestABI.requestPacketList source coeff lambda)
      (SourceListEncoding.encode cs) scalar source.size 0
    ∃ t ≤ RatioListPreparation.clock xs + RatioRequestList.clock xs cs scalar
        (by simpa [xs,cs,records,coeffWords] using hsize)+1 +
      MachineInvokeFull.uniformBound M (CodeDUpdateRequestABI.requestPacketList source coeff lambda)
        (CodeDUpdateFullPipeline.clock source coeff lambda)+1,
      ∃ v,
      ((advance program)^[t]) (⟨some start,control,frame old⟩ : TM2.Cfg (fun _ : WideStack => Bool) _ _) =
      ⟨none,v,Function.update (frame final) slots.target
        (CodeDCanonicalSourceV2.encodedSource (CodeDCompactSequentialBridge.retainedSource source
          (CodeDUpdatedArithmeticABI.candidateWeights source coeff lambda)))⟩ := by
  dsimp only
  let final := RatioRequestFrame.boundary (SourceListEncoding.encode (records source))
    (CodeDUpdateRequestABI.requestPacketList source coeff lambda)
    (SourceListEncoding.encode (coeffWords coeff)) (ratWord lambda) source.size 0
  obtain ⟨a,ha,v,hrA⟩ := RatioListFullRun.requests (records source) (coeffWords coeff) (ratWord lambda)
    (by simpa [records,coeffWords] using hsize)
  rw [RatioCanonicalRequests.requests_exact source coeff lambda hsize] at hrA
  have hrA' := frame_run
    (⟨some RatioListFullRun.requestFullStart,RatioListFullRun.requestFullControl,
      RatioRequestFrame.boundary (SourceListEncoding.encode (records source)) []
        (SourceListEncoding.encode (coeffWords coeff)) (ratWord lambda) 0 0⟩ :
      TM2.Cfg (fun _ : Stack => Bool) _ _) a
  rw [hrA] at hrA'
  have hn (j : Fin 32) (hj : 15 ≤ j.val) (h25 : j ≠ 25) : final (low j) = [] := by
    simp [final,RatioRequestFrame.boundary,RatioPhysicalFold.boundary,
      StatefulListScheduler.initialBank,RatioPhysicalFold.blank,
      Function.update_apply,low,Fin.ext_iff,Fin.ofNat]
    split_ifs <;> simp_all <;> omega
  have hsource : frame final slots.source =
      CodeDUpdateRequestABI.requestPacketList source coeff lambda := by
    rw [frame,slots,BitMachineStackEmbedding.bank_at]
    simp [final,RatioRequestFrame.boundary,RatioPhysicalFold.boundary,
      StatefulListScheduler.initialBank,Function.update_apply,low,Fin.ext_iff,Fin.ofNat]
  have htarget : frame final slots.target = [] := by
    rw [frame,slots,BitMachineStackEmbedding.bank_at]
    exact hn 24 (by decide) (by decide)
  have hscratch : frame final slots.scratch = [] := by
    rw [frame,slots,BitMachineStackEmbedding.bank_at]
    exact hn 31 (by decide) (by decide)
  have hblank : ∀ i,frame final (slots.machine i) = [] := by
    intro i
    apply BitMachineStackEmbedding.bank_outside
    intro he
    obtain ⟨j,hj⟩ := he
    have hv := congrArg Fin.val hj
    change j.val=32+extraCount+i.val at hv
    have hlt := j.isLt
    omega
  obtain ⟨b,hb,hrB⟩ := MachineInvokeFull.invoke_run_uniform slots (frame final) _ _ _
    hsource htarget hscratch hblank (CodeDUpdateFullPipeline.outputs source coeff lambda hnonneg)
  obtain ⟨t,ht,hr⟩ := BitMachineRawSequence.runs requestProgram updateProgram
    RatioListFullRun.requestFullStart (MachineInvokeFull.start slots)
    RatioListFullRun.requestFullControl v (MachineInvokeFull.control slots) (MachineInvokeFull.control slots)
    _ (frame final) _ a b (by simpa [BitMachineStackEmbedding.stackCfg,frame,final,
      records,List.length_map,Array.length_toList,CodeDUpdateRequestABI.requestPacketList,
      CodeDCodecV2.encodeItems] using hrA') hrB
  exact ⟨t,by omega,_,by simpa only [program,start,control,final] using hr⟩

#print axioms requests_update
end CurrentAdditive.RatioRequestUpdateRun
