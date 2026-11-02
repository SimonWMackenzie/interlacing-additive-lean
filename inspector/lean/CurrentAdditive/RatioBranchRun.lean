import CurrentAdditive.RatioBranchLayout

set_option maxHeartbeats 3000000
set_option maxRecDepth 10000
set_option maxSynthPendingDepth 100
noncomputable section
namespace CurrentAdditive.RatioBranchRun
open Turing EthInapproximability.CurrentPaper BitMachineEncoding
open MinimumRatioCallbackLayout MinimumRatioContext RatioCanonicalRequests RatioBranchLayout

def minCoefficient := Classical.choose RatioMinimumMachine.uniform_outputs
def minExponent := Classical.choose (Classical.choose_spec RatioMinimumMachine.uniform_outputs)
theorem minimum_outputs (xs : List (List Bool)) :
    MinM.OutputsWithin (SourceListEncoding.encode xs) (xs.foldl MinimumRatioStepSpec.step [])
      (minCoefficient*((SourceListEncoding.encode xs).length+1)^minExponent) :=
  Classical.choose_spec (Classical.choose_spec RatioMinimumMachine.uniform_outputs) xs

def packet {q : Nat} (source : Array ((Fin q → Nat) × ℚ)) (coeff : Array ℚ) :=
  SourceListEncoding.encode (RatioPairListSpec.pairs (records source) (coeffWords coeff))
def initialBank {q : Nat} (source : Array ((Fin q → Nat) × ℚ)) (coeff : Array ℚ) :=
  RatioRequestFrame.boundary (SourceListEncoding.encode (records source)) []
    (SourceListEncoding.encode (coeffWords coeff)) [] 0 0
def pairBank {q : Nat} (source : Array ((Fin q → Nat) × ℚ)) (coeff : Array ℚ) :=
  RatioRequestFrame.boundary (SourceListEncoding.encode (records source)) (packet source coeff)
    (SourceListEncoding.encode (coeffWords coeff)) [] source.size 0
def minBank {q : Nat} (source : Array ((Fin q → Nat) × ℚ)) (coeff : Array ℚ) (lambda : ℚ) :=
  RatioRequestFrame.boundary (SourceListEncoding.encode (records source)) (packet source coeff)
    (SourceListEncoding.encode (coeffWords coeff)) (true :: ratWord lambda) source.size 0
def requestBank {q : Nat} (source : Array ((Fin q → Nat) × ℚ)) (coeff : Array ℚ) (lambda : ℚ) :=
  RatioRequestFrame.boundary (SourceListEncoding.encode (records source)) []
    (SourceListEncoding.encode (coeffWords coeff)) (ratWord lambda) 0 0
def finalBank {q : Nat} (source : Array ((Fin q → Nat) × ℚ)) (coeff : Array ℚ) (lambda : ℚ) :=
  RatioRequestFrame.boundary (SourceListEncoding.encode (records source))
    (CodeDUpdateRequestABI.requestPacketList source coeff lambda)
    (SourceListEncoding.encode (coeffWords coeff)) (ratWord lambda) source.size 0

def pairClock {q : Nat} (source : Array ((Fin q → Nat) × ℚ)) (coeff : Array ℚ)
    (hsize : coeff.size=source.size) := RatioListPreparation.clock (records source)+
  RatioPairList.clock (records source) (coeffWords coeff) (by simpa [records,coeffWords] using hsize)+1
def minClock {q : Nat} (source : Array ((Fin q → Nat) × ℚ)) (coeff : Array ℚ) :=
  MachineInvokeFull.uniformBound MinM (packet source coeff)
    (minCoefficient*((packet source coeff).length+1)^minExponent)
def resetClock {q : Nat} (source : Array ((Fin q → Nat) × ℚ)) (coeff : Array ℚ) :=
  2*(packet source coeff).length+2*source.size+9
def updateClock {q : Nat} (source : Array ((Fin q → Nat) × ℚ)) (coeff : Array ℚ)
    (lambda : ℚ) (hsize : coeff.size=source.size) :=
  RatioListPreparation.clock (records source)+
  RatioRequestList.clock (records source) (coeffWords coeff) (ratWord lambda)
    (by simpa [records,coeffWords] using hsize)+1+
  MachineInvokeFull.uniformBound CodeDUpdateFullPipeline.machine
    (CodeDUpdateRequestABI.requestPacketList source coeff lambda)
    (CodeDUpdateFullPipeline.clock source coeff lambda)+1
def clock {q : Nat} (source : Array ((Fin q → Nat) × ℚ)) (coeff : Array ℚ)
    (lambda : ℚ) (hsize : coeff.size=source.size) :=
  pairClock source coeff hsize+minClock source coeff+resetClock source coeff+
    updateClock source coeff lambda hsize+3

theorem branch_run {q : Nat} (source : Array ((Fin q → Nat) × ℚ))
    (coeff : Array ℚ) (lambda : ℚ) (hsize : coeff.size=source.size)
    (hmin : SequentialCode.minimumRatio (source.map Prod.snd) coeff = some lambda)
    (hnonneg : (CodeDUpdatedArithmeticABI.candidateWeights source coeff lambda).all
      (fun w => decide (0 ≤ w)) = true) :
    ∃ t ≤ clock source coeff lambda hsize, ∃ v,
      ((advance program)^[t])
        (⟨some start,control,frame (initialBank source coeff)⟩ : TM2.Cfg (fun _ : BigStack => Bool) _ _) =
        ⟨none,v,Function.update (frame (finalBank source coeff lambda)) (core (low 24))
          (CodeDCanonicalSourceV2.encodedSource (CodeDCompactSequentialBridge.retainedSource source
            (CodeDUpdatedArithmeticABI.candidateWeights source coeff lambda)))⟩ := by
  obtain ⟨a,ha,va,hrA⟩ := RatioListFullRun.pairs (records source) (coeffWords coeff)
    (by simpa [records,coeffWords] using hsize)
  have hrA' := BitMachineStackRun.run core (fun _ => []) RatioListFullRun.pairProgram
    (⟨some RatioListFullRun.pairFullStart,RatioListFullRun.pairFullControl,initialBank source coeff⟩ :
      TM2.Cfg (fun _ : Stack => Bool) _ _) a
  have hrA0 : ((advance RatioListFullRun.pairProgram)^[a])
      (⟨some RatioListFullRun.pairFullStart,RatioListFullRun.pairFullControl,initialBank source coeff⟩ :
        TM2.Cfg (fun _ : Stack => Bool) _ _) = ⟨none,va,pairBank source coeff⟩ := by
    simpa [initialBank,pairBank,packet,records] using hrA
  rw [hrA0] at hrA'
  have hsource : frame (pairBank source coeff) minSlots.source = packet source coeff := by
    rw [frame,minSlots,BitMachineStackEmbedding.bank_at]
    simp [pairBank,RatioRequestFrame.boundary,RatioPhysicalFold.boundary,
      StatefulListScheduler.initialBank,Function.update_apply,low,Fin.ext_iff,Fin.ofNat]
  have hb (j : Fin 32) (hj : 15 ≤ j.val) (h25 : j ≠ 25) :
      pairBank source coeff (low j) = [] := by
    have h25v : j.val ≠ 25 := by intro he; apply h25; apply Fin.ext; exact he
    simp [pairBank,RatioRequestFrame.boundary,RatioPhysicalFold.boundary,
      StatefulListScheduler.initialBank,RatioPhysicalFold.blank,
      Function.update_apply,low,Fin.ext_iff,Fin.ofNat,h25v]
    split_ifs <;> simp_all <;> omega
  have htarget : frame (pairBank source coeff) minSlots.target = [] := by
    rw [frame,minSlots,BitMachineStackEmbedding.bank_at]
    simp [pairBank,RatioRequestFrame.boundary]
  have hscratch : frame (pairBank source coeff) minSlots.scratch = [] := by
    rw [frame,minSlots,BitMachineStackEmbedding.bank_at]
    exact hb 31 (by decide) (by decide)
  have hblank : ∀ i,frame (pairBank source coeff) (minSlots.machine i) = [] := by
    intro i
    apply BitMachineStackEmbedding.bank_outside
    intro he
    obtain ⟨j,hj⟩ := he
    have hv := congrArg (fun k : BigStack => k.val) hj
    change j.val=32+RatioRequestUpdateRun.N+i.val at hv
    have hjlt := j.isLt
    unfold RatioRequestUpdateRun.N at hv
    omega
  have hM := minimum_outputs (RatioPairListSpec.pairs (records source) (coeffWords coeff))
  rw [RatioCanonicalPairs.pairs_exact source coeff hsize,
    RatioMinimumMachine.canonical_fold,hmin] at hM
  obtain ⟨b,hbtime,hrB⟩ := MachineInvokeFull.invoke_run_uniform minSlots
    (frame (pairBank source coeff)) (packet source coeff)
    (MinimumRatioStepSpec.bestPacket (some lambda))
    (minCoefficient*((packet source coeff).length+1)^minExponent)
    hsource htarget hscratch hblank (by simpa [packet,RatioCanonicalPairs.pairs_exact source coeff hsize] using hM)
  have hminbank : Function.update (frame (pairBank source coeff)) minSlots.target
      (MinimumRatioStepSpec.bestPacket (some lambda)) = frame (minBank source coeff lambda) := by
    change Function.update (frame (pairBank source coeff)) (core (low 25))
      (MinimumRatioStepSpec.bestPacket (some lambda)) = frame (minBank source coeff lambda)
    rw [← frame_update]
    congr 1
    simp [pairBank,minBank,RatioRequestFrame.boundary,Function.update_idem,
      MinimumRatioStepSpec.bestPacket,ratWord,CodeDCanonicalSourceV2.rawOfRat,CodeDCanonicalSource.rawOfRat]
  rw [hminbank] at hrB
  obtain ⟨ab,hab,hrAB⟩ := BitMachineRawSequence.runs pairProgram minimumProgram
    RatioListFullRun.pairFullStart (MachineInvokeFull.start minSlots)
    RatioListFullRun.pairFullControl va (MachineInvokeFull.control minSlots) (MachineInvokeFull.control minSlots)
    _ (frame (pairBank source coeff)) _ a b
    (by simpa only [pairProgram,BitMachineStackEmbedding.stackCfg,frame] using hrA') hrB
  obtain ⟨c,hc,hrC⟩ := RatioBranchReset.outputs (SourceListEncoding.encode (records source))
    (packet source coeff) (SourceListEncoding.encode (coeffWords coeff)) (ratWord lambda) source.size
  have hrC' := BitMachineStackRun.run core (fun _ => []) RatioBranchReset.program
    (⟨some RatioBranchReset.start,RatioBranchReset.control,minBank source coeff lambda⟩ :
      TM2.Cfg (fun _ : Stack => Bool) _ _) c
  have hrC0 : ((advance RatioBranchReset.program)^[c])
      (⟨some RatioBranchReset.start,RatioBranchReset.control,minBank source coeff lambda⟩ :
        TM2.Cfg (fun _ : Stack => Bool) _ _) = ⟨none,RatioBranchReset.control,requestBank source coeff lambda⟩ := hrC
  rw [hrC0] at hrC'
  obtain ⟨abc,habc,hrABC⟩ := BitMachineRawSequence.runs p01 resetProgram s01 RatioBranchReset.start
    c01 c01 RatioBranchReset.control RatioBranchReset.control
    _ (frame (minBank source coeff lambda)) _ ab c
    (by simpa only [p01,s01,c01] using hrAB)
    (by simpa only [resetProgram,BitMachineStackEmbedding.stackCfg,frame] using hrC')
  obtain ⟨d,hd,vd,hrD⟩ := RatioRequestUpdateRun.requests_update source coeff lambda hsize hnonneg
  have hrD' := BitMachineStackRun.run wide (fun _ => []) RatioRequestUpdateRun.program
    (⟨some RatioRequestUpdateRun.start,RatioRequestUpdateRun.control,
      RatioRequestUpdateRun.frame (requestBank source coeff lambda)⟩ :
      TM2.Cfg (fun _ : RatioRequestUpdateRun.WideStack => Bool) _ _) d
  have hrD0 : ((advance RatioRequestUpdateRun.program)^[d])
      (⟨some RatioRequestUpdateRun.start,RatioRequestUpdateRun.control,
        RatioRequestUpdateRun.frame (requestBank source coeff lambda)⟩ :
        TM2.Cfg (fun _ : RatioRequestUpdateRun.WideStack => Bool) _ _) =
      ⟨none,vd,Function.update (RatioRequestUpdateRun.frame (finalBank source coeff lambda))
        RatioRequestUpdateRun.slots.target
        (CodeDCanonicalSourceV2.encodedSource (CodeDCompactSequentialBridge.retainedSource source
          (CodeDUpdatedArithmeticABI.candidateWeights source coeff lambda)))⟩ := hrD
  rw [hrD0] at hrD'
  simp only [BitMachineStackEmbedding.stackCfg,frameWide,BitMachineStackEmbedding.bank_update] at hrD'
  change ((advance updateProgram)^[d])
    ⟨some RatioRequestUpdateRun.start,RatioRequestUpdateRun.control,
      frameWide (RatioRequestUpdateRun.frame (requestBank source coeff lambda))⟩ =
    ⟨none,vd,Function.update (frameWide (RatioRequestUpdateRun.frame (finalBank source coeff lambda)))
      (core (low 24)) _⟩ at hrD'
  rw [frame_compat,frame_compat] at hrD'
  obtain ⟨t,ht,hr⟩ := BitMachineRawSequence.runs p012 updateProgram s012 RatioRequestUpdateRun.start
    c012 c012 RatioRequestUpdateRun.control vd _ _ _ abc d
    (by simpa only [p012,s012,c012] using hrABC) hrD'
  refine ⟨t,?_,_,by simpa only [RatioBranchLayout.program,RatioBranchLayout.start,RatioBranchLayout.control] using hr⟩
  dsimp only [clock,pairClock,minClock,resetClock,updateClock]
  dsimp only [RatioRequestUpdateRun.M] at hd
  omega

#print axioms branch_run
end CurrentAdditive.RatioBranchRun
