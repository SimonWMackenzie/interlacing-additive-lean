import CurrentAdditive.RatioListPreparation
import CurrentAdditive.RatioCanonicalPairs

set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
noncomputable section
namespace CurrentAdditive.RatioListFullRun
open Turing EthInapproximability.CurrentPaper BitMachineEncoding
open MinimumRatioCallbackLayout CurrentAdditive.GaussListContext

theorem prepare (xs : List (List Bool)) (context lambda : List Bool) :
    ∃ t ≤ RatioListPreparation.clock xs,
      ((advance RatioListPreparation.program)^[t])
        (⟨some RatioListPreparation.start,RatioListPreparation.control,
          RatioRequestFrame.boundary (SourceListEncoding.encode xs) [] context lambda 0 0⟩ :
          TM2.Cfg (fun _ : Stack => Bool) _ _) =
        ⟨none,RatioListPreparation.control,
          RatioRequestFrame.boundary (SourceListEncoding.encode xs)
            (EncodedCommunication.natField xs.length) context lambda 0 xs.length⟩ := by
  let S := RatioRequestFrame.boundary (SourceListEncoding.encode xs) [] context lambda 0 0
  have hb (j : Fin 32) (h8 : j ≠ 8) (h12 : j ≠ 12) (h25 : j ≠ 25) : S (low j) = [] := by
    have h8v : j.val ≠ 8 := by intro he; apply h8; apply Fin.ext; exact he
    have h12v : j.val ≠ 12 := by intro he; apply h12; apply Fin.ext; exact he
    have h25v : j.val ≠ 25 := by intro he; apply h25; apply Fin.ext; exact he
    simp [S,RatioRequestFrame.boundary,RatioPhysicalFold.boundary,
      StatefulListScheduler.initialBank,RatioPhysicalFold.blank,Function.update_apply,
      low,Fin.ext_iff,Fin.ofNat,h8v,h12v,h25v]
  obtain ⟨t,ht,hr⟩ := RatioListPreparation.outputs S xs
    (by simp [S,RatioRequestFrame.boundary,RatioPhysicalFold.boundary,
      StatefulListScheduler.initialBank,Function.update_apply,low,Fin.ext_iff,Fin.ofNat])
    (hb 9 (by decide) (by decide) (by decide))
    (hb 13 (by decide) (by decide) (by decide))
    (hb 31 (by decide) (by decide) (by decide)) (by
      intro i
      fin_cases i <;> apply hb <;> decide)
  refine ⟨t,ht,?_⟩
  have he : Function.update (Function.update S (low 13) (List.replicate xs.length true))
      (low 9) (EncodedCommunication.natField xs.length) =
      RatioRequestFrame.boundary (SourceListEncoding.encode xs)
        (EncodedCommunication.natField xs.length) context lambda 0 xs.length := by
    funext j
    simp [S,RatioRequestFrame.boundary,RatioPhysicalFold.boundary,
      StatefulListScheduler.initialBank,Function.update_apply,low,Fin.ext_iff,Fin.ofNat]
    split_ifs <;> simp_all
  simpa only [he,S] using hr

def requestStart := (some (.inr (.inr .check)) :
  Option (StatefulListScheduler.Label RatioUpdateAppendItem.Label))
def requestControl := StatefulListScheduler.getterControl RatioUpdateAppendItem.control
  (CylinderContextScanStep.copyControl ((),none))
def requestProgram := BitMachineRawSequence.program RatioListPreparation.program
  RatioRequestList.program (.inr (.inr .check)) RatioListPreparation.control requestControl
abbrev RequestLabel := BitMachineRawSequence.Label RatioListPreparation.Label
  (StatefulListScheduler.Label RatioUpdateAppendItem.Label)
def requestFullStart : RequestLabel := BitMachineRawSequence.leftLabel RatioListPreparation.start
def requestFullControl := (RatioListPreparation.control,requestControl)

/-- The request-list producer now starts with just the original ordered
records, their coefficient list, and the scalar. It computes its own header
and unary loop count in the same charged physical run. -/
theorem requests (xs coeff : List (List Bool)) (lambda : List Bool)
    (hlen : coeff.length=xs.length) :
    ∃ t ≤ RatioListPreparation.clock xs + RatioRequestList.clock xs coeff lambda hlen+1,
      ∃ v,
      ((advance requestProgram)^[t])
        (⟨some requestFullStart,requestFullControl,
          RatioRequestFrame.boundary (SourceListEncoding.encode xs) []
            (SourceListEncoding.encode coeff) lambda 0 0⟩ : TM2.Cfg (fun _ : Stack => Bool) _ _) =
        ⟨none,v,RatioRequestFrame.boundary (SourceListEncoding.encode xs)
          (SourceListEncoding.encode (RatioRequestListSpec.requests xs coeff lambda))
          (SourceListEncoding.encode coeff) lambda xs.length 0⟩ := by
  obtain ⟨a,ha,hrA⟩ := prepare xs (SourceListEncoding.encode coeff) lambda
  obtain ⟨b,hb,v,hrB⟩ := RatioRequestList.runs xs coeff lambda hlen
  obtain ⟨t,ht,hr⟩ := BitMachineRawSequence.runs RatioListPreparation.program
    RatioRequestList.program RatioListPreparation.start (.inr (.inr .check))
    RatioListPreparation.control RatioListPreparation.control requestControl v _ _ _ a b hrA hrB
  exact ⟨t,by omega,_,by simpa only [requestProgram,requestFullStart,requestFullControl] using hr⟩

def pairControl := StatefulListScheduler.getterControl RatioPairItem.control
  (CylinderContextScanStep.copyControl ((),none))
def pairProgram := BitMachineRawSequence.program RatioListPreparation.program
  RatioPairList.program (.inr (.inr .check)) RatioListPreparation.control pairControl
abbrev PairLabel := BitMachineRawSequence.Label RatioListPreparation.Label
  (StatefulListScheduler.Label RatioPairItem.Label)
def pairFullStart : PairLabel := BitMachineRawSequence.leftLabel RatioListPreparation.start
def pairFullControl := (RatioListPreparation.control,pairControl)

theorem pairs (xs coeff : List (List Bool)) (hlen : coeff.length=xs.length) :
    ∃ t ≤ RatioListPreparation.clock xs + RatioPairList.clock xs coeff hlen+1,
      ∃ v,
      ((advance pairProgram)^[t])
        (⟨some pairFullStart,pairFullControl,
          RatioRequestFrame.boundary (SourceListEncoding.encode xs) []
            (SourceListEncoding.encode coeff) [] 0 0⟩ : TM2.Cfg (fun _ : Stack => Bool) _ _) =
        ⟨none,v,RatioRequestFrame.boundary (SourceListEncoding.encode xs)
          (SourceListEncoding.encode (RatioPairListSpec.pairs xs coeff))
          (SourceListEncoding.encode coeff) [] xs.length 0⟩ := by
  obtain ⟨a,ha,hrA⟩ := prepare xs (SourceListEncoding.encode coeff) []
  obtain ⟨b,hb,v,hrB⟩ := RatioPairList.runs xs coeff hlen
  obtain ⟨t,ht,hr⟩ := BitMachineRawSequence.runs RatioListPreparation.program
    RatioPairList.program RatioListPreparation.start (.inr (.inr .check))
    RatioListPreparation.control RatioListPreparation.control pairControl v _ _ _ a b hrA hrB
  exact ⟨t,by omega,_,by simpa only [pairProgram,pairFullStart,pairFullControl] using hr⟩

#print axioms prepare
#print axioms requests
#print axioms pairs
end CurrentAdditive.RatioListFullRun
