import EthInapproximability.CurrentPaper.ETHParameterBinsSourcePreserving
import EthInapproximability.CurrentPaper.ETHParameterScaleActual

/-! The actual six-raw-word scale program followed by an inlined physical
source-preserving bin program. The second program receives the word produced
by the first, not a bank specified by an endpoint premise. -/

namespace EthInapproximability.CurrentPaper.ETHBinsJoinedScratch

open Turing BitMachineEncoding BitMachineStackEmbedding

noncomputable section

set_option maxHeartbeats 1000000

abbrev Stack := ETHScaleActualComplete.Stack ⊕ ETHBinsSourcePreservingScratch.Stack
abbrev Label := BitMachineRawSequence.Label ETHScaleActualComplete.Label ETHBinsSourcePreservingScratch.Label
abbrev Control := ETHScaleActualComplete.Control × ETHBinsSourcePreservingScratch.Control

def scaleEmbed : ETHScaleActualComplete.Stack ↪ Stack :=
  ⟨Sum.inl, by intro a b h; exact Sum.inl_injective h⟩

def binsEmbed : ETHBinsSourcePreservingScratch.Stack ↪ Stack where
  toFun k := if k = ETHBinsSourcePreservingScratch.sourceKey then
    .inl (.inr ScaleFinalScratch.answerKey) else .inr k
  inj' := by
    intro a b h
    by_cases ha : a = ETHBinsSourcePreservingScratch.sourceKey <;> by_cases hb : b = ETHBinsSourcePreservingScratch.sourceKey
    · exact ha.trans hb.symm
    · simp [ha,hb] at h
    · simp [ha,hb] at h
    · simpa only [ha,hb,ite_false,Sum.inr.injEq] using h

def scaleProgram := fun l => stackStmt scaleEmbed (ETHScaleActualComplete.program l)
def binsProgram := fun l => stackStmt binsEmbed (ETHBinsSourcePreservingScratch.program l)
def scaleStart : ETHScaleActualComplete.Label :=
  BitMachineRawSequence.leftLabel ETHScaleActualComplete.oldStart
def scaleControl : ETHScaleActualComplete.Control :=
  (ETHScaleActualComplete.oldControl,ETHScaleActualComplete.finalControl)
def binsStart : ETHBinsSourcePreservingScratch.Label :=
  BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan
def binsControl : ETHBinsSourcePreservingScratch.Control :=
  (none,ETHBinsStandaloneScratch.machine.initial)
def program := BitMachineRawSequence.program scaleProgram binsProgram
  binsStart scaleControl binsControl

def initialBank (i : Parameters.Input) : Stack → List Bool :=
  bank scaleEmbed (fun _ => []) (ETHScaleActualComplete.initialBank i)
def totalBound (i : Parameters.Input) : ℕ :=
  ETHScaleActualComplete.totalBound i + ETHBinsSourcePreservingScratch.totalTime (Parameters.scale i) + 1

private theorem raw_not_bins (j : Fin 6) :
    ¬ ∃ k : ETHBinsSourcePreservingScratch.Stack,
      binsEmbed k = scaleEmbed (.inl (ETHScaleGlobalLog.raw j)) := by
  rintro ⟨k,h⟩
  by_cases hk : k = ETHBinsSourcePreservingScratch.sourceKey
  · simp [binsEmbed,hk,scaleEmbed,ETHScaleGlobalLog.raw] at h
  · simp [binsEmbed,hk,scaleEmbed] at h

theorem bins_initial_restrict (i : Parameters.Input)
    (S : ETHScaleActualComplete.Stack → List Bool)
    (hscale : S (.inr ScaleFinalScratch.answerKey) =
      List.replicate (Parameters.scale i) true) :
    ETHBinsSourcePreservingScratch.initialBank (Parameters.scale i) =
      fun k => bank scaleEmbed (fun _ => []) S (binsEmbed k) := by
  rw [ETHBinsSourcePreservingScratch.initial_spec]
  funext k
  by_cases hk : k = ETHBinsSourcePreservingScratch.sourceKey
  · subst k
    simp only [ite_true]
    change ETHBinsStandaloneScratch.unary (Parameters.scale i) =
      bank scaleEmbed (fun _ => []) S
        (scaleEmbed (.inr ScaleFinalScratch.answerKey))
    rw [bank_at]
    exact hscale.symm
  · simp only [hk,ite_false]
    have hout : ¬ ∃ x : ETHScaleActualComplete.Stack,
        scaleEmbed x = (.inr k : Stack) := by
      rintro ⟨x,hx⟩
      cases hx
    change [] = bank scaleEmbed (fun _ => []) S
      (if k = ETHBinsSourcePreservingScratch.sourceKey then
        .inl (.inr ScaleFinalScratch.answerKey) else .inr k)
    rw [if_neg hk]
    exact (bank_outside scaleEmbed (fun _ => []) S (.inr k) hout).symm

theorem actual_bins_run (i : Parameters.Input) :
    ∃ t ≤ totalBound i, ∃ v : Fin ETHBinsStandaloneScratch.machine.controlCount,
      ∃ F : Stack → List Bool,
      ((advance program)^[t])
        (⟨some (BitMachineRawSequence.leftLabel scaleStart),
          (scaleControl,binsControl),initialBank i⟩ :
          TM2.Cfg (fun _ : Stack => Bool) Label Control) =
        ⟨none,(scaleControl,(none,v)),F⟩ ∧
      F (.inr ETHBinsSourcePreservingScratch.outputKey) =
        List.replicate (Parameters.bins i) true ∧
      F (.inl (.inr ScaleFinalScratch.answerKey)) =
        List.replicate (Parameters.scale i) true ∧
      (∀ j : Fin 6,
        F (.inl (.inl (ETHScaleGlobalLog.raw j))) =
          ETHParameterScaleMachineInput.words i j) := by
  obtain ⟨ts,hts,S,hs,hscale,_,hraw⟩ := ETHScaleActualComplete.actual_scale_run i
  obtain ⟨tb,htb,v,hb,hbrun,hbinsSource,hbinsOut⟩ :=
    ETHBinsSourcePreservingScratch.bins_run (Parameters.scale i)
  have hleft :
      ((advance scaleProgram)^[ts])
        (⟨some scaleStart,scaleControl,initialBank i⟩ :
          TM2.Cfg (fun _ : Stack => Bool) ETHScaleActualComplete.Label ETHScaleActualComplete.Control) =
        ⟨none,(ETHScaleActualComplete.oldControl,ScaleFinalScratch.base,none),
          bank scaleEmbed (fun _ => []) S⟩ := by
    have he := BitMachineStackRun.run scaleEmbed (fun _ => [])
      ETHScaleActualComplete.program
      (⟨some scaleStart,scaleControl,ETHScaleActualComplete.initialBank i⟩ :
        TM2.Cfg (fun _ : ETHScaleActualComplete.Stack => Bool) ETHScaleActualComplete.Label ETHScaleActualComplete.Control) ts
    have hs' :
        ((advance ETHScaleActualComplete.program)^[ts])
          (⟨some scaleStart,scaleControl,ETHScaleActualComplete.initialBank i⟩ :
            TM2.Cfg (fun _ : ETHScaleActualComplete.Stack => Bool) ETHScaleActualComplete.Label ETHScaleActualComplete.Control) =
          ⟨none,(ETHScaleActualComplete.oldControl,ScaleFinalScratch.base,none),S⟩ := by
      simpa only [scaleStart,scaleControl] using hs
    rw [hs'] at he
    simpa only [scaleProgram,stackCfg,initialBank] using he
  have hloc := bins_initial_restrict i S hscale
  have hbase :
      bank binsEmbed (bank scaleEmbed (fun _ => []) S)
        (ETHBinsSourcePreservingScratch.initialBank (Parameters.scale i)) =
      bank scaleEmbed (fun _ => []) S := by
    exact bank_eq_self binsEmbed _ _ (fun k => congrFun hloc k)
  have hright :
      ((advance binsProgram)^[tb])
        (⟨some binsStart,binsControl,bank scaleEmbed (fun _ => []) S⟩ :
          TM2.Cfg (fun _ : Stack => Bool) ETHBinsSourcePreservingScratch.Label ETHBinsSourcePreservingScratch.Control) =
        ⟨none,(none,v),
          bank binsEmbed (bank scaleEmbed (fun _ => []) S) hb⟩ := by
    have he := BitMachineStackRun.run binsEmbed
      (bank scaleEmbed (fun _ => []) S) ETHBinsSourcePreservingScratch.program
      (⟨some binsStart,binsControl,ETHBinsSourcePreservingScratch.initialBank (Parameters.scale i)⟩ :
        TM2.Cfg (fun _ : ETHBinsSourcePreservingScratch.Stack => Bool) ETHBinsSourcePreservingScratch.Label ETHBinsSourcePreservingScratch.Control) tb
    have hb' :
        ((advance ETHBinsSourcePreservingScratch.program)^[tb])
          (⟨some binsStart,binsControl,ETHBinsSourcePreservingScratch.initialBank (Parameters.scale i)⟩ :
            TM2.Cfg (fun _ : ETHBinsSourcePreservingScratch.Stack => Bool) ETHBinsSourcePreservingScratch.Label ETHBinsSourcePreservingScratch.Control) =
          ⟨none,(none,v),hb⟩ := by
      simpa only [binsStart,binsControl] using hbrun
    rw [hb'] at he
    simpa only [binsProgram,stackCfg,hbase] using he
  obtain ⟨t,ht,hr⟩ := BitMachineRawSequence.runs
    scaleProgram binsProgram scaleStart binsStart
    scaleControl (ETHScaleActualComplete.oldControl,ScaleFinalScratch.base,none)
    binsControl (none,v)
    (initialBank i) (bank scaleEmbed (fun _ => []) S)
    (bank binsEmbed (bank scaleEmbed (fun _ => []) S) hb)
    ts tb hleft hright
  refine ⟨t, ?_, v,
    bank binsEmbed (bank scaleEmbed (fun _ => []) S) hb,
    ?_, ?_, ?_, ?_⟩
  · unfold totalBound
    omega
  · simpa only [program] using hr
  · change bank binsEmbed (bank scaleEmbed (fun _ => []) S) hb
      (binsEmbed ETHBinsSourcePreservingScratch.outputKey) = _
    rw [bank_at]
    simpa only [ETHBinsStandaloneScratch.bins_eq_parameters,
      ETHBinsStandaloneScratch.unary] using hbinsOut
  · change bank binsEmbed (bank scaleEmbed (fun _ => []) S) hb
      (binsEmbed ETHBinsSourcePreservingScratch.sourceKey) = _
    rw [bank_at]
    simpa only [ETHBinsStandaloneScratch.unary] using hbinsSource
  · intro j
    change bank binsEmbed (bank scaleEmbed (fun _ => []) S) hb
      (scaleEmbed (.inl (ETHScaleGlobalLog.raw j))) = _
    rw [bank_outside binsEmbed _ _ _ (raw_not_bins j)]
    rw [bank_at]
    exact hraw j

end
end EthInapproximability.CurrentPaper.ETHBinsJoinedScratch
