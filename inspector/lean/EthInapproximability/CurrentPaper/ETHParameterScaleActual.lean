import EthInapproximability.CurrentPaper.ETHParameterScaleActualBound
import EthInapproximability.CurrentPaper.ETHParameterScaleFinalStage

/-! One fixed physical controller from the actual six raw unary parameter
words through the candidate logarithms, six-way maximum, final logarithm,
constant floor, final maximum, and cleanup. -/

namespace EthInapproximability.CurrentPaper.ETHScaleActualComplete

open Turing BitMachineEncoding BitMachineStackEmbedding

noncomputable section

set_option maxHeartbeats 1000000

abbrev Stack := ETHScaleActualScaleBound.Stack ⊕ ScaleFinalScratch.Stack
abbrev Label := BitMachineRawSequence.Label ETHScaleActualScaleBound.Label ScaleFinalScratch.Label
abbrev Control := ETHScaleActualScaleBound.Control × ScaleFinalScratch.Control

def oldEmbed : ETHScaleActualScaleBound.Stack ↪ Stack :=
  ⟨Sum.inl, by intro a b h; exact Sum.inl_injective h⟩

def finalEmbed : ScaleFinalScratch.Stack ↪ Stack where
  toFun k := if k = ScaleFinalScratch.sourceKey then
    .inl (ETHScaleGlobalLog.tail 12) else .inr k
  inj' := by
    intro a b h
    by_cases ha : a = ScaleFinalScratch.sourceKey <;>
      by_cases hb : b = ScaleFinalScratch.sourceKey
    · exact ha.trans hb.symm
    · simp [ha,hb] at h
    · simp [ha,hb] at h
    · simpa only [ha,hb,ite_false,Sum.inr.injEq] using h

def oldProgram := fun l => stackStmt oldEmbed (ETHScaleActualScaleBound.program l)
def finalProgram := fun l => stackStmt finalEmbed (ScaleFinalScratch.program l)

def oldStart : ETHScaleActualScaleBound.Label :=
  BitMachineRawSequence.leftLabel
    (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel
        (BitMachineRawSequence.leftLabel
          (BitMachineRawSequence.leftLabel
            (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan)))))

def oldControl : ETHScaleActualScaleBound.Control :=
  ((((ETHScaleGlobalLog.edgeControl,
    ETHScaleGlobalLog.columnControl),
    ETHScaleGlobalLog.columnControl), none), (none,none))

def finalStart : ScaleFinalScratch.Label := .log (.inl .scan)
def finalControl : ScaleFinalScratch.Control :=
  ScaleFinalScratch.logControl (ETHParameterScaleMachineLogCopy.copyControl none)

def program := BitMachineRawSequence.program oldProgram finalProgram
  finalStart oldControl finalControl

def initialBank (i : Parameters.Input) : Stack → List Bool :=
  bank oldEmbed (fun _ => []) (ETHScaleGlobalLog.initial i)

def totalBound (i : Parameters.Input) : ℕ :=
  ETHScaleActualScaleBound.totalBound i + ScaleFinalScratch.inputClock (Parameters.scaleBound i) + 1

private theorem raw_not_final (j : Fin 6) :
    ¬ ∃ k : ScaleFinalScratch.Stack,
      finalEmbed k = oldEmbed (ETHScaleGlobalLog.raw j) := by
  rintro ⟨k,h⟩
  by_cases hk : k = ScaleFinalScratch.sourceKey
  · simp [finalEmbed,hk,oldEmbed,
      ETHScaleGlobalLog.tail,ETHScaleGlobalLog.raw] at h
  · simp [finalEmbed,hk,oldEmbed] at h

theorem final_initial_restrict (i : Parameters.Input)
    (S : ETHScaleActualScaleBound.Stack → List Bool)
    (hword : S (ETHScaleGlobalLog.tail 12) =
      List.replicate (Parameters.scaleBound i) true) :
    ScaleFinalScratch.initialBank (Parameters.scaleBound i) =
      fun k => bank oldEmbed (fun _ => []) S (finalEmbed k) := by
  rw [ScaleFinalScratch.initialBank_spec]
  funext k
  by_cases hk : k = ScaleFinalScratch.sourceKey
  · subst k
    simp only [ite_true]
    change List.replicate (Parameters.scaleBound i) true =
      bank oldEmbed (fun _ => []) S
        (oldEmbed (ETHScaleGlobalLog.tail 12))
    rw [bank_at]
    exact hword.symm
  · simp only [hk,ite_false]
    have hout : ¬ ∃ x : ETHScaleActualScaleBound.Stack,
        oldEmbed x = (.inr k : Stack) := by
      rintro ⟨x,hx⟩
      cases hx
    change [] = bank oldEmbed (fun _ => []) S
      (if k = ScaleFinalScratch.sourceKey then
        .inl (ETHScaleGlobalLog.tail 12) else .inr k)
    rw [if_neg hk]
    exact (bank_outside oldEmbed (fun _ => []) S (.inr k) hout).symm

/-- Fixed finite-control execution of the literal single-scale formula from
the six raw unary source fields. The bound counts every staged handoff and
the final floor emitter/cleanup; no candidate or scaleBound word is supplied
as a premise. -/
theorem actual_scale_run (i : Parameters.Input) :
    ∃ t ≤ totalBound i, ∃ F : Stack → List Bool,
      ((advance program)^[t])
        (⟨some (BitMachineRawSequence.leftLabel oldStart),
          (oldControl,finalControl), initialBank i⟩ :
          TM2.Cfg (fun _ : Stack => Bool) Label Control) =
        ⟨none,(oldControl,ScaleFinalScratch.base,none),F⟩ ∧
      F (.inr ScaleFinalScratch.answerKey) =
        List.replicate (Parameters.scale i) true ∧
      F (.inl (ETHScaleGlobalLog.tail 12)) =
        List.replicate (Parameters.scaleBound i) true ∧
      (∀ j : Fin 6, F (.inl (ETHScaleGlobalLog.raw j)) =
        ETHParameterScaleMachineInput.words i j) := by
  obtain ⟨tOld,htOld,S,ho,hscale,hraw⟩ := ETHScaleActualScaleBound.actual_scaleBound_run i
  obtain ⟨tf,c,htf,hf,hsource,hanswer,_,_⟩ :=
    ScaleFinalScratch.final_scale_input_clock_for i
  have hstart :
      bank oldEmbed (fun _ => []) (ETHScaleGlobalLog.initial i) =
        initialBank i := rfl
  have hold :
      ((advance oldProgram)^[tOld])
        (⟨some oldStart,oldControl,initialBank i⟩ :
          TM2.Cfg (fun _ : Stack => Bool) ETHScaleActualScaleBound.Label ETHScaleActualScaleBound.Control) =
        ⟨none,oldControl,bank oldEmbed (fun _ => []) S⟩ := by
    have he := BitMachineStackRun.run oldEmbed (fun _ => [])
      ETHScaleActualScaleBound.program
      (⟨some oldStart,oldControl,ETHScaleGlobalLog.initial i⟩ :
        TM2.Cfg (fun _ : ETHScaleActualScaleBound.Stack => Bool) ETHScaleActualScaleBound.Label ETHScaleActualScaleBound.Control) tOld
    have ho' :
        ((advance ETHScaleActualScaleBound.program)^[tOld])
          (⟨some oldStart,oldControl,ETHScaleGlobalLog.initial i⟩ :
            TM2.Cfg (fun _ : ETHScaleActualScaleBound.Stack => Bool)
              ETHScaleActualScaleBound.Label ETHScaleActualScaleBound.Control) =
          ⟨none,oldControl,S⟩ := by
      simpa only [oldStart,oldControl] using ho
    rw [ho'] at he
    simpa only [oldProgram,stackCfg,oldStart,oldControl,initialBank] using he
  have hlocal := final_initial_restrict i S hscale
  have hbase :
      bank finalEmbed (bank oldEmbed (fun _ => []) S)
        (ScaleFinalScratch.initialBank (Parameters.scaleBound i)) =
      bank oldEmbed (fun _ => []) S := by
    exact bank_eq_self finalEmbed _ _ (fun k => congrFun hlocal k)
  have hfinal :
      ((advance finalProgram)^[tf])
        (⟨some finalStart,finalControl,
          bank oldEmbed (fun _ => []) S⟩ :
          TM2.Cfg (fun _ : Stack => Bool) ScaleFinalScratch.Label ScaleFinalScratch.Control) =
        ⟨none,(ScaleFinalScratch.base,none),
          bank finalEmbed (bank oldEmbed (fun _ => []) S)
            (ScaleFinalScratch.finalBank (Parameters.scaleBound i) c)⟩ := by
    have he := BitMachineStackRun.run finalEmbed
      (bank oldEmbed (fun _ => []) S) ScaleFinalScratch.program
      (⟨some finalStart,finalControl,
        ScaleFinalScratch.initialBank (Parameters.scaleBound i)⟩ : ScaleFinalScratch.Config) tf
    have hf' :
        ((advance ScaleFinalScratch.program)^[tf])
          (⟨some finalStart,finalControl,
            ScaleFinalScratch.initialBank (Parameters.scaleBound i)⟩ :
            ScaleFinalScratch.Config) =
          ⟨none,(ScaleFinalScratch.base,none),
            ScaleFinalScratch.finalBank (Parameters.scaleBound i) c⟩ := by
      simpa only [ScaleFinalScratch.run,finalStart,finalControl] using hf
    rw [hf'] at he
    simpa only [finalProgram,stackCfg,finalStart,finalControl,hbase] using he
  obtain ⟨t,ht,hr⟩ := BitMachineRawSequence.runs
    oldProgram finalProgram oldStart finalStart
    oldControl oldControl finalControl (ScaleFinalScratch.base,none)
    (initialBank i) (bank oldEmbed (fun _ => []) S)
    (bank finalEmbed (bank oldEmbed (fun _ => []) S)
      (ScaleFinalScratch.finalBank (Parameters.scaleBound i) c))
    tOld tf hold hfinal
  refine ⟨t, ?_,
    bank finalEmbed (bank oldEmbed (fun _ => []) S)
      (ScaleFinalScratch.finalBank (Parameters.scaleBound i) c),
    ?_, ?_, ?_, ?_⟩
  · unfold totalBound
    omega
  · simpa only [program] using hr
  · change bank finalEmbed (bank oldEmbed (fun _ => []) S)
      (ScaleFinalScratch.finalBank (Parameters.scaleBound i) c)
      (finalEmbed ScaleFinalScratch.answerKey) = _
    rw [bank_at]
    exact hanswer
  · change bank finalEmbed (bank oldEmbed (fun _ => []) S)
      (ScaleFinalScratch.finalBank (Parameters.scaleBound i) c)
      (finalEmbed ScaleFinalScratch.sourceKey) = _
    rw [bank_at]
    exact hsource
  · intro j
    change bank finalEmbed (bank oldEmbed (fun _ => []) S)
      (ScaleFinalScratch.finalBank (Parameters.scaleBound i) c)
      (oldEmbed (ETHScaleGlobalLog.raw j)) = _
    rw [bank_outside finalEmbed _ _ _ (raw_not_final j)]
    rw [bank_at]
    exact hraw j

end
end EthInapproximability.CurrentPaper.ETHScaleActualComplete
