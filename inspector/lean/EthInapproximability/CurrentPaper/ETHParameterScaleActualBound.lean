import EthInapproximability.CurrentPaper.ETHParameterScaleCandidateProducer

/-! One physical fixed controller from the six authoritative raw unary words
to the unary scaleBound. The candidate-producing segment and six-way maximum
fold are sequenced on one ambient bank. -/

namespace EthInapproximability.CurrentPaper.ETHScaleActualScaleBound

open Turing BitMachineEncoding BitMachineStackEmbedding
open ETHScaleCandidateProducer

noncomputable section

set_option maxHeartbeats 1000000

abbrev Stack := ETHScaleGlobalLog.Stack
abbrev CandidateLabel := BitMachineRawSequence.Label
  (BitMachineRawSequence.Label
    (BitMachineRawSequence.Label
      ETHScaleEdgePreparation.FullLabel ETHScaleColumnCandidate.Label)
    ETHScaleColumnCandidate.Label)
  ScaleRawTailScratch.Label
abbrev CandidateControl :=
  (((ETHScaleEdgePreparation.FullControl × ETHScaleColumnCandidate.Control) ×
    ETHScaleColumnCandidate.Control) × Option Bool)
abbrev Label := BitMachineRawSequence.Label CandidateLabel ScaleMaxFoldScratch.Label
abbrev Control := CandidateControl × ScaleMaxFoldScratch.Control

def foldProgram := fun l =>
  stackStmt foldEmbed (ScaleMaxFoldScratch.program l)

def program := BitMachineRawSequence.program candidateProgram foldProgram
  (0 : ScaleMaxFoldScratch.Label)
  (((ETHScaleGlobalLog.edgeControl, ETHScaleGlobalLog.columnControl),
    ETHScaleGlobalLog.columnControl), none)
  (none, none)

def totalBound (i : Parameters.Input) :=
  candidateBound i + ScaleMaxFoldScratch.totalCost i + 1

private theorem raw_not_fold (j : Fin 6) :
    ¬ ∃ k : Fin 13, foldEmbed k = ETHScaleGlobalLog.raw j := by
  rintro ⟨k, h⟩
  fin_cases k <;>
    simp [foldEmbed, ETHScaleGlobalLog.raw,
      ETHScaleGlobalLog.edgeOut, ETHScaleGlobalLog.columnOut,
      ETHScaleGlobalLog.rowOut, ETHScaleGlobalLog.tail,
      ETHScaleGlobalLog.edgeEmbed, ETHScaleGlobalLog.columnEmbed,
      ETHScaleGlobalLog.rowEmbed,
      ETHScaleGlobalLog.edgePrivate, ETHScaleGlobalLog.columnPrivate,
      ETHScaleGlobalLog.rowPrivate,
      ETHScaleEdgePreparation.candidateEmbed,
      ETHScaleEdgePreparation.raw] at h

/-- This theorem has no preloaded candidate premise: the initial bank holds
only the six supplied raw unary words in the actual source order. -/
theorem actual_scaleBound_run (i : Parameters.Input) :
    ∃ t ≤ totalBound i, ∃ F : Stack → List Bool,
      ((advance program)^[t])
        (⟨some (BitMachineRawSequence.leftLabel
            (BitMachineRawSequence.leftLabel
              (BitMachineRawSequence.leftLabel
                (BitMachineRawSequence.leftLabel
                  (BitMachineRawSequence.leftLabel
                    (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan)))))),
          ((((ETHScaleGlobalLog.edgeControl,
              ETHScaleGlobalLog.columnControl),
              ETHScaleGlobalLog.columnControl), none), (none,none)),
          ETHScaleGlobalLog.initial i⟩ :
          TM2.Cfg (fun _ : Stack => Bool) Label Control) =
        ⟨none,
          ((((ETHScaleGlobalLog.edgeControl,
              ETHScaleGlobalLog.columnControl),
              ETHScaleGlobalLog.columnControl), none), (none,none)), F⟩ ∧
      F (ETHScaleGlobalLog.tail 12) =
        List.replicate (Parameters.scaleBound i) true ∧
      (∀ j : Fin 6, F (ETHScaleGlobalLog.raw j) =
        ETHParameterScaleMachineInput.words i j) := by
  obtain ⟨tc, htc, S, hc, hbank, hraw⟩ := candidate_run i
  obtain ⟨tf, htf, hf⟩ := ScaleMaxFoldScratch.six_phase_run i
  have hbase : bank foldEmbed S (ScaleMaxFoldScratch.inputBank i) = S := by
    exact bank_eq_self foldEmbed S _ (fun j => (hbank j).symm)
  have hfold :
      ((advance foldProgram)^[tf])
        (⟨some (0 : ScaleMaxFoldScratch.Label), (none,none), S⟩ :
          TM2.Cfg (fun _ : Stack => Bool)
            ScaleMaxFoldScratch.Label ScaleMaxFoldScratch.Control) =
        ⟨none, (none,none),
          bank foldEmbed S (ScaleMaxFoldScratch.finalBank i)⟩ := by
    have he := BitMachineStackRun.run foldEmbed S
      ScaleMaxFoldScratch.program
      (⟨some (0 : ScaleMaxFoldScratch.Label), (none,none),
        ScaleMaxFoldScratch.inputBank i⟩ : ScaleMaxFoldScratch.Config) tf
    change ((advance ScaleMaxFoldScratch.program)^[tf]) _ = _ at hf
    rw [hf] at he
    simpa only [foldProgram, stackCfg, hbase] using he
  obtain ⟨t, ht, hr⟩ := BitMachineRawSequence.runs
    candidateProgram foldProgram
    (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel
        (BitMachineRawSequence.leftLabel
          (BitMachineRawSequence.leftLabel
            (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan)))))
    (0 : ScaleMaxFoldScratch.Label)
    (((ETHScaleGlobalLog.edgeControl, ETHScaleGlobalLog.columnControl),
      ETHScaleGlobalLog.columnControl), none)
    (((ETHScaleGlobalLog.edgeControl, ETHScaleGlobalLog.columnControl),
      ETHScaleGlobalLog.columnControl), none)
    (none,none) (none,none)
    (ETHScaleGlobalLog.initial i) S
    (bank foldEmbed S (ScaleMaxFoldScratch.finalBank i))
    tc tf hc hfold
  refine ⟨t, ?_, bank foldEmbed S (ScaleMaxFoldScratch.finalBank i),
    ?_, ?_, ?_⟩
  · unfold totalBound
    omega
  · simpa only [program] using hr
  · have he : foldEmbed (12 : Fin 13) = ETHScaleGlobalLog.tail 12 := rfl
    rw [← he, bank_at]
    rfl
  · intro j
    rw [bank_outside foldEmbed S _ _ (raw_not_fold j)]
    exact hraw j

end
end EthInapproximability.CurrentPaper.ETHScaleActualScaleBound
