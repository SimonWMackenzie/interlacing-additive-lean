import EthInapproximability.CurrentPaper.ETHParameterScaleGlobalLog
import EthInapproximability.CurrentPaper.ETHParameterScaleMaxFold
import EthInapproximability.CurrentPaper.ETHParameterScaleRawTail

/-! Literal six-candidate preparation from the supplied six raw unary words.
The three logarithms are produced by the checked fixed global log controller;
the other three words and seed are produced by the checked physical raw-tail
controller. The resulting bank is passed to the fixed six-way max fold through
one injective stack map; no candidate value is supplied as a premise. -/

namespace EthInapproximability.CurrentPaper.ETHScaleCandidateProducer

open Turing BitMachineEncoding BitMachineStackEmbedding
open scoped Classical

abbrev Private := ETHScaleEdgePreparation.Stack ⊕
  (ETHScaleColumnCandidate.Stack ⊕ ETHScaleColumnCandidate.Stack)
abbrev Stack := ETHScaleGlobalLog.Stack

noncomputable def foldEmbed : Fin 13 ↪ Stack where
  toFun := ![ETHScaleGlobalLog.edgeOut,
    ETHScaleGlobalLog.columnOut,
    ETHScaleGlobalLog.rowOut,
    ETHScaleGlobalLog.tail 3,
    ETHScaleGlobalLog.tail 4,
    ETHScaleGlobalLog.tail 5,
    ETHScaleGlobalLog.tail 6,
    ETHScaleGlobalLog.tail 7,
    ETHScaleGlobalLog.tail 8,
    ETHScaleGlobalLog.tail 9,
    ETHScaleGlobalLog.tail 10,
    ETHScaleGlobalLog.tail 11,
    ETHScaleGlobalLog.tail 12]
  inj' := by
    intro a b h
    fin_cases a <;> fin_cases b <;>
      simp [ETHScaleGlobalLog.edgeOut, ETHScaleGlobalLog.columnOut,
        ETHScaleGlobalLog.rowOut, ETHScaleGlobalLog.edgeEmbed,
        ETHScaleGlobalLog.columnEmbed, ETHScaleGlobalLog.rowEmbed,
        ETHScaleGlobalLog.edgePrivate, ETHScaleGlobalLog.columnPrivate,
        ETHScaleGlobalLog.rowPrivate, ETHScaleGlobalLog.tail,
        ETHScaleEdgePreparation.candidateEmbed,
        ETHScaleEdgePreparation.raw] at h ⊢

noncomputable def candidateProgram :=
  BitMachineRawSequence.program ETHScaleGlobalLog.threeProgram
    (ScaleRawTailScratch.program (Private := Private))
    (.copy 0 .scan)
    ((ETHScaleGlobalLog.edgeControl, ETHScaleGlobalLog.columnControl),
      ETHScaleGlobalLog.columnControl) none

noncomputable def candidateBound (i : Parameters.Input) :=
  ETHScaleGlobalLog.threeBound i +
    ((2*i.cost+2)+(2*i.nextDepth+2)+(2*i.sourceConstant+2)+2) + 1

theorem tail_inputBank (i : Parameters.Input) (S : Stack → List Bool)
    (hraw : ∀ j : Fin 6,
      S (ETHScaleGlobalLog.raw j) = ETHParameterScaleMachineInput.words i j)
    (h0 : S ETHScaleGlobalLog.edgeOut =
      List.replicate (Nat.clog 2 (i.edges+2)) true)
    (h1 : S ETHScaleGlobalLog.columnOut =
      List.replicate (Nat.clog 2 i.columns) true)
    (h2 : S ETHScaleGlobalLog.rowOut =
      List.replicate (Nat.clog 2 i.rows) true)
    (htail : ∀ j : Fin 13, S (ETHScaleGlobalLog.tail j) = []) :
    ∀ j : Fin 13,
      ScaleRawTailScratch.outputBank S (foldEmbed j) =
        ScaleMaxFoldScratch.inputBank i j := by
  have hprivate0 : ScaleRawTailScratch.outputBank S
      ETHScaleGlobalLog.edgeOut = S ETHScaleGlobalLog.edgeOut := by
    change ScaleRawTailScratch.outputBank S
      (.inr (.inr (.inl
        (ETHScaleEdgePreparation.candidateEmbed (.inr 0))))) = _
    exact ScaleRawTailScratch.outputBank_private S _
  have hprivate1 : ScaleRawTailScratch.outputBank S
      ETHScaleGlobalLog.columnOut = S ETHScaleGlobalLog.columnOut := by
    change ScaleRawTailScratch.outputBank S
      (.inr (.inr (.inr (.inl (.inr 0))))) = _
    exact ScaleRawTailScratch.outputBank_private S _
  have hprivate2 : ScaleRawTailScratch.outputBank S
      ETHScaleGlobalLog.rowOut = S ETHScaleGlobalLog.rowOut := by
    change ScaleRawTailScratch.outputBank S
      (.inr (.inr (.inr (.inr (.inr 0))))) = _
    exact ScaleRawTailScratch.outputBank_private S _
  have hw := ScaleRawTailScratch.outputBank_words i S hraw
  intro j
  by_cases hj : j.val < 7
  · fin_cases j <;> simp at hj
    · change ScaleRawTailScratch.outputBank S ETHScaleGlobalLog.edgeOut = _
      simpa [ScaleMaxFoldScratch.inputBank, ScaleMaxFoldScratch.candidate]
        using hprivate0.trans h0
    · change ScaleRawTailScratch.outputBank S ETHScaleGlobalLog.columnOut = _
      simpa [ScaleMaxFoldScratch.inputBank, ScaleMaxFoldScratch.candidate]
        using hprivate1.trans h1
    · change ScaleRawTailScratch.outputBank S ETHScaleGlobalLog.rowOut = _
      simpa [ScaleMaxFoldScratch.inputBank, ScaleMaxFoldScratch.candidate]
        using hprivate2.trans h2
    · simpa [foldEmbed, ScaleMaxFoldScratch.inputBank,
        ScaleMaxFoldScratch.candidate] using hw.1
    · simpa [foldEmbed, ScaleMaxFoldScratch.inputBank,
        ScaleMaxFoldScratch.candidate] using hw.2.1
    · simpa [foldEmbed, ScaleMaxFoldScratch.inputBank,
        ScaleMaxFoldScratch.candidate] using hw.2.2.1
    · simpa [foldEmbed, ScaleMaxFoldScratch.inputBank,
        ScaleMaxFoldScratch.candidate] using hw.2.2.2
  · have hf : foldEmbed j = ETHScaleGlobalLog.tail j := by
      fin_cases j <;> simp_all [foldEmbed, ETHScaleGlobalLog.tail]
    rw [hf]
    change ScaleRawTailScratch.outputBank S
      (ScaleRawTailScratch.candidate j) = _
    rw [ScaleRawTailScratch.outputBank_suffix S j (by omega)]
    change S (ETHScaleGlobalLog.tail j) = _
    rw [htail j]
    fin_cases j <;> simp_all [ScaleMaxFoldScratch.inputBank]

theorem candidate_run (i : Parameters.Input) :
    ∃ t ≤ candidateBound i, ∃ F : Stack → List Bool,
      ((advance candidateProgram)^[t])
        (⟨some (BitMachineRawSequence.leftLabel
            (BitMachineRawSequence.leftLabel
              (BitMachineRawSequence.leftLabel
                (BitMachineRawSequence.leftLabel
                  (BitMachineRawSequence.leftLabel .scan))))),
          (((ETHScaleGlobalLog.edgeControl,
              ETHScaleGlobalLog.columnControl),
              ETHScaleGlobalLog.columnControl), none),
          ETHScaleGlobalLog.initial i⟩ :
          TM2.Cfg (fun _ : Stack => Bool)
            (BitMachineRawSequence.Label
              (BitMachineRawSequence.Label
                (BitMachineRawSequence.Label
                  ETHScaleEdgePreparation.FullLabel ETHScaleColumnCandidate.Label)
                ETHScaleColumnCandidate.Label)
              ScaleRawTailScratch.Label)
            (((ETHScaleEdgePreparation.FullControl × ETHScaleColumnCandidate.Control) ×
              ETHScaleColumnCandidate.Control) × Option Bool)) =
        ⟨none,
          (((ETHScaleGlobalLog.edgeControl,
              ETHScaleGlobalLog.columnControl),
              ETHScaleGlobalLog.columnControl), none), F⟩ ∧
      (∀ j : Fin 13, F (foldEmbed j) =
        ScaleMaxFoldScratch.inputBank i j) ∧
      (∀ j : Fin 6, F (ETHScaleGlobalLog.raw j) =
        ETHParameterScaleMachineInput.words i j) := by
  obtain ⟨tg, htg, S, hg, h0, h1, h2, hraw, htail⟩ :=
    ETHScaleGlobalLog.three_log_run i
  have ht3 : S (ScaleRawTailScratch.candidate 3) = [] := htail 3
  have ht4 : S (ScaleRawTailScratch.candidate 4) = [] := htail 4
  have ht5 : S (ScaleRawTailScratch.candidate 5) = [] := htail 5
  have ht6 : S ScaleRawTailScratch.seed = [] := htail 6
  have ht7 : S ScaleRawTailScratch.scratch = [] := htail 7
  obtain ⟨tt, htt, htailRun⟩ :=
    ScaleRawTailScratch.raw_tail_run S ht3 ht4 ht5 ht6 ht7
  have htailRun' :
      ((advance (ScaleRawTailScratch.program (Private := Private)))^[tt])
        (⟨some (.copy 0 .scan), none, S⟩ :
          TM2.Cfg (fun _ : Stack => Bool)
            ScaleRawTailScratch.Label (Option Bool)) =
        ⟨none, none, ScaleRawTailScratch.outputBank S⟩ := by
    simpa only [ScaleRawTailScratch.run] using htailRun
  obtain ⟨t, ht, hr⟩ := BitMachineRawSequence.runs
    ETHScaleGlobalLog.threeProgram
    (ScaleRawTailScratch.program (Private := Private))
    (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel
        (BitMachineRawSequence.leftLabel
          (BitMachineRawSequence.leftLabel .scan))))
    (.copy 0 .scan)
    ((ETHScaleGlobalLog.edgeControl, ETHScaleGlobalLog.columnControl),
      ETHScaleGlobalLog.columnControl)
    ((ETHScaleGlobalLog.edgeControl, ETHScaleGlobalLog.columnControl),
      ETHScaleGlobalLog.columnControl)
    none none (ETHScaleGlobalLog.initial i) S
    (ScaleRawTailScratch.outputBank S) tg tt hg htailRun'
  refine ⟨t, ?_, ScaleRawTailScratch.outputBank S,
    by simpa only [candidateProgram] using hr, ?_, ?_⟩
  · have hw2 := hraw 2
    have hw1 := hraw 1
    have hw0 := hraw 0
    simp only [ETHParameterScaleMachineInput.words,
      ScaleRawTailScratch.raw, ETHScaleGlobalLog.raw] at hw2 hw1 hw0
    have hl2 : (S (.inl 2)).length = i.cost := by rw [hw2]; simp
    have hl1 : (S (.inl 1)).length = i.nextDepth := by rw [hw1]; simp
    have hl0 : (S (.inl 0)).length = i.sourceConstant := by rw [hw0]; simp
    change tt ≤ (2*(S (.inl 2)).length+2) +
      (2*(S (.inl 1)).length+2) +
      (2*(S (.inl 0)).length+2) + 2 at htt
    rw [hl2, hl1, hl0] at htt
    unfold candidateBound
    omega
  · exact tail_inputBank i S hraw h0 h1 h2 htail
  · intro j
    exact (ScaleRawTailScratch.outputBank_raw S j).trans (hraw j)

end EthInapproximability.CurrentPaper.ETHScaleCandidateProducer
