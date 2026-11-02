import EthInapproximability.CurrentPaper.WeightedLevel0Ready

/-! Lane owner:b-weighted-level-4, unit 2, segment 1 (1c-iii), piece 1c-c (writer part).

The charged handoff of the level-0 writer frame into the ADMITTED writer run,
with writer 22 as the one named premise: for ANY global bank `S` that agrees
with the exit bank `G4 …` of `readyProgram` on every writer-stack cell except
writer 22 and holds `d.rawBits` in writer 22 (the premise: lane
owner:b-stage4-entry-program-2 writes it), the admitted
`MatrixWeightedOrderWriter.program`, embedded by `wEmb` into the SAME global
stack (production `BitMachineStackRun.run` via `WeightedRawWords.region_run`),
runs from its fixed start label/control within the admitted
`ProtectedFullBankBridgeScratch.actualWriterBound` to the admitted writer exit
(`PostProtectedWriterRunScratch.actual_writer_source_run`): writer bank
`persistentBank d`, `rows`/`cols` words, output word `rowMajor (actualF …)`,
every cell outside the writer region unchanged. -/

namespace EthInapproximability.CurrentPaper.WeightedLevel0WriterRun

open Turing BitMachineEncoding BitMachineStackEmbedding
open EthInapproximability.ParameterizedNP.GuardedSourceGraph
open WeightedLevel0Rows WeightedLevel0Persist WeightedLevel0Clean WeightedLevel0Target
  WeightedLevel0Ready

noncomputable section

set_option maxHeartbeats 8000000
set_option maxRecDepth 8192
set_option synthInstance.maxSize 200000
set_option synthInstance.maxHeartbeats 2000000

theorem pb22 (d : MatrixWeightedEntryController.Input) :
    MatrixWeightedEntryController.persistentBank d 22 = d.rawBits := by
  simp [MatrixWeightedEntryController.persistentBank]

variable (M : BitMachine.Machine)
variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

/-- The admitted writer program embedded into the global stack. -/
def writerG := fun l => stackStmt wEmb (MatrixWeightedOrderWriter.program l)

theorem writer_start_22 (G : EndpointGraph V E) (n c : ℕ) :
    (ProtectedFullBankBridgeScratch.actualWriterStart G c (EffectiveIteration.sourceDepth n)
        (Iteration.seedState (EffectiveIteration.sourceDepth n)).budget 0
        (Iteration.seedState (EffectiveIteration.sourceDepth n)).matrix).stk (.inl (.inl 22)) =
      (ProtectedFullBankBridgeScratch.actualD G c (EffectiveIteration.sourceDepth n)
        (Iteration.seedState (EffectiveIteration.sourceDepth n)).budget 0
        (Iteration.seedState (EffectiveIteration.sourceDepth n)).matrix).rawBits := by
  show MatrixWeightedOrderPreparation.sourceBank _ _ _ _ 22 = _
  rw [sb_other _ _ _ _ 22 (by decide), pb22]

theorem level0_writer_run (G : EndpointGraph V E) (n c : ℕ)
    (F : ETHBinsJoinedScratch.Stack → List Bool)
    (Q : WeightedGraphQJoined.Stack → List Bool) (P : ChosenPrimeRaw.Stack → List Bool)
    (hf : level0Facts M G n c F Q P) (S : GStack → List Bool)
    (hS : ∀ w, w ≠ .inl (.inl 22) → S (wEmb w) = G4 (level0RowsBank M G n c F Q P) (wEmb w))
    (h22 : S (wEmb (.inl (.inl 22))) =
      (ProtectedFullBankBridgeScratch.actualD G c (EffectiveIteration.sourceDepth n)
        (Iteration.seedState (EffectiveIteration.sourceDepth n)).budget 0
        (Iteration.seedState (EffectiveIteration.sourceDepth n)).matrix).rawBits) :
    ∃ t ≤ ProtectedFullBankBridgeScratch.actualWriterBound G c (EffectiveIteration.sourceDepth n)
        (Iteration.seedState (EffectiveIteration.sourceDepth n)).budget 0
        (Iteration.seedState (EffectiveIteration.sourceDepth n)).matrix,
      ∃ w,
        ((advance writerG)^[t])
          (⟨some (BitMachineRawSequence.leftLabel MatrixWeightedOrderPreparation.start),
            (MatrixWeightedOrderPreparation.initial, MatrixWeightedOrderWriter.writerInitial),
            S⟩ : TM2.Cfg (fun _ : GStack => Bool) MatrixWeightedOrderWriter.Label
              MatrixWeightedOrderWriter.Control) =
          ⟨none, (MatrixWeightedOrderPreparation.initial, w),
            bank wEmb S (MatrixTableWriter.ready
              (MatrixWeightedEntryController.persistentBank
                (ProtectedFullBankBridgeScratch.actualD G c (EffectiveIteration.sourceDepth n)
                  (Iteration.seedState (EffectiveIteration.sourceDepth n)).budget 0
                  (Iteration.seedState (EffectiveIteration.sourceDepth n)).matrix))
              (ProtectedFullBankBridgeScratch.actualRows G c (EffectiveIteration.sourceDepth n)
                (Iteration.seedState (EffectiveIteration.sourceDepth n)).budget 0
                (Iteration.seedState (EffectiveIteration.sourceDepth n)).matrix)
              (ProtectedFullBankBridgeScratch.actualCols G c (EffectiveIteration.sourceDepth n)
                (Iteration.seedState (EffectiveIteration.sourceDepth n)).budget 0
                (Iteration.seedState (EffectiveIteration.sourceDepth n)).matrix)
              0 0 0 0 []
              (MatrixMaterialization.rowMajor
                (ProtectedFullBankBridgeScratch.actualF G c (EffectiveIteration.sourceDepth n)
                  (Iteration.seedState (EffectiveIteration.sourceDepth n)).budget 0
                  (Iteration.seedState (EffectiveIteration.sourceDepth n)).matrix))).contents⟩ := by
  obtain ⟨tw, htw, w, hw⟩ := PostProtectedWriterRunScratch.actual_writer_source_run
    G c (EffectiveIteration.sourceDepth n)
    (Iteration.seedState (EffectiveIteration.sourceDepth n)).budget 0
    (Iteration.seedState (EffectiveIteration.sourceDepth n)).matrix
  have hrun : MatrixWeightedOrderWriter.run tw
      (ProtectedFullBankBridgeScratch.actualWriterStart G c (EffectiveIteration.sourceDepth n)
        (Iteration.seedState (EffectiveIteration.sourceDepth n)).budget 0
        (Iteration.seedState (EffectiveIteration.sourceDepth n)).matrix) =
      MatrixWeightedOrderWriter.cfg none (MatrixWeightedOrderPreparation.initial, w)
        (MatrixTableWriter.ready
          (MatrixWeightedEntryController.persistentBank
            (ProtectedFullBankBridgeScratch.actualD G c (EffectiveIteration.sourceDepth n)
              (Iteration.seedState (EffectiveIteration.sourceDepth n)).budget 0
              (Iteration.seedState (EffectiveIteration.sourceDepth n)).matrix))
          (ProtectedFullBankBridgeScratch.actualRows G c (EffectiveIteration.sourceDepth n)
            (Iteration.seedState (EffectiveIteration.sourceDepth n)).budget 0
            (Iteration.seedState (EffectiveIteration.sourceDepth n)).matrix)
          (ProtectedFullBankBridgeScratch.actualCols G c (EffectiveIteration.sourceDepth n)
            (Iteration.seedState (EffectiveIteration.sourceDepth n)).budget 0
            (Iteration.seedState (EffectiveIteration.sourceDepth n)).matrix)
          0 0 0 0 []
          (MatrixMaterialization.rowMajor
            (ProtectedFullBankBridgeScratch.actualF G c (EffectiveIteration.sourceDepth n)
              (Iteration.seedState (EffectiveIteration.sourceDepth n)).budget 0
              (Iteration.seedState (EffectiveIteration.sourceDepth n)).matrix))).contents := hw
  have hG : ∀ k, (ProtectedFullBankBridgeScratch.actualWriterStart G c
      (EffectiveIteration.sourceDepth n)
      (Iteration.seedState (EffectiveIteration.sourceDepth n)).budget 0
      (Iteration.seedState (EffectiveIteration.sourceDepth n)).matrix).stk k = S (wEmb k) := by
    intro k
    by_cases hk : k = .inl (.inl 22)
    · subst hk
      rw [writer_start_22, h22]
    · rw [hS k hk, ready_writer M G n c F Q P hf k hk]
  have r := WeightedRawWords.region_run wEmb MatrixWeightedOrderWriter.program _ _ tw hrun S hG
  exact ⟨tw, htw, w, r⟩

#print axioms writer_start_22
#print axioms level0_writer_run

end
end EthInapproximability.CurrentPaper.WeightedLevel0WriterRun
