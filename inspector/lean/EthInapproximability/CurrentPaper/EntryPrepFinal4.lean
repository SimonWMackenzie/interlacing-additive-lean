import EthInapproximability.CurrentPaper.EntryPrepLab

/-!
# `PrepSpec` and `Writer22Spec` from `Family4Spec` alone (cw 4, 5, 8, 11)

Lane owner:b-stage4-entry-program-7 (Paper B, unit 2, map item 3).
-/

namespace EthInapproximability.CurrentPaper.EntryPrepVec

set_option synthInstance.maxSize 200000
set_option synthInstance.maxHeartbeats 2000000
set_option maxRecDepth 16384

open Turing BitMachineEncoding BitMachineStackEmbedding
open EthInapproximability.ParameterizedNP.GuardedSourceGraph
open WeightedLevel0Rows WeightedLevel0Persist WeightedLevel0Clean WeightedLevel0Ready OuterLevel0Prep
open EntryPrepBudget EntryTailEmbed EntryTailClear EntryPrepCopy

/-- `progA ; (progV ; (progC ; (progL ; W)))`. -/
noncomputable def prepProg4 {LW VW : Type} (W : LW → TM2.Stmt (fun _ : HStack => Bool) LW VW)
    (w₀ : LW) (v₀ : VW) :=
  prepProg (BitMachineRawSequence.program progL W w₀ (MultiMove.initial, false) v₀)
    (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel (MultiMove.startLabel (jobsL.map CopyFill.toJob))))
    ((MultiMove.initial, false), v₀)

variable (Mm : BitMachine.Machine)
variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

noncomputable def labBound (G : EndpointGraph V E) (n c T : ℕ) : ℕ :=
  (((2 * (EntryLevelWords.w0 G n c).sL + 2) + 0 + 1) +
    MatrixUnaryDivision.exactTime (EntryLevelWords.w0 G n c).sL (EntryLevelWords.w0 G n c).s + 1)
    + T + 1

theorem prep_of_family4 (G : EndpointGraph V E) (n c : ℕ) {LW VW : Type}
    (W : LW → TM2.Stmt (fun _ : HStack => Bool) LW VW) (w₀ : LW) (v₀ : VW) (T : ℕ)
    (hF : Family4Spec Mm W w₀ v₀ T G n c) :
    PrepSpec Mm (prepProg4 W w₀ v₀)
      (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel
        (MultiMove.startLabel (copyJobs.map CopyFill.toJob))))
      (prepInit ((MultiMove.initial, false), v₀)) (prepBound G n c (labBound G n c T)) G n c :=
  prep_of_family5 Mm G n c _ _ _ _ (family5_of_family4 Mm G n c W w₀ v₀ T hF)

theorem level0_writer22_of_family4 (G : EndpointGraph V E) (n c : ℕ) {LW VW : Type}
    (W : LW → TM2.Stmt (fun _ : HStack => Bool) LW VW) (w₀ : LW) (v₀ : VW) (T : ℕ)
    (hF : Family4Spec Mm W w₀ v₀ T G n c) :
    OuterLevel0Full.Writer22Spec Mm
      (BitMachineRawSequence.program EntrySeedSpec.seedProgram
        (BitMachineRawSequence.program (prepProg4 W w₀ v₀) tailClear
          (BitMachineRawSequence.leftLabel RawTableTail.startLabel)
          (prepInit ((MultiMove.initial, false), v₀))
          (RawTableTail.startControl EntryRunsRaw.startControl, ((), (none : Option Bool))))
        (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel
          (BitMachineRawSequence.leftLabel (MultiMove.startLabel (copyJobs.map CopyFill.toJob)))))
        ((none : Option Bool), (none : Option Bool))
        (prepInit ((MultiMove.initial, false), v₀),
          (RawTableTail.startControl EntryRunsRaw.startControl, ((), (none : Option Bool)))))
      (BitMachineRawSequence.leftLabel SeedTable.startLabel)
      (((none : Option Bool), (none : Option Bool)),
        (prepInit ((MultiMove.initial, false), v₀),
          (RawTableTail.startControl EntryRunsRaw.startControl, ((), (none : Option Bool)))))
      (SeedTable.bound (IndexSeed.width (EffectiveIteration.sourceDepth n)) +
        (prepBound G n c (labBound G n c T) + (tailBound G n c + clearBound G n c + 1) + 1) + 1)
      G n c :=
  level0_writer22_of_prep Mm G n c _ _ _ _ (prep_of_family4 Mm G n c W w₀ v₀ T hF)

#print axioms prep_of_family4
#print axioms level0_writer22_of_family4

end EthInapproximability.CurrentPaper.EntryPrepVec
