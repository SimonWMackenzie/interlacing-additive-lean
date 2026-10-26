import EthInapproximability.CurrentPaper.EntryPrepPow

/-!
# Segment 5/6 status composition: `Writer22Spec` from `Family5Spec` alone

Lane owner:b-stage4-entry-program-7 (Paper B, unit 2, map item 3).

`prepProg W = progA ; (progV ; (progC ; W))` (all fixed, uniform in `G, n, c` once `W` is).
`prep_of_family5`: `EntryTailClear.PrepSpec (prepProg W)` from `Family5Spec W`.
`level0_writer22_of_family5`: the admitted target `OuterLevel0Full.Writer22Spec` for
`seedProgram ; (prepProg W ; tailClear)` from `Family5Spec W` alone.
-/

namespace EthInapproximability.CurrentPaper.EntryPrepVec

set_option synthInstance.maxSize 200000
set_option synthInstance.maxHeartbeats 2000000
set_option maxRecDepth 16384

open Turing BitMachineEncoding BitMachineStackEmbedding
open EthInapproximability.ParameterizedNP.GuardedSourceGraph
open WeightedLevel0Rows WeightedLevel0Persist WeightedLevel0Clean WeightedLevel0Ready OuterLevel0Prep
open EntryPrepBudget EntryTailEmbed EntryTailClear EntryPrepCopy

noncomputable def prepProg {LW VW : Type} (W : LW → TM2.Stmt (fun _ : HStack => Bool) LW VW)
    (w₀ : LW) (v₀ : VW) :=
  BitMachineRawSequence.program progA
    (BitMachineRawSequence.program progV
      (BitMachineRawSequence.program progC W w₀ MultiMove.initial v₀)
      (BitMachineRawSequence.leftLabel (MultiMove.startLabel (jobs9.map CopyFill.toJob)))
      initV (MultiMove.initial, v₀))
    (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel
      (MultiMove.startLabel (jobs1.map CopyFill.toJob))))
    (MultiMove.initial, DerivedScalars.initial) (initV, (MultiMove.initial, v₀))

noncomputable def prepInit {VW : Type} (v₀ : VW) :=
  ((MultiMove.initial, DerivedScalars.initial), (initV, (MultiMove.initial, v₀)))

variable (Mm : BitMachine.Machine)
variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

noncomputable def prepBound (G : EndpointGraph V E) (n c T : ℕ) : ℕ :=
  boundA G n c + (boundV G n c + ((((2 * (EntryLevelWords.w0 G n c).wordB + 2) + 0) + 1) + T + 1)
    + 1) + 1

theorem prep_of_family5 (G : EndpointGraph V E) (n c : ℕ) {LW VW : Type}
    (W : LW → TM2.Stmt (fun _ : HStack => Bool) LW VW) (w₀ : LW) (v₀ : VW) (T : ℕ)
    (hF : Family5Spec Mm W w₀ v₀ T G n c) :
    PrepSpec Mm (prepProg W w₀ v₀) (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel
        (MultiMove.startLabel (copyJobs.map CopyFill.toJob)))) (prepInit v₀) (prepBound G n c T) G n c :=
  prep_of_family Mm G n c _ _ _ _ (family_of_family5 Mm G n c W w₀ v₀ T hF)

theorem level0_writer22_of_family5 (G : EndpointGraph V E) (n c : ℕ) {LW VW : Type}
    (W : LW → TM2.Stmt (fun _ : HStack => Bool) LW VW) (w₀ : LW) (v₀ : VW) (T : ℕ)
    (hF : Family5Spec Mm W w₀ v₀ T G n c) :
    OuterLevel0Full.Writer22Spec Mm
      (BitMachineRawSequence.program EntrySeedSpec.seedProgram
        (BitMachineRawSequence.program (prepProg W w₀ v₀) tailClear
          (BitMachineRawSequence.leftLabel RawTableTail.startLabel) (prepInit v₀)
          (RawTableTail.startControl EntryRunsRaw.startControl, ((), (none : Option Bool))))
        (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel
        (MultiMove.startLabel (copyJobs.map CopyFill.toJob)))))
        ((none : Option Bool), (none : Option Bool))
        (prepInit v₀, (RawTableTail.startControl EntryRunsRaw.startControl,
          ((), (none : Option Bool)))))
      (BitMachineRawSequence.leftLabel SeedTable.startLabel)
      (((none : Option Bool), (none : Option Bool)),
        (prepInit v₀, (RawTableTail.startControl EntryRunsRaw.startControl,
          ((), (none : Option Bool)))))
      (SeedTable.bound (IndexSeed.width (EffectiveIteration.sourceDepth n)) +
        (prepBound G n c T + (tailBound G n c + clearBound G n c + 1) + 1) + 1) G n c :=
  level0_writer22_of_prep Mm G n c _ _ _ _ (prep_of_family5 Mm G n c W w₀ v₀ T hF)

#print axioms prep_of_family5
#print axioms level0_writer22_of_family5

end EthInapproximability.CurrentPaper.EntryPrepVec
