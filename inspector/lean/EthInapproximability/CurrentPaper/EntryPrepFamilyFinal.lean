import EthInapproximability.CurrentPaper.EntryPrepFamilyRun

/-!
# Lane owner:b-stage4-entry-program-8: `OuterLevel0Full.Writer22Spec`, no remaining premise

`level0_writer22` instantiates owner-7's frozen `EntryPrepVec.level0_writer22_of_family4` (admitted
by the root as `EntryPrepFinal4`, batch wave12-b22; imported here as the frozen object `P7Final4`)
with this lane's fixed program `progF` and its discharged interface `family4`. The program
`seedProgram ; (progA ; (progV ; (progC ; (progL ; progF))) ; tailClear)` does not depend on
`G, n, c`; the clock is the public expression below.
-/

namespace EthInapproximability.CurrentPaper.EntryPrepFamily

set_option synthInstance.maxSize 200000
set_option synthInstance.maxHeartbeats 2000000
set_option maxRecDepth 16384

open Turing BitMachineEncoding BitMachineStackEmbedding
open EthInapproximability.ParameterizedNP.GuardedSourceGraph
open WeightedLevel0Rows WeightedLevel0Persist WeightedLevel0Clean WeightedLevel0Ready OuterLevel0Prep
open EntryPrepBudget EntryTailEmbed EntryTailClear EntryPrepCopy EntryPrepVec

variable (Mm : BitMachine.Machine)
variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

theorem level0_writer22 (G : EndpointGraph V E) (n c : ℕ) :
    OuterLevel0Full.Writer22Spec Mm
      (BitMachineRawSequence.program EntrySeedSpec.seedProgram
        (BitMachineRawSequence.program
          (prepProg4 progF
            (BitMachineRawSequence.leftLabel (MultiMove.startLabel (jobsA.map CopyFill.toJob)))
            (MultiMove.initial, ((), (MultiMove.initial, (EntryFamilyLevel.initialControl,
              (MultiMove.initial, ((none : Option Bool), ((), (none : Option Bool)))))))))
          tailClear
          (BitMachineRawSequence.leftLabel RawTableTail.startLabel)
          (prepInit ((MultiMove.initial, false),
            (MultiMove.initial, ((), (MultiMove.initial, (EntryFamilyLevel.initialControl,
              (MultiMove.initial, ((none : Option Bool), ((), (none : Option Bool))))))))))
          (RawTableTail.startControl EntryRunsRaw.startControl, ((), (none : Option Bool))))
        (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel
          (BitMachineRawSequence.leftLabel (MultiMove.startLabel (copyJobs.map CopyFill.toJob)))))
        ((none : Option Bool), (none : Option Bool))
        (prepInit ((MultiMove.initial, false),
            (MultiMove.initial, ((), (MultiMove.initial, (EntryFamilyLevel.initialControl,
              (MultiMove.initial, ((none : Option Bool), ((), (none : Option Bool))))))))),
          (RawTableTail.startControl EntryRunsRaw.startControl, ((), (none : Option Bool)))))
      (BitMachineRawSequence.leftLabel SeedTable.startLabel)
      (((none : Option Bool), (none : Option Bool)),
        (prepInit ((MultiMove.initial, false),
            (MultiMove.initial, ((), (MultiMove.initial, (EntryFamilyLevel.initialControl,
              (MultiMove.initial, ((none : Option Bool), ((), (none : Option Bool))))))))),
          (RawTableTail.startControl EntryRunsRaw.startControl, ((), (none : Option Bool)))))
      (SeedTable.bound (IndexSeed.width (EffectiveIteration.sourceDepth n)) +
        (prepBound G n c (labBound G n c (TF G n c)) + (tailBound G n c + clearBound G n c + 1) + 1) + 1)
      G n c :=
  level0_writer22_of_family4 Mm G n c progF _ _ (TF G n c) (family4 Mm G n c)

#print axioms level0_writer22

end EthInapproximability.CurrentPaper.EntryPrepFamily
