import EthInapproximability.CurrentPaper.SourceClausePrefixResumePieces

namespace EthInapproximability.CurrentPaper.SourceBooleanPrefix.PrefixUnitCycle

open Turing BitMachineEncoding BitMachineStackEmbedding
open scoped Classical

noncomputable def program (w ell : ℕ) (sign : Bool) :=
  BitMachineRawSequence.program
    (PrefixSharedUnitPair.program w ell sign)
    PrefixSharedClear.program
    (.clear 0) ((), PrefixUnitRun.startControl) ((), none)

theorem run (n ordinal w ell : ℕ) (sign : Bool)
    (saved output count : List Bool) :
    ∃ t ≤ (SourceClauseFixedBatch.costPrefix
          (PrefixUnitClean.constantSize w ell) 3 + 1) +
        PrefixUnitRun.cost n ordinal w ell + 1 +
        PrefixSharedClear.cost
          (bank PrefixSharedCore.unitEmbedding
            (PrefixGateReady.blank n ordinal saved output count)
            (PrefixUnitRun.finished n ordinal w ell sign
              saved output count)) + 1,
      ((advance (program w ell sign))^[t])
        (⟨some (BitMachineRawSequence.leftLabel
            (BitMachineRawSequence.leftLabel
              (SourceClauseFixedBatch.labelAt
                (PrefixUnitClean.constantSize w ell) 0))),
          (((), PrefixUnitRun.startControl), ((), none)),
          PrefixGateReady.blank n ordinal saved output count⟩) =
        ⟨none, (((), PrefixUnitRun.startControl), ((), none)),
          PrefixGateReady.blank n ordinal
            (PrefixSharedUnitHandoff.nextSaved n ordinal w ell sign saved)
            output (true :: count)⟩ := by
  let B := PrefixGateReady.blank n ordinal saved output count
  let F := bank PrefixSharedCore.unitEmbedding B
    (PrefixUnitRun.finished n ordinal w ell sign saved output count)
  obtain ⟨a, ha, hA⟩ := PrefixSharedUnitPair.run n ordinal w ell sign
    saved output count
  have hA' :
      ((advance (PrefixSharedUnitPair.program w ell sign))^[a])
        (⟨some (BitMachineRawSequence.leftLabel
          (SourceClauseFixedBatch.labelAt
            (PrefixUnitClean.constantSize w ell) 0)),
          ((), PrefixUnitRun.startControl), B⟩) =
        ⟨none, ((), PrefixUnitRun.startControl), F⟩ := hA
  have hB' :
      ((advance PrefixSharedClear.program)^[PrefixSharedClear.cost F])
        (⟨some (.clear 0), ((), none), F⟩) =
        ⟨none, ((), none), PrefixGateReady.blank n ordinal
          (PrefixSharedUnitHandoff.nextSaved n ordinal w ell sign saved)
          output (true :: count)⟩ := by
    rw [PrefixSharedClear.run]
    rw [show SourceClauseClearExcept.result PrefixSharedClear.keep F =
      PrefixGateReady.blank n ordinal
        (PrefixSharedUnitHandoff.nextSaved n ordinal w ell sign saved)
        output (true :: count) from
      PrefixSharedUnitHandoff.after_clear n ordinal w ell sign
        saved output count B]
  obtain ⟨t, ht, h⟩ := BitMachineRawSequence.runs
    (PrefixSharedUnitPair.program w ell sign) PrefixSharedClear.program
    (BitMachineRawSequence.leftLabel
      (SourceClauseFixedBatch.labelAt
        (PrefixUnitClean.constantSize w ell) 0))
    (.clear 0) ((), PrefixUnitRun.startControl)
    ((), PrefixUnitRun.startControl) ((), none) ((), none)
    B F (PrefixGateReady.blank n ordinal
      (PrefixSharedUnitHandoff.nextSaved n ordinal w ell sign saved)
      output (true :: count))
    a (PrefixSharedClear.cost F) hA' hB'
  refine ⟨t, ?_, h⟩
  change t ≤ (SourceClauseFixedBatch.costPrefix
      (PrefixUnitClean.constantSize w ell) 3 + 1) +
    PrefixUnitRun.cost n ordinal w ell + 1 +
    PrefixSharedClear.cost F + 1
  omega

end EthInapproximability.CurrentPaper.SourceBooleanPrefix.PrefixUnitCycle

#print axioms EthInapproximability.CurrentPaper.SourceBooleanPrefix.PrefixUnitCycle.run
