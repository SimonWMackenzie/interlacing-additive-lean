import EthInapproximability.CurrentPaper.SourceClausePrefixSharedExecution

/-! The actual opening/closing unit routine, embedded into the shared prefix bank. -/

namespace EthInapproximability.CurrentPaper.SourceBooleanPrefix.PrefixSharedUnit

open Turing BitMachineEncoding BitMachineStackEmbedding
open scoped Classical

noncomputable def program (sign : Bool) :=
  PrefixSharedExecution.liftedProgram PrefixSharedCore.unitEmbedding
    (PrefixUnitRun.program sign)

theorem run (n ordinal w ell : ℕ) (sign : Bool)
    (saved output count : List Bool)
    (foreign : PrefixSharedCore.Stack → List Bool) :
    ∃ t ≤ PrefixUnitRun.cost n ordinal w ell,
      ((advance (program sign))^[t])
        (stackCfg PrefixSharedCore.unitEmbedding foreign
          ⟨some (BitMachineRawSequence.leftLabel
            (BitMachineRawSequence.leftLabel
              (BitMachineRawSequence.leftLabel
                (BitMachineRawSequence.leftLabel
                  MatrixAddressMachine.Label.outer)))),
            PrefixUnitRun.startControl,
            PrefixUnitRun.initial n ordinal w ell saved output count⟩) =
        stackCfg PrefixSharedCore.unitEmbedding foreign
          ⟨none, PrefixUnitRun.startControl,
            PrefixUnitRun.finished n ordinal w ell sign saved output count⟩ := by
  obtain ⟨t, ht, hrun⟩ := PrefixUnitRun.run n ordinal w ell sign
    saved output count
  obtain ⟨u, hu, h⟩ := PrefixSharedExecution.lifted_run
    PrefixSharedCore.unitEmbedding foreign (PrefixUnitRun.program sign)
    _ _ t hrun rfl
  exact ⟨u, hu.trans ht, h⟩

end EthInapproximability.CurrentPaper.SourceBooleanPrefix.PrefixSharedUnit
