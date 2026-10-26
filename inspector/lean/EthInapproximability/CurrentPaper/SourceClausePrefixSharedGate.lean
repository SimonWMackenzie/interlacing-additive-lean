import EthInapproximability.CurrentPaper.SourceClausePrefixSharedUnit
import EthInapproximability.CurrentPaper.SourceClausePrefixGate

/-! The actual at-least OR-gate routine embedded into the shared prefix bank. -/

namespace EthInapproximability.CurrentPaper.SourceBooleanPrefix.PrefixSharedGate

open Turing BitMachineEncoding BitMachineStackEmbedding
open SourceBooleanEncoding
open scoped Classical

noncomputable def program :=
  PrefixSharedExecution.liftedProgram PrefixSharedCore.gateEmbedding
    (SourceClauseRowGate.program (0 : Fin 1) true)

theorem run {n q : ℕ} (v : Fin n) (s : Fin 2)
    (saved output count : List Bool)
    (foreign : PrefixSharedCore.Stack → List Bool) :
    ∃ t ≤ SourceClauseRowGate.cost v.val 2 s.val n s.val v.val
        (width 2 q + 1) true,
      ((advance program)^[t])
        (stackCfg PrefixSharedCore.gateEmbedding foreign
          ⟨some (BitMachineRawSequence.leftLabel
            (BitMachineRawSequence.leftLabel
              (BitMachineRawSequence.leftLabel
                MatrixAddressMachine.Label.outer))),
            (((false, (SourceLabelAddressMachine.counter.initial, none)),
                ((), none)),
              ((false, ((), none)),
                (((false, (SourceLabelAddressMachine.counter.initial, none)),
                    ((), none)),
                  ((((), none), none), SourceClauseGateMachine.control)))),
            SourceClauseRowGate.initial (vertexFrame v) v.val 2 s.val n s.val
              v.val (width 2 q + 1) saved output count⟩) =
        stackCfg PrefixSharedCore.gateEmbedding foreign
          ⟨none,
            (((false, (SourceLabelAddressMachine.counter.initial, none)),
                ((), none)),
              ((false, ((), none)),
                (((false, (SourceLabelAddressMachine.counter.initial, none)),
                    ((), none)),
                  ((((), none), none), SourceClauseGateMachine.control)))),
            SourceClauseRowGate.finalBank (0 : Fin 1) (vertexFrame v)
              v.val 2 s.val n s.val v.val (width 2 q + 1) true
              saved output count⟩ := by
  obtain ⟨t, ht, hrun⟩ := atLeast_gate_run (q := q) v s
    saved output count
  obtain ⟨u, hu, h⟩ := PrefixSharedExecution.lifted_run
    PrefixSharedCore.gateEmbedding foreign
    (SourceClauseRowGate.program (0 : Fin 1) true) _ _ t hrun rfl
  exact ⟨u, hu.trans ht, h⟩

end EthInapproximability.CurrentPaper.SourceBooleanPrefix.PrefixSharedGate
