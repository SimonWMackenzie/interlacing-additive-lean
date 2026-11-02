import EthInapproximability.CurrentPaper.SourceClausePrefixGateClean

/-!
One at-least OR gate and a physical scratch clear, in one controller. Its
initial row query and duplicated unary operands are still supplied; this is
not the four-stage exact-one callback.
-/

namespace EthInapproximability.CurrentPaper.SourceBooleanPrefix.PrefixGateCleanRun

open Turing BitMachineEncoding
open SourceBooleanEncoding

abbrev Stack := SourceClauseRowGate.Stack 1

abbrev GateControl := BitMachineRawSequence.Control
  (BitMachineRawSequence.Control
    (BitMachineRawSequence.Control Bool
      (BitMachineIteration.Control SourceLabelAddressMachine.counter))
    (Unit × Option Bool))
  (BitMachineRawSequence.Control
    (BitMachineRawSequence.Control Bool (Unit × Option Bool))
    (BitMachineRawSequence.Control
      (BitMachineRawSequence.Control
        (BitMachineRawSequence.Control Bool
          (BitMachineIteration.Control SourceLabelAddressMachine.counter))
        (Unit × Option Bool))
      (BitMachineRawSequence.Control
        (BitMachineRawSequence.Control (Unit × Option Bool) (Option Bool))
        (BitMachineRawSequence.Control
          (BitMachineRawSequence.Control
            (BitMachineRawSequence.Control (Unit × Option Bool)
              (Unit × Option Bool))
            (Unit × Option Bool))
          SourceClauseGateMachine.EmitControl))))

noncomputable def gateControl : GateControl :=
  (((false, (SourceLabelAddressMachine.counter.initial, none)),
      ((), none)),
    ((false, ((), none)),
      (((false, (SourceLabelAddressMachine.counter.initial, none)),
          ((), none)),
        ((((), none), none), SourceClauseGateMachine.control))))

noncomputable def program :=
  BitMachineRawSequence.program
    (SourceClauseRowGate.program (0 : Fin 1) true)
    (SourceClauseClearExcept.program PrefixGateClean.keep)
    (SourceClauseClearExcept.Label.clear 0)
    gateControl ((), none)

noncomputable def cost {n q : ℕ} (v : Fin n) (s : Fin 2)
    (savedBits outputBits countBits : List Bool) : ℕ :=
  SourceClauseRowGate.cost v.val 2 s.val n s.val v.val
      (width 2 q + 1) true +
    PrefixGateClean.clearCost
      (SourceClauseRowGate.finalBank (0 : Fin 1) (vertexFrame v)
        v.val 2 s.val n s.val v.val (width 2 q + 1)
        true savedBits outputBits countBits) + 1

theorem run {n q : ℕ} (v : Fin n) (s : Fin 2)
    (savedBits outputBits countBits : List Bool) :
    ∃ T ≤ cost (q := q) v s savedBits outputBits countBits,
      ((advance program)^[T])
        (⟨some (BitMachineRawSequence.leftLabel
          (BitMachineRawSequence.leftLabel
            (BitMachineRawSequence.leftLabel
              (BitMachineRawSequence.leftLabel
                MatrixAddressMachine.Label.outer)))),
          (gateControl, ((), none)),
          SourceClauseRowGate.initial (vertexFrame v) v.val 2 s.val n s.val
            v.val (width 2 q + 1) savedBits outputBits countBits⟩) =
        ⟨none, (gateControl, ((), none)),
          PrefixGateClean.clean
            (SourceClauseRowGate.finalBank (0 : Fin 1) (vertexFrame v)
              v.val 2 s.val n s.val v.val (width 2 q + 1) true
              savedBits outputBits countBits)⟩ := by
  obtain ⟨tg, htg, hg⟩ := atLeast_gate_run (q := q) v s
    savedBits outputBits countBits
  have hc := PrefixGateClean.clear_run
    (SourceClauseRowGate.finalBank (0 : Fin 1) (vertexFrame v)
      v.val 2 s.val n s.val v.val (width 2 q + 1)
      true savedBits outputBits countBits)
  obtain ⟨T, hT, hr⟩ := BitMachineRawSequence.runs
    (SourceClauseRowGate.program (0 : Fin 1) true)
    (SourceClauseClearExcept.program PrefixGateClean.keep)
    (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel
        (BitMachineRawSequence.leftLabel MatrixAddressMachine.Label.outer)))
    (SourceClauseClearExcept.Label.clear 0)
    gateControl gateControl ((), none) ((), none)
    (SourceClauseRowGate.initial (vertexFrame v) v.val 2 s.val n s.val
      v.val (width 2 q + 1) savedBits outputBits countBits)
    (SourceClauseRowGate.finalBank (0 : Fin 1) (vertexFrame v)
      v.val 2 s.val n s.val v.val (width 2 q + 1)
      true savedBits outputBits countBits)
    (PrefixGateClean.clean
      (SourceClauseRowGate.finalBank (0 : Fin 1) (vertexFrame v)
        v.val 2 s.val n s.val v.val (width 2 q + 1)
        true savedBits outputBits countBits))
    tg _ hg hc
  exact ⟨T, by dsimp [cost] at *; omega,
    by simpa only [program, gateControl] using hr⟩

end EthInapproximability.CurrentPaper.SourceBooleanPrefix.PrefixGateCleanRun
