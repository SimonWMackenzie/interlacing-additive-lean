import EthInapproximability.CurrentPaper.SourceClausePrefixUnitCycle

namespace EthInapproximability.CurrentPaper.SourceBooleanPrefix.PrefixGateCycle

open Turing BitMachineEncoding BitMachineStackEmbedding
open SourceBooleanEncoding
open scoped Classical

noncomputable def gateControl :=
  (((false, (SourceLabelAddressMachine.counter.initial, (none : Option Bool))),
      ((), (none : Option Bool))),
    ((false, ((), (none : Option Bool))),
      (((false, (SourceLabelAddressMachine.counter.initial, (none : Option Bool))),
          ((), (none : Option Bool))),
        ((((), (none : Option Bool)), (none : Option Bool)),
          SourceClauseGateMachine.control))))

noncomputable def pairProgram (s w : ℕ) :=
  BitMachineRawSequence.program
    (PrefixGateOperands.preparationProgram s w)
    PrefixSharedGate.program
    (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel
        (BitMachineRawSequence.leftLabel
          MatrixAddressMachine.Label.outer)))
    ((), ((), none)) gateControl

theorem pair_run {n q : ℕ} (v : Fin n) (s : Fin 2)
    (saved output count : List Bool) :
    ∃ t ≤ PrefixGateOperands.preparationCost s.val (width 2 q + 1)
        (List.replicate v.val true) +
        SourceClauseRowGate.cost v.val 2 s.val n s.val v.val
          (width 2 q + 1) true + 1,
      ((advance (pairProgram s.val (width 2 q + 1)))^[t])
        (⟨some (BitMachineRawSequence.leftLabel
            (BitMachineRawSequence.leftLabel
              (SourceClauseFixedBatch.labelAt
                (PrefixGateOperands.constantSize s.val (width 2 q + 1)) 0))),
          (((), ((), none)), gateControl),
          PrefixGateReady.blank n v.val saved output count⟩) =
        ⟨none, (((), ((), none)), gateControl),
          bank PrefixSharedCore.gateEmbedding
            (PrefixGateReady.prepared (q := q) v s saved output count)
            (SourceClauseRowGate.finalBank (0 : Fin 1) (vertexFrame v)
              v.val 2 s.val n s.val v.val (width 2 q + 1) true
              saved output count)⟩ := by
  let B := PrefixGateReady.blank n v.val saved output count
  let P := PrefixGateReady.prepared (q := q) v s saved output count
  let F := bank PrefixSharedCore.gateEmbedding P
    (SourceClauseRowGate.finalBank (0 : Fin 1) (vertexFrame v)
      v.val 2 s.val n s.val v.val (width 2 q + 1) true
      saved output count)
  obtain ⟨a, ha, hA⟩ := PrefixGateReady.prepared_run (q := q) v s
    saved output count
  obtain ⟨b, hb, hB⟩ := PrefixSharedGate.run (q := q) v s
    saved output count P
  have hP : bank PrefixSharedCore.gateEmbedding P
      (SourceClauseRowGate.initial (vertexFrame v)
        v.val 2 s.val n s.val v.val (width 2 q + 1)
        saved output count) = P := by
    apply bank_eq_self
    intro x
    exact (PrefixGateReady.gate_ready (q := q) v s
      saved output count x).symm
  have hB' :
      ((advance PrefixSharedGate.program)^[b])
        (⟨some (BitMachineRawSequence.leftLabel
          (BitMachineRawSequence.leftLabel
            (BitMachineRawSequence.leftLabel
              MatrixAddressMachine.Label.outer))), gateControl, P⟩) =
        ⟨none, gateControl, F⟩ := by
    simpa only [stackCfg, gateControl, hP] using hB
  obtain ⟨t, ht, h⟩ := BitMachineRawSequence.runs
    (PrefixGateOperands.preparationProgram s.val (width 2 q + 1))
    PrefixSharedGate.program
    (BitMachineRawSequence.leftLabel
      (SourceClauseFixedBatch.labelAt
        (PrefixGateOperands.constantSize s.val (width 2 q + 1)) 0))
    (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel
        (BitMachineRawSequence.leftLabel
          MatrixAddressMachine.Label.outer)))
    ((), ((), none)) ((), ((), none)) gateControl gateControl
    B P F a b hA hB'
  exact ⟨t, by omega, h⟩

noncomputable def program (s w : ℕ) :=
  BitMachineRawSequence.program (pairProgram s w)
    PrefixSharedClear.program (.clear 0)
    (((), ((), none)), gateControl) ((), none)

theorem run {n q : ℕ} (v : Fin n) (s : Fin 2)
    (saved output count : List Bool) :
    ∃ t ≤ PrefixGateOperands.preparationCost s.val (width 2 q + 1)
        (List.replicate v.val true) +
        SourceClauseRowGate.cost v.val 2 s.val n s.val v.val
          (width 2 q + 1) true + 1 +
        PrefixSharedClear.cost
          (bank PrefixSharedCore.gateEmbedding
            (PrefixGateReady.prepared (q := q) v s saved output count)
            (SourceClauseRowGate.finalBank (0 : Fin 1) (vertexFrame v)
              v.val 2 s.val n s.val v.val (width 2 q + 1) true
              saved output count)) + 1,
      ((advance (program s.val (width 2 q + 1)))^[t])
        (⟨some (BitMachineRawSequence.leftLabel
            (BitMachineRawSequence.leftLabel
              (BitMachineRawSequence.leftLabel
                (SourceClauseFixedBatch.labelAt
                  (PrefixGateOperands.constantSize s.val (width 2 q + 1)) 0)))),
          ((((), ((), none)), gateControl), ((), none)),
          PrefixGateReady.blank n v.val saved output count⟩) =
        ⟨none, ((((), ((), none)), gateControl), ((), none)),
          PrefixGateReady.blank n v.val
            (PrefixSharedGateHandoff.nextSaved (q := q) v s saved)
            output (true :: true :: true :: count)⟩ := by
  let B := PrefixGateReady.blank n v.val saved output count
  let P := PrefixGateReady.prepared (q := q) v s saved output count
  let F := bank PrefixSharedCore.gateEmbedding P
    (SourceClauseRowGate.finalBank (0 : Fin 1) (vertexFrame v)
      v.val 2 s.val n s.val v.val (width 2 q + 1) true
      saved output count)
  obtain ⟨a, ha, hA⟩ := pair_run (q := q) v s saved output count
  have hB :
      ((advance PrefixSharedClear.program)^[PrefixSharedClear.cost F])
        (⟨some (.clear 0), ((), none), F⟩) =
        ⟨none, ((), none), PrefixGateReady.blank n v.val
          (PrefixSharedGateHandoff.nextSaved (q := q) v s saved)
          output (true :: true :: true :: count)⟩ := by
    rw [PrefixSharedClear.run]
    rw [show SourceClauseClearExcept.result PrefixSharedClear.keep F =
      PrefixGateReady.blank n v.val
        (PrefixSharedGateHandoff.nextSaved (q := q) v s saved)
        output (true :: true :: true :: count) from
      PrefixSharedGateHandoff.after_clear v s saved output count P]
  obtain ⟨t, ht, h⟩ := BitMachineRawSequence.runs
    (pairProgram s.val (width 2 q + 1)) PrefixSharedClear.program
    (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel
        (SourceClauseFixedBatch.labelAt
          (PrefixGateOperands.constantSize s.val (width 2 q + 1)) 0)))
    (.clear 0) (((), ((), none)), gateControl)
    (((), ((), none)), gateControl) ((), none) ((), none)
    B F (PrefixGateReady.blank n v.val
      (PrefixSharedGateHandoff.nextSaved (q := q) v s saved)
      output (true :: true :: true :: count))
    a (PrefixSharedClear.cost F) hA hB
  refine ⟨t, ?_, h⟩
  change t ≤ PrefixGateOperands.preparationCost s.val (width 2 q + 1)
      (List.replicate v.val true) +
    SourceClauseRowGate.cost v.val 2 s.val n s.val v.val
      (width 2 q + 1) true + 1 + PrefixSharedClear.cost F + 1
  omega

end EthInapproximability.CurrentPaper.SourceBooleanPrefix.PrefixGateCycle

#print axioms EthInapproximability.CurrentPaper.SourceBooleanPrefix.PrefixGateCycle.run
