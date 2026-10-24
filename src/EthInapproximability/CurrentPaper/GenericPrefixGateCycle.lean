import EthInapproximability.CurrentPaper.GenericPrefixGateHandoff

namespace EthInapproximability.CurrentPaper.SourceGenericPrefixMachine.GateCycle

open Turing BitMachineEncoding BitMachineStackEmbedding
open SourceBooleanEncoding SourceBooleanPrefix
open scoped Classical

noncomputable def gateControl := PrefixGateCycle.gateControl

noncomputable def pairProgram (a s w : Nat) :=
  BitMachineRawSequence.program
    (GateOperands.program a s w)
    PrefixSharedGate.program
    (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel
        (BitMachineRawSequence.leftLabel
          MatrixAddressMachine.Label.outer)))
    ((),((),none)) gateControl

theorem pair_run {n a q : Nat} (v : Fin n) (s : Fin a)
    (saved output count : List Bool) :
    ∃ t ≤ GateOperands.cost a s.val (width a q + 1)
        (List.replicate v.val true) +
        SourceClauseRowGate.cost v.val a s.val n s.val v.val
          (width a q + 1) true + 1,
      ((advance (pairProgram a s.val (width a q + 1)))^[t])
        (⟨some (BitMachineRawSequence.leftLabel
          (BitMachineRawSequence.leftLabel
            (SourceClauseFixedBatch.labelAt
              (GateOperands.constantSize a s.val (width a q + 1)) 0))),
          (((),((),none)),gateControl),
          PrefixGateReady.blank n v.val saved output count⟩) =
        ⟨none,(((),((),none)),gateControl),
          bank PrefixSharedCore.gateEmbedding
            (GateReady.prepared v s (width a q + 1)
              saved output count)
            (SourceClauseRowGate.finalBank (0 : Fin 1) (vertexFrame v)
              v.val a s.val n s.val v.val (width a q + 1) true
              saved output count)⟩ := by
  let B := PrefixGateReady.blank n v.val saved output count
  let P := GateReady.prepared v s (width a q + 1) saved output count
  let F := bank PrefixSharedCore.gateEmbedding P
    (SourceClauseRowGate.finalBank (0 : Fin 1) (vertexFrame v)
      v.val a s.val n s.val v.val (width a q + 1) true
      saved output count)
  obtain ⟨u,hu,hU⟩ := GateReady.prepared_run v s (width a q + 1)
    saved output count
  obtain ⟨b,hb,hB⟩ := GateSemantic.run (q := q) v s v.val s.val true
    saved output count
  obtain ⟨c,hc,hC⟩ := PrefixSharedExecution.lifted_run
    PrefixSharedCore.gateEmbedding P
    (SourceClauseRowGate.program (0 : Fin 1) true) _ _ b hB rfl
  have hP : bank PrefixSharedCore.gateEmbedding P
      (SourceClauseRowGate.initial (vertexFrame v)
        v.val a s.val n s.val v.val (width a q + 1)
        saved output count) = P := by
    apply bank_eq_self
    intro x
    exact (GateReady.gate_ready v s (width a q + 1)
      saved output count x).symm
  have hC' :
      ((advance PrefixSharedGate.program)^[c])
        (⟨some (BitMachineRawSequence.leftLabel
          (BitMachineRawSequence.leftLabel
            (BitMachineRawSequence.leftLabel MatrixAddressMachine.Label.outer))),
          gateControl,P⟩) = ⟨none,gateControl,F⟩ := by
    simpa only [PrefixSharedGate.program,stackCfg,gateControl,hP]
      using hC
  obtain ⟨t,ht,h⟩ := BitMachineRawSequence.runs
    (GateOperands.program a s.val (width a q + 1))
    PrefixSharedGate.program
    (BitMachineRawSequence.leftLabel
      (SourceClauseFixedBatch.labelAt
        (GateOperands.constantSize a s.val (width a q + 1)) 0))
    (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel
        (BitMachineRawSequence.leftLabel MatrixAddressMachine.Label.outer)))
    ((),((),none)) ((),((),none)) gateControl gateControl
    B P F u c hU hC'
  exact ⟨t,by omega,h⟩

noncomputable def program (a s w : Nat) :=
  BitMachineRawSequence.program (pairProgram a s w)
    PrefixSharedClear.program (.clear 0)
    (((),((),none)),gateControl) ((),none)

theorem run {n a q : Nat} (v : Fin n) (s : Fin a)
    (saved output count : List Bool) :
    ∃ t ≤ GateOperands.cost a s.val (width a q + 1)
        (List.replicate v.val true) +
        SourceClauseRowGate.cost v.val a s.val n s.val v.val
          (width a q + 1) true + 1 +
        PrefixSharedClear.cost
          (bank PrefixSharedCore.gateEmbedding
            (GateReady.prepared v s (width a q + 1)
              saved output count)
            (SourceClauseRowGate.finalBank (0 : Fin 1) (vertexFrame v)
              v.val a s.val n s.val v.val (width a q + 1) true
              saved output count)) + 1,
      ((advance (program a s.val (width a q + 1)))^[t])
        (⟨some (BitMachineRawSequence.leftLabel
          (BitMachineRawSequence.leftLabel
            (BitMachineRawSequence.leftLabel
              (SourceClauseFixedBatch.labelAt
                (GateOperands.constantSize a s.val (width a q + 1)) 0)))),
          ((((),((),none)),gateControl),((),none)),
          PrefixGateReady.blank n v.val saved output count⟩) =
        ⟨none,((((),((),none)),gateControl),((),none)),
          PrefixGateReady.blank n v.val
            (GateHandoff.nextSaved (q := q) v s saved)
            output (true :: true :: true :: count)⟩ := by
  let B := PrefixGateReady.blank n v.val saved output count
  let P := GateReady.prepared v s (width a q + 1) saved output count
  let F := bank PrefixSharedCore.gateEmbedding P
    (SourceClauseRowGate.finalBank (0 : Fin 1) (vertexFrame v)
      v.val a s.val n s.val v.val (width a q + 1) true
      saved output count)
  obtain ⟨u,hu,hU⟩ := pair_run (q := q) v s saved output count
  have hC :
      ((advance PrefixSharedClear.program)^[PrefixSharedClear.cost F])
        (⟨some (.clear 0),((),none),F⟩) =
        ⟨none,((),none),PrefixGateReady.blank n v.val
          (GateHandoff.nextSaved (q := q) v s saved)
          output (true :: true :: true :: count)⟩ := by
    rw [PrefixSharedClear.run]
    exact congrArg (fun S => (⟨none,((),none),S⟩ :
      TM2.Cfg (fun _ : PrefixSharedCore.Stack => Bool)
        (SourceClauseClearExcept.Label
          (SourceClauseClearExcept.workCount PrefixSharedClear.keep))
        (Unit × Option Bool)))
      (GateHandoff.after_clear (q := q) v s saved output count P)
  obtain ⟨t,ht,h⟩ := BitMachineRawSequence.runs
    (pairProgram a s.val (width a q + 1)) PrefixSharedClear.program
    (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel
        (SourceClauseFixedBatch.labelAt
          (GateOperands.constantSize a s.val (width a q + 1)) 0)))
    (.clear 0) (((),((),none)),gateControl)
    (((),((),none)),gateControl) ((),none) ((),none)
    B F (PrefixGateReady.blank n v.val
      (GateHandoff.nextSaved (q := q) v s saved)
      output (true :: true :: true :: count))
    u (PrefixSharedClear.cost F) hU hC
  refine ⟨t,?_,h⟩
  change t ≤ GateOperands.cost a s.val (width a q + 1)
    (List.replicate v.val true) +
    SourceClauseRowGate.cost v.val a s.val n s.val v.val
      (width a q + 1) true + 1 + PrefixSharedClear.cost F + 1
  omega

#print axioms run

end EthInapproximability.CurrentPaper.SourceGenericPrefixMachine.GateCycle
