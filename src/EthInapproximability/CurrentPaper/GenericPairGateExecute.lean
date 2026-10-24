import EthInapproximability.CurrentPaper.GenericPairGateReady

namespace EthInapproximability.CurrentPaper.SourceGenericPrefixMachine.PairGateExecute

open Turing BitMachineEncoding BitMachineStackEmbedding
open SourceBooleanPrefix
open scoped Classical

abbrev Stack := PairUnitLift.Stack

noncomputable def gateEmbedding : SourceClauseRowGate.Stack 1 ↪ Stack :=
  PrefixSharedCore.gateEmbedding.trans PairGateBase.coreEmbedding

noncomputable def program (sign : Bool) :=
  fun l => stackStmt gateEmbedding (SourceClauseRowGate.program (0 : Fin 1) sign l)

noncomputable def gateControl :=
  (((false, (SourceLabelAddressMachine.counter.initial, (none : Option Bool))),
      ((), (none : Option Bool))),
    ((false, ((), (none : Option Bool))),
      (((false, (SourceLabelAddressMachine.counter.initial, (none : Option Bool))),
          ((), (none : Option Bool))),
        ((((), (none : Option Bool)), (none : Option Bool)),
          SourceClauseGateMachine.control))))

noncomputable def finished {n a : Nat} (v : Fin n) (bit : Fin a)
    (position ordinal w : Nat) (sign : Bool)
    (saved output count : List Bool) : Stack → List Bool :=
  bank gateEmbedding
    (PairGatePrep.ready v bit w ordinal position saved output count)
    (SourceClauseRowGate.finalBank (0 : Fin 1) (vertexFrame v)
      v.val a bit.val n position ordinal w sign saved output count)

theorem run {n a : Nat} (v : Fin n) (bit : Fin a)
    (position ordinal w : Nat) (sign : Bool)
    (saved output count : List Bool) :
    ∃ T ≤ SourceClauseRowGate.cost v.val a bit.val n position ordinal w sign,
      ((advance (program sign))^[T])
        (⟨some (BitMachineRawSequence.leftLabel
          (BitMachineRawSequence.leftLabel
            (BitMachineRawSequence.leftLabel MatrixAddressMachine.Label.outer))),
          gateControl,
          PairGatePrep.ready v bit w ordinal position saved output count⟩ :
          TM2.Cfg (fun _ : Stack => Bool) _ _) =
        ⟨none, gateControl, finished v bit position ordinal w sign
          saved output count⟩ := by
  obtain ⟨T, hT, hrun⟩ := SourceClauseRowGate.run (0 : Fin 1)
    (vertexFrame v) v.val a bit.val n position ordinal w sign
    saved output count (vertexFrame_query v)
  have hsim := BitMachineStackRun.run gateEmbedding
    (PairGatePrep.ready v bit w ordinal position saved output count)
    (SourceClauseRowGate.program (0 : Fin 1) sign)
    (⟨some (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel
        (BitMachineRawSequence.leftLabel MatrixAddressMachine.Label.outer))),
      gateControl,
      SourceClauseRowGate.initial (vertexFrame v)
        v.val a bit.val n position ordinal w saved output count⟩ :
      TM2.Cfg (fun _ : SourceClauseRowGate.Stack 1 => Bool) _ _) T
  dsimp [gateControl] at hsim
  rw [hrun] at hsim
  have hbank : bank gateEmbedding
      (PairGatePrep.ready v bit w ordinal position saved output count)
      (SourceClauseRowGate.initial (vertexFrame v)
        v.val a bit.val n position ordinal w saved output count) =
      PairGatePrep.ready v bit w ordinal position saved output count := by
    apply bank_eq_self
    intro x
    exact (PairGateReady.ready_gate_at v bit position ordinal w
      saved output count x).symm
  refine ⟨T, hT, ?_⟩
  simp only [stackCfg] at hsim
  rw [hbank] at hsim
  simpa only [program, finished, gateEmbedding, gateControl, stackCfg] using hsim

#print axioms run

end EthInapproximability.CurrentPaper.SourceGenericPrefixMachine.PairGateExecute
