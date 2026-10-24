import EthInapproximability.CurrentPaper.SourceClausePairGateReady

namespace EthInapproximability.CurrentPaper.SourceBooleanPrefix.PairGateExecute

open Turing BitMachineEncoding BitMachineStackEmbedding
open SourceBooleanEncoding
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

noncomputable def finished {n q : Nat} (v : Fin n) (s t ell : Fin 2)
    (saved output count : List Bool) : Stack → List Bool :=
  bank gateEmbedding
    (PairGatePrep.ready (q := q) v (if ell = 0 then s else t)
      ell (pairOrdinal v s t) saved output count)
    (SourceClauseRowGate.finalBank (0 : Fin 1) (vertexFrame v)
      v.val 2 (if ell = 0 then s else t).val n ell.val
      (pairOrdinal v s t) (width 2 q + 1)
      (if ell = 0 then PairSignedGate.signFirst s t
        else PairSignedGate.signSecond s t)
      saved output count)

theorem run {n q : Nat} (v : Fin n) (s t ell : Fin 2)
    (saved output count : List Bool) :
    let bit := if ell = 0 then s else t
    let sign := if ell = 0 then PairSignedGate.signFirst s t
      else PairSignedGate.signSecond s t
    ∃ T ≤ SourceClauseRowGate.cost v.val 2 bit.val n ell.val
        (pairOrdinal v s t) (width 2 q + 1) sign,
      ((advance (program sign))^[T])
        (⟨some (BitMachineRawSequence.leftLabel
          (BitMachineRawSequence.leftLabel
            (BitMachineRawSequence.leftLabel MatrixAddressMachine.Label.outer))),
          gateControl,
          PairGatePrep.ready (q := q) v bit ell (pairOrdinal v s t)
            saved output count⟩ : TM2.Cfg (fun _ : Stack => Bool) _ _) =
        ⟨none, gateControl, finished (q := q) v s t ell
          saved output count⟩ := by
  dsimp
  let bit : Fin 2 := if ell = 0 then s else t
  let sign : Bool := if ell = 0 then PairSignedGate.signFirst s t
    else PairSignedGate.signSecond s t
  obtain ⟨T, hT, hrun⟩ := SourceClauseRowGate.run (0 : Fin 1)
    (vertexFrame v) v.val 2 bit.val n ell.val (pairOrdinal v s t)
    (width 2 q + 1) sign saved output count (vertexFrame_query v)
  have hsim := BitMachineStackRun.run gateEmbedding
    (PairGatePrep.ready (q := q) v bit ell (pairOrdinal v s t)
      saved output count)
    (SourceClauseRowGate.program (0 : Fin 1) sign)
    (⟨some (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel
        (BitMachineRawSequence.leftLabel MatrixAddressMachine.Label.outer))),
      gateControl,
      SourceClauseRowGate.initial (vertexFrame v)
        v.val 2 bit.val n ell.val (pairOrdinal v s t)
        (width 2 q + 1) saved output count⟩ :
      TM2.Cfg (fun _ : SourceClauseRowGate.Stack 1 => Bool) _ _) T
  dsimp [gateControl] at hsim
  rw [hrun] at hsim
  have hbank : bank gateEmbedding
      (PairGatePrep.ready (q := q) v bit ell (pairOrdinal v s t)
        saved output count)
      (SourceClauseRowGate.initial (vertexFrame v)
        v.val 2 bit.val n ell.val (pairOrdinal v s t)
        (width 2 q + 1) saved output count) =
      PairGatePrep.ready (q := q) v bit ell (pairOrdinal v s t)
        saved output count := by
    apply bank_eq_self
    intro x
    exact (PairGateReady.ready_gate_at (q := q) v bit ell
      (pairOrdinal v s t) saved output count x).symm
  refine ⟨T, hT, ?_⟩
  simp only [stackCfg] at hsim
  rw [hbank] at hsim
  simpa only [program, finished, gateEmbedding, gateControl,
    bit, sign, stackCfg] using hsim

end EthInapproximability.CurrentPaper.SourceBooleanPrefix.PairGateExecute
