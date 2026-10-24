import EthInapproximability.CurrentPaper.SourceClausePairUnitLift
import EthInapproximability.CurrentPaper.SourceClausePrefixGate

/-!
The existing physical row-gate routine is specialized to a pair source slot.
This checks both signs and an ordinal independent of the queried vertex.
Preparing these operands on the shared bank is a separate physical step.
-/

namespace EthInapproximability.CurrentPaper.SourceBooleanPrefix.PairSignedGate

open Turing BitMachineEncoding
open SourceBooleanEncoding SourceClauseEncoding EncodedCNF

def signFirst (s t : Fin 2) : Bool := decide (s = t)
def signSecond (_s _t : Fin 2) : Bool := false

def bitFirst (s _t : Fin 2) : Fin 2 := s
def bitSecond (_s t : Fin 2) : Fin 2 := t

def emittedGate {n q : Nat} (v : Fin n) (s t : Fin 2)
    (ell : Fin 2) : List Clause :=
  let bit := if ell = 0 then s else t
  let sign := if ell = 0 then signFirst s t else signSecond s t
  orGate (base n q (pairOrdinal v s t) + ell.val)
    ⟨bitIndex v bit, sign⟩

theorem chain_stages {n q : Nat} (v : Fin n) (s t : Fin 2) :
    chain (base n q (pairOrdinal v s t)) (pairPayload v s t) =
      [unit (SourceClauseEncoding.negative
        (base n q (pairOrdinal v s t)))] ++
      emittedGate (q := q) v s t 0 ++
      emittedGate (q := q) v s t 1 ++
      [unit (SourceClauseEncoding.positive
        (base n q (pairOrdinal v s t) + 2))] := by
  rw [PairSourceSchedule.payload_signs]
  simp [chain, emittedGate, signFirst, signSecond,
    SourceBooleanEncoding.negative]

theorem gate_run {n q : Nat} (v : Fin n) (s t : Fin 2)
    (ell : Fin 2) (saved output count : List Bool) :
    let bit := if ell = 0 then s else t
    let sign := if ell = 0 then signFirst s t else signSecond s t
    ∃ T ≤ SourceClauseRowGate.cost v.val 2 bit.val n ell.val
        (pairOrdinal v s t) (width 2 q + 1) sign,
      ((advance (SourceClauseRowGate.program (0 : Fin 1) sign))^[T])
        (⟨some (BitMachineRawSequence.leftLabel
          (BitMachineRawSequence.leftLabel
            (BitMachineRawSequence.leftLabel MatrixAddressMachine.Label.outer))),
          (((false, (SourceLabelAddressMachine.counter.initial, none)),
              ((), none)),
            ((false, ((), none)),
              (((false, (SourceLabelAddressMachine.counter.initial, none)),
                  ((), none)),
                ((((), none), none), SourceClauseGateMachine.control)))),
          SourceClauseRowGate.initial (vertexFrame v)
            v.val 2 bit.val n ell.val (pairOrdinal v s t)
            (width 2 q + 1) saved output count⟩ :
          TM2.Cfg (fun _ : SourceClauseRowGate.Stack 1 => Bool) _ _) =
        ⟨none,
          (((false, (SourceLabelAddressMachine.counter.initial, none)),
              ((), none)),
            ((false, ((), none)),
              (((false, (SourceLabelAddressMachine.counter.initial, none)),
                  ((), none)),
                ((((), none), none), SourceClauseGateMachine.control)))),
          SourceClauseRowGate.finalBank (0 : Fin 1) (vertexFrame v)
            v.val 2 bit.val n ell.val (pairOrdinal v s t)
            (width 2 q + 1) sign saved output count⟩ := by
  exact SourceClauseRowGate.run (0 : Fin 1) (vertexFrame v)
    v.val 2 (if ell = 0 then s else t).val n ell.val
    (pairOrdinal v s t) (width 2 q + 1)
    (if ell = 0 then signFirst s t else signSecond s t)
    saved output count (vertexFrame_query v)

theorem gate_saved {n q : Nat} (v : Fin n) (s t : Fin 2)
    (ell : Fin 2) (saved output count : List Bool) :
    let bit := if ell = 0 then s else t
    let sign := if ell = 0 then signFirst s t else signSecond s t
    SourceClauseRowGate.finalBank (0 : Fin 1) (vertexFrame v)
      v.val 2 bit.val n ell.val (pairOrdinal v s t)
      (width 2 q + 1) sign saved output count gateSavedKey =
      (clauseFields (emittedGate (q := q) v s t ell)).reverse ++ saved := by
  intro bit sign
  rw [gateSavedKey, SourceClauseRowGate.final_saved]
  simp [emittedGate, base, bitIndex_val,
    SourceClauseGatePrepare.firstClause,
    SourceClauseGatePrepare.secondClause,
    SourceClauseGatePrepare.thirdClause, orGate, clauseFields,
    List.reverse_append, List.append_assoc]
  have hp : (pairOrdinal v s t) * (width 2 q + 1) +
      (n * 2 + ell.val) =
      2 * n + (pairOrdinal v s t) * (width 2 q + 1) + ell.val := by
    omega
  rw [hp]

end EthInapproximability.CurrentPaper.SourceBooleanPrefix.PairSignedGate
