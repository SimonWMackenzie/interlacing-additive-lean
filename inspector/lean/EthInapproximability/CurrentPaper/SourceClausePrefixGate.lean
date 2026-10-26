import EthInapproximability.CurrentPaper.SourceClauseBooleanPrefix
import EthInapproximability.CurrentPaper.SourceClauseRowGate

/-!
One physically executed prefix OR gate. The full eight-clause at-least and
pair callbacks, including two unit endpoints and the pair ordinal preparer,
are not asserted here.
-/

namespace EthInapproximability.CurrentPaper.SourceBooleanPrefix

open SourceBooleanEncoding SourceClauseEncoding EncodedCNF
open Turing BitMachineEncoding

def atLeastGateAddress {n q : ℕ} (v : Fin n) (s : Fin 2) : ℕ :=
  v.val * (width 2 q + 1) + (n * 2 + s.val)

theorem atLeastGateAddress_eq {n q : ℕ} (v : Fin n) (s : Fin 2) :
    atLeastGateAddress (q := q) v s =
      base n q (atLeastOrdinal v) + s.val := by
  simp only [atLeastGateAddress, base, atLeastOrdinal]
  ring

theorem bitIndex_val {n : ℕ} (v : Fin n) (s : Fin 2) :
    (bitIndex v s).val = v.val * 2 + s.val := by
  simp [bitIndex, finProdFinEquiv]
  omega

def vertexFrame {n : ℕ} (v : Fin n) :
    SourceCSPRowQueryFrame.Stack 1 → List Bool :=
  fun k => if k = .inl ((0 : Fin 1), 1) then List.replicate v.val true else []

theorem vertexFrame_query {n : ℕ} (v : Fin n) :
    vertexFrame v (.inl ((0 : Fin 1), 1)) = List.replicate v.val true := by
  simp [vertexFrame]

theorem atLeast_gate_run {n q : ℕ} (v : Fin n) (s : Fin 2)
    (saved output count : List Bool) :
    ∃ T ≤ SourceClauseRowGate.cost v.val 2 s.val n s.val v.val
        (width 2 q + 1) true,
      ((advance (SourceClauseRowGate.program (0 : Fin 1) true))^[T])
        (⟨some (BitMachineRawSequence.leftLabel
          (BitMachineRawSequence.leftLabel
            (BitMachineRawSequence.leftLabel MatrixAddressMachine.Label.outer))),
          (((false, (SourceLabelAddressMachine.counter.initial, none)),
              ((), none)),
            ((false, ((), none)),
              (((false, (SourceLabelAddressMachine.counter.initial, none)),
                  ((), none)),
                ((((), none), none), SourceClauseGateMachine.control)))),
          SourceClauseRowGate.initial (vertexFrame v) v.val 2 s.val n s.val
            v.val (width 2 q + 1) saved output count⟩) =
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
  exact SourceClauseRowGate.run (0 : Fin 1) (vertexFrame v)
    v.val 2 s.val n s.val v.val (width 2 q + 1) true
    saved output count (vertexFrame_query v)

def gateSavedKey : SourceClauseRowGate.Stack 1 :=
  SourceClauseRowGate.gateEmbedding
    (SourceClauseGateSlotAddress.gateEmbedding
      (SourceClauseGateAffineAddress.gateEmbedding
        (SourceClauseGateTwoAddress.embedding
          (SourceClauseGateMachine.embedding (.inr (.inl 0))))))

def gateCountKey : SourceClauseRowGate.Stack 1 :=
  SourceClauseRowGate.gateEmbedding
    (SourceClauseGateSlotAddress.gateEmbedding
      (SourceClauseGateAffineAddress.gateEmbedding
        (SourceClauseGateTwoAddress.embedding
          (SourceClauseGateMachine.embedding (.inr (.inr ()))))))

theorem atLeast_gate_saved {n q : ℕ} (v : Fin n) (s : Fin 2)
    (saved output count : List Bool) :
    SourceClauseRowGate.finalBank (0 : Fin 1) (vertexFrame v)
      v.val 2 s.val n s.val v.val (width 2 q + 1) true
      saved output count gateSavedKey =
    (clauseFields (orGate
      (base n q (atLeastOrdinal v) + s.val)
      (SourceBooleanEncoding.positive (bitIndex v s)))).reverse ++ saved := by
  rw [gateSavedKey, SourceClauseRowGate.final_saved]
  rw [← atLeastGateAddress_eq (q := q) v s]
  simp [atLeastGateAddress, bitIndex_val, SourceBooleanEncoding.positive,
    orGate, SourceClauseGatePrepare.firstClause,
    SourceClauseGatePrepare.secondClause,
    SourceClauseGatePrepare.thirdClause,
    clauseFields, List.reverse_append, List.append_assoc]

theorem atLeast_gate_count {n q : ℕ} (v : Fin n) (s : Fin 2)
    (saved output count : List Bool) :
    SourceClauseRowGate.finalBank (0 : Fin 1) (vertexFrame v)
      v.val 2 s.val n s.val v.val (width 2 q + 1) true
      saved output count gateCountKey = true :: true :: true :: count := by
  exact SourceClauseRowGate.final_count (0 : Fin 1) (vertexFrame v)
    v.val 2 s.val n s.val v.val (width 2 q + 1) true saved output count

end EthInapproximability.CurrentPaper.SourceBooleanPrefix
