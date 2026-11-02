import EthInapproximability.CurrentPaper.SourceClauseGateMachine
import EthInapproximability.CurrentPaper.BinarySuccessorMachine

/-!
# Physically prepare adjacent gate addresses from one binary prefix address

The caller supplies `l.variable.bits` and `p.bits` only. A fixed broadcast
copies `p.bits` to the gate's prefix and successor slots, then the verified
variable-width successor program increments the successor copy. This avoids
preloading `(p+1).bits` as an oracle input.
-/

namespace EthInapproximability.CurrentPaper.SourceClauseGateSuccessor

open Turing BitMachineEncoding BitMachineStackEmbedding

abbrev Stack := Fin 2 ⊕ SourceClauseGateMachine.Stack
def source : Stack := .inl 0
def temp : Stack := .inl 1
def literal : Stack := .inr SourceClauseGateBroadcast.literalSource
def prefixAddress : Stack := .inr SourceClauseGateBroadcast.prefixSource
def successorAddress : Stack := .inr SourceClauseGateBroadcast.successorSource
def targets : List Stack := [prefixAddress, successorAddress]

inductive CopyLabel where
  | scan | restore | finish
  deriving DecidableEq, Fintype

def copyProgram : CopyLabel → TM2.Stmt (fun _ : Stack => Bool) CopyLabel
    (Unit × Option Bool)
  | .scan => BitMachineBroadcast.scanStep source temp .scan .restore
  | .restore => BitMachineBroadcast.restoreStep temp targets .restore .finish
  | .finish => .halt

def initial (lword pword saved output count : List Bool) : Stack → List Bool :=
  Sum.elim ![pword, []]
    (SourceClauseGateBroadcast.initial lword [] [] saved output count)

def copied (lword pword saved output count : List Bool) : Stack → List Bool :=
  BitMachineBroadcast.copied source temp targets pword
    (initial lword pword saved output count)

theorem copy_run (lword pword saved output count : List Bool) :
    ((advance copyProgram)^[2 * pword.length + 3])
      (⟨some .scan, ((), none), initial lword pword saved output count⟩ :
        TM2.Cfg (fun _ : Stack => Bool) CopyLabel (Unit × Option Bool)) =
      ⟨none, ((), none), copied lword pword saved output count⟩ := by
  classical
  have h := BitMachineBroadcast.broadcast_run copyProgram source temp
    (by simp [source, temp]) targets
    (by simp [targets, prefixAddress, successorAddress,
      SourceClauseGateBroadcast.prefixSource,
      SourceClauseGateBroadcast.successorSource])
    (by simp [source, targets, prefixAddress, successorAddress])
    (by simp [temp, targets, prefixAddress, successorAddress])
    .scan .restore .finish rfl rfl () none pword
    (initial lword pword saved output count) rfl rfl
  rw [show 2 * pword.length + 3 = (2 * pword.length + 2) + 1 by omega,
    Function.iterate_succ_apply']
  change advance copyProgram
    (BitMachineBroadcast.run copyProgram (2 * pword.length + 2)
      (⟨some .scan, ((), none), initial lword pword saved output count⟩ :
        TM2.Cfg (fun _ : Stack => Bool) CopyLabel (Unit × Option Bool))) = _
  rw [h]
  simp [advance, TM2.step, copyProgram, copied]

def successorEmbedding : Fin 2 ↪ Stack where
  toFun k := if k = 0 then successorAddress else temp
  inj' := by intro i j h; fin_cases i <;> fin_cases j <;> simp_all [successorAddress, temp]

noncomputable def successorProgram (q : BinarySuccessorMachine.Label) :=
  stackStmt successorEmbedding (BinarySuccessorMachine.program q)

def prepared (lword : List Bool) (p : ℕ)
    (saved output count : List Bool) : Stack → List Bool :=
  Sum.elim ![[], []]
    (SourceClauseGateBroadcast.initial lword p.bits (p + 1).bits
      saved output count)

theorem copy_bank (lword : List Bool) (p : ℕ)
    (saved output count : List Bool) :
    copied lword p.bits saved output count =
      Sum.elim ![[], []]
        (SourceClauseGateBroadcast.initial lword p.bits p.bits
          saved output count) := by
  funext k
  cases k with
  | inl i => fin_cases i <;> simp [copied, BitMachineBroadcast.copied,
      source, temp, targets, initial]
  | inr j =>
      cases j with
      | inl i => fin_cases i <;> simp [copied, BitMachineBroadcast.copied,
          source, temp, literal, prefixAddress, successorAddress, targets,
          SourceClauseGateBroadcast.prefixSource,
          SourceClauseGateBroadcast.successorSource,
          initial, SourceClauseGateBroadcast.initial]
      | inr j => simp [copied, BitMachineBroadcast.copied, source, temp,
          targets, prefixAddress, successorAddress,
          SourceClauseGateBroadcast.prefixSource,
          SourceClauseGateBroadcast.successorSource,
          initial, SourceClauseGateBroadcast.initial]

theorem successor_initial (lword : List Bool) (p : ℕ)
    (saved output count : List Bool) :
    bank successorEmbedding (copied lword p.bits saved output count)
      (BinarySuccessorMachine.cfg (some .carry) none p.bits []).stk =
      copied lword p.bits saved output count := by
  apply bank_eq_self
  intro k
  fin_cases k
  · rw [copy_bank]
    simp [successorEmbedding, successorAddress,
      SourceClauseGateBroadcast.initial,
      SourceClauseGateBroadcast.successorSource,
      BinarySuccessorMachine.cfg]
  · rw [copy_bank]
    simp [successorEmbedding, temp, BinarySuccessorMachine.cfg]

theorem successor_final (lword : List Bool) (p : ℕ)
    (saved output count : List Bool) :
    bank successorEmbedding (copied lword p.bits saved output count)
      (BinarySuccessorMachine.cfg none none (p + 1).bits []).stk =
      prepared lword p saved output count := by
  funext k
  by_cases hs : k = successorAddress
  · subst k
    change bank successorEmbedding (copied lword p.bits saved output count)
      (BinarySuccessorMachine.cfg none none (p + 1).bits []).stk
      (successorEmbedding 0) = _
    rw [bank_at]
    simp [BinarySuccessorMachine.cfg, prepared, successorAddress,
      SourceClauseGateBroadcast.successorSource,
      SourceClauseGateBroadcast.initial]
  · by_cases ht : k = temp
    · subst k
      change bank successorEmbedding (copied lword p.bits saved output count)
        (BinarySuccessorMachine.cfg none none (p + 1).bits []).stk
        (successorEmbedding 1) = _
      rw [bank_at]
      simp [BinarySuccessorMachine.cfg, prepared, temp]
    · rw [bank_outside]
      · rw [copy_bank]
        cases k with
        | inl i => fin_cases i <;> simp [prepared, temp, source]
        | inr j =>
            cases j with
            | inl i => fin_cases i <;>
                simp [prepared, successorAddress,
                  SourceClauseGateBroadcast.successorSource,
                  SourceClauseGateBroadcast.initial] at hs ⊢
            | inr j => simp [prepared, SourceClauseGateBroadcast.initial]
      · intro ⟨i, hi⟩
        fin_cases i
        · exact hs hi.symm
        · exact ht hi.symm

theorem successor_run (lword : List Bool) (p : ℕ)
    (saved output count : List Bool) :
    ((advance successorProgram)^[2 * BinarySuccessorMachine.carryCount p.bits + 2])
      (⟨some .carry, none, copied lword p.bits saved output count⟩ :
        TM2.Cfg (fun _ : Stack => Bool) BinarySuccessorMachine.Label (Option Bool)) =
      ⟨none, none, prepared lword p saved output count⟩ := by
  have h := BinarySuccessorMachine.run_correct none p.bits []
  simp only [List.length_nil, Nat.add_zero, List.reverse_nil,
    List.nil_append, BinarySuccessorMachine.successor_bits] at h
  have he := BitMachineStackRun.run successorEmbedding
    (copied lword p.bits saved output count)
    BinarySuccessorMachine.program
    (BinarySuccessorMachine.cfg (some .carry) none p.bits [])
    (2 * BinarySuccessorMachine.carryCount p.bits + 2)
  rw [show ((advance BinarySuccessorMachine.program)^[
      2 * BinarySuccessorMachine.carryCount p.bits + 2])
      (BinarySuccessorMachine.cfg (some .carry) none p.bits []) = _ from h] at he
  simpa only [stackCfg, successor_initial, successor_final] using he

noncomputable def prepareProgram :=
  BitMachineRawSequence.program copyProgram successorProgram
    BinarySuccessorMachine.Label.carry ((), none) none

theorem prepare_run (lword : List Bool) (p : ℕ)
    (saved output count : List Bool) :
    ∃ t ≤ 4 * p.bits.length + 6,
      ((advance prepareProgram)^[t])
        (⟨some (BitMachineRawSequence.leftLabel CopyLabel.scan),
          (((), none), none), initial lword p.bits saved output count⟩ :
          TM2.Cfg (fun _ : Stack => Bool)
            (BitMachineRawSequence.Label CopyLabel BinarySuccessorMachine.Label)
            ((Unit × Option Bool) × Option Bool)) =
        ⟨none, (((), none), none), prepared lword p saved output count⟩ := by
  obtain ⟨t, ht, hr⟩ := BitMachineRawSequence.runs copyProgram successorProgram
    CopyLabel.scan BinarySuccessorMachine.Label.carry
    ((), none) ((), none) none none
    (initial lword p.bits saved output count)
    (copied lword p.bits saved output count)
    (prepared lword p saved output count)
    (2 * p.bits.length + 3)
    (2 * BinarySuccessorMachine.carryCount p.bits + 2)
    (copy_run lword p.bits saved output count)
    (successor_run lword p saved output count)
  refine ⟨t, ?_, hr⟩
  have hcarry := BinarySuccessorMachine.carryCount_le_length p.bits
  omega

end EthInapproximability.CurrentPaper.SourceClauseGateSuccessor
