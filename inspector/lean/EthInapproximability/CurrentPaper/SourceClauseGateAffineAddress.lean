import EthInapproximability.CurrentPaper.SourceClauseGateTwoAddress
import EthInapproximability.CurrentPaper.SourceLabelAddressMachine

/-!
# Affine prefix address, then one physical OR gate

The prefix address is computed from preserved unary arguments `r,w,c` as
`r*w+c`, copied to the gate input, and consumed by the two-address gate
writer. The sole binary numerical input is the original literal address.
-/

namespace EthInapproximability.CurrentPaper.SourceClauseGateAffineAddress

open Turing BitMachineEncoding BitMachineStackEmbedding

abbrev Stack := SourceLabelAddressMachine.Stack ⊕ SourceClauseGateTwoAddress.Stack

def addressEmbedding : SourceLabelAddressMachine.Stack ↪ Stack :=
  Function.Embedding.inl
def gateEmbedding : SourceClauseGateTwoAddress.Stack ↪ Stack :=
  Function.Embedding.inr

noncomputable def addressSource : Stack :=
  .inl (.inr (.inl SourceLabelAddressMachine.counter.input))
def temp : Stack := .inl (.inl 3)
def gatePrefix : Stack := .inr SourceClauseGateSuccessor.source
def targets : List Stack := [gatePrefix]

inductive CopyLabel where
  | scan | restore | finish
  deriving DecidableEq, Fintype

noncomputable def copyProgram : CopyLabel →
    TM2.Stmt (fun _ : Stack => Bool) CopyLabel (Unit × Option Bool)
  | .scan => BitMachineBroadcast.scanStep addressSource temp .scan .restore
  | .restore => BitMachineBroadcast.restoreStep temp targets .restore .finish
  | .finish => .halt

noncomputable def initial (r w c : ℕ) (lword saved output count : List Bool) :
    Stack → List Bool :=
  Sum.elim (SourceLabelAddressMachine.inputs r w c)
    (SourceClauseGateSuccessor.initial lword [] saved output count)

noncomputable def addressed (r w c : ℕ) (lword saved output count : List Bool) :
    Stack → List Bool :=
  Sum.elim (SourceLabelAddressMachine.outputs r w c)
    (SourceClauseGateSuccessor.initial lword [] saved output count)

noncomputable def copied (r w c : ℕ) (lword saved output count : List Bool) :
    Stack → List Bool :=
  BitMachineBroadcast.copied addressSource temp targets (r * w + c).bits
    (addressed r w c lword saved output count)

noncomputable def addressProgram (q : SourceLabelAddressMachine.Label) :=
  stackStmt addressEmbedding (SourceLabelAddressMachine.program q)

noncomputable def gateProgram (sign : Bool)
    (q : BitMachineRawSequence.Label
      (BitMachineRawSequence.Label SourceClauseGateSuccessor.CopyLabel
        BinarySuccessorMachine.Label)
      (BitMachineRawSequence.Label SourceClauseGateMachine.PrepareLabel
        SourceClauseGateMachine.EmitLabel)) :=
  stackStmt gateEmbedding (SourceClauseGateTwoAddress.program sign q)

noncomputable def program (sign : Bool) :=
  BitMachineRawSequence.program
    (BitMachineRawSequence.program addressProgram copyProgram
      CopyLabel.scan (false, (SourceLabelAddressMachine.counter.initial, none))
      ((), none))
    (gateProgram sign)
    (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel SourceClauseGateSuccessor.CopyLabel.scan))
    (((false, (SourceLabelAddressMachine.counter.initial, none)), ((), none)))
    ((((), none), none), SourceClauseGateMachine.control)

theorem address_initial (r w c : ℕ) (lword saved output count : List Bool) :
    bank addressEmbedding (initial r w c lword saved output count)
      (SourceLabelAddressMachine.inputs r w c) =
      initial r w c lword saved output count := by
  apply bank_eq_self
  intro k
  rfl

theorem address_final (r w c : ℕ) (lword saved output count : List Bool) :
    bank addressEmbedding (initial r w c lword saved output count)
      (SourceLabelAddressMachine.outputs r w c) =
      addressed r w c lword saved output count := by
  funext k
  cases k with
  | inl i => exact bank_at addressEmbedding _ _ i
  | inr j =>
      rw [bank_outside]
      · rfl
      · intro ⟨i, hi⟩; cases hi

theorem address_run (r w c : ℕ) (lword saved output count : List Bool) :
    ∃ t ≤ MatrixAddressMachine.exactTime r w c +
        UnaryBinaryEncoding.coefficient * (r * w + c + 1) ^ 2 + 1,
      ((advance addressProgram)^[t])
        (⟨some (BitMachineRawSequence.leftLabel .outer),
          (false, (SourceLabelAddressMachine.counter.initial, none)),
          initial r w c lword saved output count⟩ :
          TM2.Cfg (fun _ : Stack => Bool) SourceLabelAddressMachine.Label
            SourceLabelAddressMachine.Control) =
        ⟨none, (false, (SourceLabelAddressMachine.counter.initial, none)),
          addressed r w c lword saved output count⟩ := by
  obtain ⟨t, ht, hr⟩ := SourceLabelAddressMachine.label_run r w c
  have he := BitMachineStackRun.run addressEmbedding
    (initial r w c lword saved output count)
    SourceLabelAddressMachine.program
    (⟨some (BitMachineRawSequence.leftLabel .outer),
      (false, (SourceLabelAddressMachine.counter.initial, none)),
      SourceLabelAddressMachine.inputs r w c⟩ :
      SourceLabelAddressMachine.Config) t
  rw [hr] at he
  simp only [stackCfg] at he
  rw [address_initial, address_final] at he
  exact ⟨t, ht, he⟩

theorem copy_run (r w c : ℕ) (lword saved output count : List Bool) :
    let p := r * w + c
    ((advance copyProgram)^[2 * p.bits.length + 3])
      (⟨some CopyLabel.scan, ((), none), addressed r w c lword saved output count⟩ :
        TM2.Cfg (fun _ : Stack => Bool) CopyLabel (Unit × Option Bool)) =
      ⟨none, ((), none), copied r w c lword saved output count⟩ := by
  dsimp only
  let p := r * w + c
  have hs : (addressed r w c lword saved output count) addressSource = p.bits := by
    simp [addressed, addressSource, SourceLabelAddressMachine.outputs,
      SourceLabelAddressMachine.ambient, SourceUnaryBinaryCall.final_bank, p]
  have ht : (addressed r w c lword saved output count) temp = [] := by
    rfl
  have h := BitMachineBroadcast.broadcast_run copyProgram addressSource temp
    (by simp [addressSource, temp]) targets (by simp [targets])
    (by simp [addressSource, targets, gatePrefix])
    (by simp [temp, targets, gatePrefix])
    .scan .restore .finish rfl rfl () none p.bits
    (addressed r w c lword saved output count) hs ht
  rw [show 2 * p.bits.length + 3 = (2 * p.bits.length + 2) + 1 by omega,
    Function.iterate_succ_apply']
  change advance copyProgram
    (BitMachineBroadcast.run copyProgram (2 * p.bits.length + 2)
      (⟨some .scan, ((), none), addressed r w c lword saved output count⟩ :
        TM2.Cfg (fun _ : Stack => Bool) CopyLabel (Unit × Option Bool))) = _
  rw [h]
  simp [advance, TM2.step, copyProgram, copied, p]

theorem gate_initial (r w c : ℕ) (lword saved output count : List Bool) :
    bank gateEmbedding (copied r w c lword saved output count)
      (SourceClauseGateSuccessor.initial lword (r * w + c).bits
        saved output count) =
      copied r w c lword saved output count := by
  apply bank_eq_self
  intro k
  cases k with
  | inl i =>
      fin_cases i <;>
        simp [copied, BitMachineBroadcast.copied, gatePrefix, targets,
          addressSource, temp, addressed, gateEmbedding,
          SourceClauseGateSuccessor.initial,
          SourceClauseGateSuccessor.source]
  | inr k => simp [copied, BitMachineBroadcast.copied, gatePrefix, targets,
      addressSource, temp, addressed, gateEmbedding,
      SourceClauseGateSuccessor.source, SourceClauseGateSuccessor.initial]

noncomputable def finalBank (r w c : ℕ) (l : EncodedCNF.Literal)
    (saved output count : List Bool) : Stack → List Bool :=
  let p := r * w + c
  let P := SourceClauseGateSuccessor.prepared l.variable.bits p
    saved output count
  bank gateEmbedding (copied r w c l.variable.bits saved output count)
    (bank SourceClauseGateTwoAddress.embedding P
      (bank SourceClauseGateMachine.embedding
        (SourceClauseGateBroadcast.prepared l.variable.bits p.bits
          (p + 1).bits saved output count)
        (SourceClauseGateMachine.finalSchedule p l saved output count)))

theorem run (r w c : ℕ) (l : EncodedCNF.Literal)
    (saved output count : List Bool) :
    let p := r * w + c
    ∃ t ≤ MatrixAddressMachine.exactTime r w c +
        UnaryBinaryEncoding.coefficient * (p + 1) ^ 2 +
        6 * p.bits.length +
        2 * (l.variable.bits.length + p.bits.length + (p + 1).bits.length) +
        SourceLiteralWriter.emitTime
          (SourceLiteralWriter.words (SourceClauseGatePrepare.firstClause p l)) +
        SourceLiteralWriter.emitTime
          (SourceLiteralWriter.words (SourceClauseGatePrepare.secondClause p)) +
        SourceLiteralWriter.emitTime
          (SourceLiteralWriter.words (SourceClauseGatePrepare.thirdClause p l)) + 37,
      ((advance (program l.positive))^[t])
        (⟨some (BitMachineRawSequence.leftLabel
          (BitMachineRawSequence.leftLabel
            (BitMachineRawSequence.leftLabel MatrixAddressMachine.Label.outer))),
          (((false, (SourceLabelAddressMachine.counter.initial, none)), ((), none)),
            ((((), none), none), SourceClauseGateMachine.control)),
          initial r w c l.variable.bits saved output count⟩ :
          TM2.Cfg (fun _ : Stack => Bool)
            (BitMachineRawSequence.Label
              (BitMachineRawSequence.Label SourceLabelAddressMachine.Label CopyLabel)
              (BitMachineRawSequence.Label
                (BitMachineRawSequence.Label SourceClauseGateSuccessor.CopyLabel
                  BinarySuccessorMachine.Label)
                (BitMachineRawSequence.Label SourceClauseGateMachine.PrepareLabel
                  SourceClauseGateMachine.EmitLabel)))
            ((SourceLabelAddressMachine.Control × (Unit × Option Bool)) ×
              (((Unit × Option Bool) × Option Bool) ×
                (SourceClauseGateMachine.PrepareControl ×
                  SourceClauseGateMachine.EmitControl)))) =
        ⟨none,
          (((false, (SourceLabelAddressMachine.counter.initial, none)), ((), none)),
            ((((), none), none), SourceClauseGateMachine.control)),
          finalBank r w c l saved output count⟩ := by
  dsimp only
  let p := r * w + c
  obtain ⟨ta, hta, ha⟩ := address_run r w c l.variable.bits saved output count
  have hb := copy_run r w c l.variable.bits saved output count
  obtain ⟨tab, htab, hab⟩ := BitMachineRawSequence.runs addressProgram
    copyProgram (BitMachineRawSequence.leftLabel MatrixAddressMachine.Label.outer)
    CopyLabel.scan
    (false, (SourceLabelAddressMachine.counter.initial, none))
    (false, (SourceLabelAddressMachine.counter.initial, none))
    ((), none) ((), none)
    (initial r w c l.variable.bits saved output count)
    (addressed r w c l.variable.bits saved output count)
    (copied r w c l.variable.bits saved output count)
    ta (2 * p.bits.length + 3) ha hb
  let P := SourceClauseGateSuccessor.prepared l.variable.bits p saved output count
  obtain ⟨tg, htg, hg⟩ := SourceClauseGateTwoAddress.run p l saved output count
  have hg' := BitMachineStackRun.run gateEmbedding
    (copied r w c l.variable.bits saved output count)
    (SourceClauseGateTwoAddress.program l.positive)
    (⟨some (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel SourceClauseGateSuccessor.CopyLabel.scan)),
      ((((), none), none), SourceClauseGateMachine.control),
      SourceClauseGateSuccessor.initial l.variable.bits p.bits saved output count⟩ :
      TM2.Cfg (fun _ : SourceClauseGateTwoAddress.Stack => Bool)
        (BitMachineRawSequence.Label
          (BitMachineRawSequence.Label SourceClauseGateSuccessor.CopyLabel
            BinarySuccessorMachine.Label)
          (BitMachineRawSequence.Label SourceClauseGateMachine.PrepareLabel
            SourceClauseGateMachine.EmitLabel))
        (((Unit × Option Bool) × Option Bool) ×
          (SourceClauseGateMachine.PrepareControl ×
            SourceClauseGateMachine.EmitControl))) tg
  rw [hg] at hg'
  simp only [stackCfg] at hg'
  rw [gate_initial r w c l.variable.bits saved output count] at hg'
  obtain ⟨t, ht, hr⟩ := BitMachineRawSequence.runs
    (BitMachineRawSequence.program addressProgram copyProgram CopyLabel.scan
      (false, (SourceLabelAddressMachine.counter.initial, none)) ((), none))
    (gateProgram l.positive)
    (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel MatrixAddressMachine.Label.outer))
    (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel SourceClauseGateSuccessor.CopyLabel.scan))
    ((false, (SourceLabelAddressMachine.counter.initial, none)), ((), none))
    ((false, (SourceLabelAddressMachine.counter.initial, none)), ((), none))
    ((((), none), none), SourceClauseGateMachine.control)
    ((((), none), none), SourceClauseGateMachine.control)
    (initial r w c l.variable.bits saved output count)
    (copied r w c l.variable.bits saved output count)
    (finalBank r w c l saved output count)
    tab tg hab hg'
  refine ⟨t, ?_, hr⟩
  dsimp [p] at htab htg
  omega

theorem final_saved (r w c : ℕ) (l : EncodedCNF.Literal)
    (saved output count : List Bool) :
    finalBank r w c l saved output count
      (gateEmbedding (SourceClauseGateTwoAddress.embedding
        (SourceClauseGateMachine.embedding (.inr (.inl 0))))) =
      (EncodedCNF.encodeClause
        (SourceClauseGatePrepare.thirdClause (r * w + c) l)).reverse ++
      (EncodedCNF.encodeClause
        (SourceClauseGatePrepare.secondClause (r * w + c))).reverse ++
      (EncodedCNF.encodeClause
        (SourceClauseGatePrepare.firstClause (r * w + c) l)).reverse ++
      saved := by
  simp only [finalBank, bank_at, SourceClauseGateMachine.final_saved]

theorem final_count (r w c : ℕ) (l : EncodedCNF.Literal)
    (saved output count : List Bool) :
    finalBank r w c l saved output count
      (gateEmbedding (SourceClauseGateTwoAddress.embedding
        (SourceClauseGateMachine.embedding (.inr (.inr ()))))) =
      true :: true :: true :: count := by
  simp only [finalBank, bank_at, SourceClauseGateMachine.final_count]

theorem final_output (r w c : ℕ) (l : EncodedCNF.Literal)
    (saved output count : List Bool) :
    finalBank r w c l saved output count
      (gateEmbedding (SourceClauseGateTwoAddress.embedding
        (SourceClauseGateMachine.embedding (.inr (.inl 1))))) = output := by
  simp only [finalBank, bank_at, SourceClauseGateMachine.final_output]

end EthInapproximability.CurrentPaper.SourceClauseGateAffineAddress
