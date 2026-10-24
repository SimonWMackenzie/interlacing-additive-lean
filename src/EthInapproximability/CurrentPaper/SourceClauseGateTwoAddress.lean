import EthInapproximability.CurrentPaper.SourceClauseGateSuccessor

/-!
# One fixed gate program from two numerical address words

The successor address `p+1` is generated on stacks before the gate writer
runs. The input contains only `l.variable.bits` and `p.bits`, plus the
reverse-payload accumulator, output suffix, and unary clause count.
-/

namespace EthInapproximability.CurrentPaper.SourceClauseGateTwoAddress

open Turing BitMachineEncoding BitMachineStackEmbedding

abbrev Stack := SourceClauseGateSuccessor.Stack
def embedding : SourceClauseGateMachine.Stack ↪ Stack := Function.Embedding.inr

noncomputable def writer (sign : Bool)
    (q : BitMachineRawSequence.Label
      SourceClauseGateMachine.PrepareLabel SourceClauseGateMachine.EmitLabel) :=
  stackStmt embedding (SourceClauseGateMachine.fixedProgram sign q)

noncomputable def program (sign : Bool) :=
  BitMachineRawSequence.program SourceClauseGateSuccessor.prepareProgram
    (writer sign)
    (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel
        (BitMachineRawSequence.leftLabel
          SourceClauseGateBroadcast.CopyLabel.scan)))
    (((), none), none) SourceClauseGateMachine.control

theorem writer_initial (lword : List Bool) (p : ℕ)
    (saved output count : List Bool) :
    bank embedding (SourceClauseGateSuccessor.prepared lword p saved output count)
      (SourceClauseGateBroadcast.initial lword p.bits (p + 1).bits
        saved output count) =
      SourceClauseGateSuccessor.prepared lword p saved output count := by
  apply bank_eq_self
  intro k
  rfl

theorem run (p : ℕ) (l : EncodedCNF.Literal)
    (saved output count : List Bool) :
    let F := SourceClauseGateMachine.finalSchedule p l saved output count
    let P := SourceClauseGateSuccessor.prepared l.variable.bits p
      saved output count
    ∃ t ≤ 4 * p.bits.length +
        2 * (l.variable.bits.length + p.bits.length + (p + 1).bits.length) +
        SourceLiteralWriter.emitTime
          (SourceLiteralWriter.words (SourceClauseGatePrepare.firstClause p l)) +
        SourceLiteralWriter.emitTime
          (SourceLiteralWriter.words (SourceClauseGatePrepare.secondClause p)) +
        SourceLiteralWriter.emitTime
          (SourceLiteralWriter.words (SourceClauseGatePrepare.thirdClause p l)) + 30,
      ((advance (program l.positive))^[t])
        (⟨some (BitMachineRawSequence.leftLabel
          (BitMachineRawSequence.leftLabel
            SourceClauseGateSuccessor.CopyLabel.scan)),
          ((((), none), none), SourceClauseGateMachine.control),
          SourceClauseGateSuccessor.initial l.variable.bits p.bits
            saved output count⟩ :
          TM2.Cfg (fun _ : Stack => Bool)
            (BitMachineRawSequence.Label
              (BitMachineRawSequence.Label SourceClauseGateSuccessor.CopyLabel
                BinarySuccessorMachine.Label)
              (BitMachineRawSequence.Label
                SourceClauseGateMachine.PrepareLabel
                SourceClauseGateMachine.EmitLabel))
            (((Unit × Option Bool) × Option Bool) ×
              (SourceClauseGateMachine.PrepareControl ×
                SourceClauseGateMachine.EmitControl))) =
        ⟨none, ((((), none), none), SourceClauseGateMachine.control),
          bank embedding P
            (bank SourceClauseGateMachine.embedding
              (SourceClauseGateBroadcast.prepared l.variable.bits p.bits
                (p + 1).bits saved output count) F)⟩ := by
  let P := SourceClauseGateSuccessor.prepared l.variable.bits p saved output count
  let F := SourceClauseGateMachine.finalSchedule p l saved output count
  obtain ⟨t₀, ht₀, h₀⟩ := SourceClauseGateSuccessor.prepare_run
    l.variable.bits p saved output count
  obtain ⟨t₁, ht₁, h₁⟩ := SourceClauseGateMachine.gate_run
    p l saved output count
  have h₁' := BitMachineStackRun.run embedding P
    (SourceClauseGateMachine.fixedProgram l.positive)
    (⟨some (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel
        (BitMachineRawSequence.leftLabel
          SourceClauseGateBroadcast.CopyLabel.scan))),
      SourceClauseGateMachine.control,
      SourceClauseGateBroadcast.initial l.variable.bits p.bits
        (p + 1).bits saved output count⟩ :
      TM2.Cfg (fun _ : SourceClauseGateMachine.Stack => Bool)
        (BitMachineRawSequence.Label
          SourceClauseGateMachine.PrepareLabel SourceClauseGateMachine.EmitLabel)
        (SourceClauseGateMachine.PrepareControl ×
          SourceClauseGateMachine.EmitControl)) t₁
  rw [SourceClauseGateMachine.fixed_program_eq p l] at h₁'
  rw [h₁] at h₁'
  simp only [stackCfg] at h₁'
  rw [writer_initial l.variable.bits p saved output count] at h₁'
  obtain ⟨t, ht, hr⟩ := BitMachineRawSequence.runs
    SourceClauseGateSuccessor.prepareProgram (writer l.positive)
    (BitMachineRawSequence.leftLabel SourceClauseGateSuccessor.CopyLabel.scan)
    (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel
        (BitMachineRawSequence.leftLabel
          SourceClauseGateBroadcast.CopyLabel.scan)))
    (((), none), none) (((), none), none)
    SourceClauseGateMachine.control SourceClauseGateMachine.control
    (SourceClauseGateSuccessor.initial l.variable.bits p.bits
      saved output count)
    P (bank embedding P
      (bank SourceClauseGateMachine.embedding
        (SourceClauseGateBroadcast.prepared l.variable.bits p.bits
          (p + 1).bits saved output count) F))
    t₀ t₁ h₀ h₁'
  exact ⟨t, by omega, hr⟩

end EthInapproximability.CurrentPaper.SourceClauseGateTwoAddress
