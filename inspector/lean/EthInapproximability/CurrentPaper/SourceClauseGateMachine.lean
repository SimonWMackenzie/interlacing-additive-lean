import EthInapproximability.CurrentPaper.SourceClauseGatePrepare

/-!
# Physically emitting one ordered three-clause prefix-OR gate

This joins physical address broadcast to the three counted literal writers.
The input has three address words, not encoded clauses. Program control uses
only the fixed sign pattern of the gate, while source addresses are on stacks.
-/

namespace EthInapproximability.CurrentPaper.SourceClauseGateMachine

open Turing BitMachineEncoding BitMachineStackEmbedding

abbrev Stack := SourceClauseGateBroadcast.Stack
abbrev PrepareLabel :=
  BitMachineRawSequence.Label
    (BitMachineRawSequence.Label SourceClauseGateBroadcast.CopyLabel
      SourceClauseGateBroadcast.CopyLabel)
    SourceClauseGateBroadcast.CopyLabel
abbrev PrepareControl :=
  (((Unit × Option Bool) × (Unit × Option Bool)) × (Unit × Option Bool))
abbrev EmitLabel :=
  BitMachineRawSequence.Label
    (BitMachineRawSequence.Label SourceClauseCountedStream.Label
      SourceClauseCountedStream.Label)
    SourceClauseCountedStream.Label
abbrev EmitControl :=
  ((SourceClauseCountedStream.Control × SourceClauseCountedStream.Control) ×
    SourceClauseCountedStream.Control)

def control : PrepareControl × EmitControl :=
  ( ((((), none), ((), none)), ((), none)),
    (((none, ()), (none, ())), (none, ())) )

def embedding : SourceClauseGateSchedule.Stack ↪ Stack := Function.Embedding.inr

noncomputable def emitter (p : ℕ) (l : EncodedCNF.Literal)
    (q : EmitLabel) : TM2.Stmt (fun _ : Stack => Bool) EmitLabel EmitControl :=
  stackStmt embedding
    (SourceClauseGateSchedule.program
      (SourceClauseGatePrepare.firstClause p l)
      (SourceClauseGatePrepare.secondClause p)
      (SourceClauseGatePrepare.thirdClause p l) q)

noncomputable def program (p : ℕ) (l : EncodedCNF.Literal) :=
  BitMachineRawSequence.program SourceClauseGatePrepare.program
    (emitter p l)
    (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel
        (BitMachineRawSequence.leftLabel (.begin 0))))
    ((((), none), ((), none)), ((), none))
    (((none, ()), (none, ())), (none, ()))

/-- The numerical addresses are data on the stacks, not program syntax. -/
theorem program_uniform (p : ℕ) (l : EncodedCNF.Literal) :
    program p l = program 0 ⟨0, l.positive⟩ := by
  let l₀ : EncodedCNF.Literal := ⟨0, l.positive⟩
  have h₀ : SourceLiteralWriter.signs (SourceClauseGatePrepare.firstClause p l) =
      SourceLiteralWriter.signs (SourceClauseGatePrepare.firstClause 0 l₀) := by
    funext i; fin_cases i <;> rfl
  have h₁ : SourceLiteralWriter.signs (SourceClauseGatePrepare.secondClause p) =
      SourceLiteralWriter.signs (SourceClauseGatePrepare.secondClause 0) := by
    funext i; fin_cases i <;> rfl
  have h₂ : SourceLiteralWriter.signs (SourceClauseGatePrepare.thirdClause p l) =
      SourceLiteralWriter.signs (SourceClauseGatePrepare.thirdClause 0 l₀) := by
    funext i; fin_cases i <;> rfl
  have he : emitter p l = emitter 0 l₀ := by
    funext q
    simp only [emitter, SourceClauseGateSchedule.program, h₀, h₁, h₂]
  simp only [program, he]
  rfl

/-- Only one input sign bit selects between the two fixed gate programs. -/
noncomputable def fixedProgram (sign : Bool) :=
  program 0 (⟨0, sign⟩ : EncodedCNF.Literal)

theorem fixed_program_eq (p : ℕ) (l : EncodedCNF.Literal) :
    fixedProgram l.positive = program p l := by
  exact (program_uniform p l).symm

theorem prepared_as_bank (p : ℕ) (l : EncodedCNF.Literal)
    (saved output count : List Bool) :
    bank embedding
      (SourceClauseGateBroadcast.prepared l.variable.bits p.bits
        (p + 1).bits saved output count)
      (SourceClauseGateSchedule.contents
        (SourceClauseGateSchedule.initialWords
          (SourceClauseGatePrepare.firstClause p l)
          (SourceClauseGatePrepare.secondClause p)
          (SourceClauseGatePrepare.thirdClause p l))
        saved output count) =
      SourceClauseGateBroadcast.prepared l.variable.bits p.bits
        (p + 1).bits saved output count := by
  apply bank_eq_self
  intro k
  exact congrFun (SourceClauseGatePrepare.prepared_inner p l saved output count) k |>.symm

theorem gate_run (p : ℕ) (l : EncodedCNF.Literal)
    (saved output count : List Bool) :
    let c₀ := SourceClauseGatePrepare.firstClause p l
    let c₁ := SourceClauseGatePrepare.secondClause p
    let c₂ := SourceClauseGatePrepare.thirdClause p l
    let S₀ := SourceClauseGateSchedule.contents
      (SourceClauseGateSchedule.initialWords c₀ c₁ c₂) saved output count
    let S₁ := SourceClauseGateSchedule.after 0 c₀ S₀ saved output count
    let saved₁ := (EncodedCNF.encodeClause c₀).reverse ++ saved
    let S₂ := SourceClauseGateSchedule.after 1 c₁ S₁ saved₁ output (true :: count)
    let saved₂ := (EncodedCNF.encodeClause c₁).reverse ++ saved₁
    let S₃ := SourceClauseGateSchedule.after 2 c₂ S₂ saved₂ output
      (true :: true :: count)
    ∃ t ≤ 2 * (l.variable.bits.length + p.bits.length + (p + 1).bits.length) +
        SourceLiteralWriter.emitTime (SourceLiteralWriter.words c₀) +
        SourceLiteralWriter.emitTime (SourceLiteralWriter.words c₁) +
        SourceLiteralWriter.emitTime (SourceLiteralWriter.words c₂) + 23,
      ((advance (program p l))^[t])
        (⟨some (BitMachineRawSequence.leftLabel
          (BitMachineRawSequence.leftLabel
            (BitMachineRawSequence.leftLabel
              SourceClauseGateBroadcast.CopyLabel.scan))),
          control,
          SourceClauseGateBroadcast.initial l.variable.bits p.bits
            (p + 1).bits saved output count⟩ :
          TM2.Cfg (fun _ : Stack => Bool)
            (BitMachineRawSequence.Label PrepareLabel EmitLabel)
            (PrepareControl × EmitControl)) =
        ⟨none,
          control,
          bank embedding
            (SourceClauseGateBroadcast.prepared l.variable.bits p.bits
              (p + 1).bits saved output count) S₃⟩ := by
  let c₀ := SourceClauseGatePrepare.firstClause p l
  let c₁ := SourceClauseGatePrepare.secondClause p
  let c₂ := SourceClauseGatePrepare.thirdClause p l
  let S₀ := SourceClauseGateSchedule.contents
    (SourceClauseGateSchedule.initialWords c₀ c₁ c₂) saved output count
  let S₁ := SourceClauseGateSchedule.after 0 c₀ S₀ saved output count
  let saved₁ := (EncodedCNF.encodeClause c₀).reverse ++ saved
  let S₂ := SourceClauseGateSchedule.after 1 c₁ S₁ saved₁ output (true :: count)
  let saved₂ := (EncodedCNF.encodeClause c₁).reverse ++ saved₁
  let S₃ := SourceClauseGateSchedule.after 2 c₂ S₂ saved₂ output
    (true :: true :: count)
  let P := SourceClauseGateBroadcast.prepared l.variable.bits p.bits
    (p + 1).bits saved output count
  obtain ⟨t₀, ht₀, h₀⟩ := SourceClauseGatePrepare.run
    l.variable.bits p.bits (p + 1).bits saved output count
  obtain ⟨t₁, ht₁, h₁⟩ := SourceClauseGateSchedule.three_run
    c₀ c₁ c₂ saved output count
  have h₁' := BitMachineStackRun.run embedding P
    (SourceClauseGateSchedule.program c₀ c₁ c₂)
    (⟨some (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel
        (BitMachineRawSequence.leftLabel (.begin 0)))),
      (((none, ()), (none, ())), (none, ())), S₀⟩ :
      TM2.Cfg (fun _ : SourceClauseGateSchedule.Stack => Bool)
        EmitLabel EmitControl) t₁
  rw [h₁] at h₁'
  simp only [stackCfg] at h₁'
  rw [prepared_as_bank p l saved output count] at h₁'
  obtain ⟨t, ht, hr⟩ := BitMachineRawSequence.runs
    SourceClauseGatePrepare.program (emitter p l)
    (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel SourceClauseGateBroadcast.CopyLabel.scan))
    (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel
        (BitMachineRawSequence.leftLabel (.begin 0))))
    ((((), none), ((), none)), ((), none))
    ((((), none), ((), none)), ((), none))
    (((none, ()), (none, ())), (none, ()))
    (((none, ()), (none, ())), (none, ()))
    (SourceClauseGateBroadcast.initial l.variable.bits p.bits
      (p + 1).bits saved output count)
    P (bank embedding P S₃) t₀ t₁ h₀ h₁'
  refine ⟨t, ?_, hr⟩
  dsimp [c₀, c₁, c₂] at ht₁
  omega

noncomputable def finalSchedule (p : ℕ) (l : EncodedCNF.Literal)
    (saved output count : List Bool) :
    SourceClauseGateSchedule.Stack → List Bool :=
  let c₀ := SourceClauseGatePrepare.firstClause p l
  let c₁ := SourceClauseGatePrepare.secondClause p
  let c₂ := SourceClauseGatePrepare.thirdClause p l
  let S₀ := SourceClauseGateSchedule.contents
    (SourceClauseGateSchedule.initialWords c₀ c₁ c₂) saved output count
  let S₁ := SourceClauseGateSchedule.after 0 c₀ S₀ saved output count
  let saved₁ := (EncodedCNF.encodeClause c₀).reverse ++ saved
  let S₂ := SourceClauseGateSchedule.after 1 c₁ S₁ saved₁ output (true :: count)
  let saved₂ := (EncodedCNF.encodeClause c₁).reverse ++ saved₁
  SourceClauseGateSchedule.after 2 c₂ S₂ saved₂ output (true :: true :: count)

theorem final_saved (p : ℕ) (l : EncodedCNF.Literal)
    (saved output count : List Bool) :
    finalSchedule p l saved output count (.inr (.inl 0)) =
      (EncodedCNF.encodeClause (SourceClauseGatePrepare.thirdClause p l)).reverse ++
      (EncodedCNF.encodeClause (SourceClauseGatePrepare.secondClause p)).reverse ++
      (EncodedCNF.encodeClause (SourceClauseGatePrepare.firstClause p l)).reverse ++
      saved := by
  simp only [finalSchedule, SourceClauseGateSchedule.after_saved, List.append_assoc]

theorem final_count (p : ℕ) (l : EncodedCNF.Literal)
    (saved output count : List Bool) :
    finalSchedule p l saved output count (.inr (.inr ())) =
      true :: true :: true :: count := by
  simp only [finalSchedule, SourceClauseGateSchedule.after_count]

theorem final_output (p : ℕ) (l : EncodedCNF.Literal)
    (saved output count : List Bool) :
    finalSchedule p l saved output count (.inr (.inl 1)) = output := by
  simp only [finalSchedule, SourceClauseGateSchedule.after_output]

/-- Observable endpoint: three ordered encoded clauses have been appended to
the reverse accumulator and the physically maintained clause count is +3. -/
theorem gate_run_observable (p : ℕ) (l : EncodedCNF.Literal)
    (saved output count : List Bool) :
    ∃ t ≤ 2 * (l.variable.bits.length + p.bits.length + (p + 1).bits.length) +
        SourceLiteralWriter.emitTime
          (SourceLiteralWriter.words (SourceClauseGatePrepare.firstClause p l)) +
        SourceLiteralWriter.emitTime
          (SourceLiteralWriter.words (SourceClauseGatePrepare.secondClause p)) +
        SourceLiteralWriter.emitTime
          (SourceLiteralWriter.words (SourceClauseGatePrepare.thirdClause p l)) + 23,
      let c := ((advance (program p l))^[t])
        (⟨some (BitMachineRawSequence.leftLabel
          (BitMachineRawSequence.leftLabel
            (BitMachineRawSequence.leftLabel
              SourceClauseGateBroadcast.CopyLabel.scan))),
          control,
          SourceClauseGateBroadcast.initial l.variable.bits p.bits
            (p + 1).bits saved output count⟩ :
          TM2.Cfg (fun _ : Stack => Bool)
            (BitMachineRawSequence.Label PrepareLabel EmitLabel)
            (PrepareControl × EmitControl))
      c.l = none ∧
      c.stk (.inr (.inr (.inl 0))) =
        (EncodedCNF.encodeClause (SourceClauseGatePrepare.thirdClause p l)).reverse ++
        (EncodedCNF.encodeClause (SourceClauseGatePrepare.secondClause p)).reverse ++
        (EncodedCNF.encodeClause (SourceClauseGatePrepare.firstClause p l)).reverse ++
        saved ∧
      c.stk (.inr (.inr (.inr ()))) = true :: true :: true :: count ∧
      c.stk (.inr (.inr (.inl 1))) = output := by
  obtain ⟨t, ht, hr⟩ := gate_run p l saved output count
  refine ⟨t, ht, ?_⟩
  rw [hr]
  refine ⟨rfl, ?_, ?_, ?_⟩
  · change bank embedding
      (SourceClauseGateBroadcast.prepared l.variable.bits p.bits
        (p + 1).bits saved output count)
      (finalSchedule p l saved output count)
      (embedding (.inr (.inl 0))) = _
    rw [bank_at, final_saved]
  · change bank embedding
      (SourceClauseGateBroadcast.prepared l.variable.bits p.bits
        (p + 1).bits saved output count)
      (finalSchedule p l saved output count)
      (embedding (.inr (.inr ()))) = _
    rw [bank_at, final_count]
  · change bank embedding
      (SourceClauseGateBroadcast.prepared l.variable.bits p.bits
        (p + 1).bits saved output count)
      (finalSchedule p l saved output count)
      (embedding (.inr (.inl 1))) = _
    rw [bank_at, final_output]

theorem fixed_gate_run_observable (p : ℕ) (l : EncodedCNF.Literal)
    (saved output count : List Bool) :
    ∃ t ≤ 2 * (l.variable.bits.length + p.bits.length + (p + 1).bits.length) +
        SourceLiteralWriter.emitTime
          (SourceLiteralWriter.words (SourceClauseGatePrepare.firstClause p l)) +
        SourceLiteralWriter.emitTime
          (SourceLiteralWriter.words (SourceClauseGatePrepare.secondClause p)) +
        SourceLiteralWriter.emitTime
          (SourceLiteralWriter.words (SourceClauseGatePrepare.thirdClause p l)) + 23,
      let c := ((advance (fixedProgram l.positive))^[t])
        (⟨some (BitMachineRawSequence.leftLabel
          (BitMachineRawSequence.leftLabel
            (BitMachineRawSequence.leftLabel
              SourceClauseGateBroadcast.CopyLabel.scan))),
          control,
          SourceClauseGateBroadcast.initial l.variable.bits p.bits
            (p + 1).bits saved output count⟩ :
          TM2.Cfg (fun _ : Stack => Bool)
            (BitMachineRawSequence.Label PrepareLabel EmitLabel)
            (PrepareControl × EmitControl))
      c.l = none ∧
      c.stk (.inr (.inr (.inl 0))) =
        (EncodedCNF.encodeClause (SourceClauseGatePrepare.thirdClause p l)).reverse ++
        (EncodedCNF.encodeClause (SourceClauseGatePrepare.secondClause p)).reverse ++
        (EncodedCNF.encodeClause (SourceClauseGatePrepare.firstClause p l)).reverse ++
        saved ∧
      c.stk (.inr (.inr (.inr ()))) = true :: true :: true :: count ∧
      c.stk (.inr (.inr (.inl 1))) = output := by
  simpa only [fixed_program_eq p l] using
    gate_run_observable p l saved output count

end EthInapproximability.CurrentPaper.SourceClauseGateMachine
