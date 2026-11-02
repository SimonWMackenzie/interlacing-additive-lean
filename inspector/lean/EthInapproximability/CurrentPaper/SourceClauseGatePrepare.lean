import EthInapproximability.CurrentPaper.SourceClauseGateBroadcast

/-!
# One physical preparation program for a three-CNF OR gate

Three fixed broadcasts copy the three original address words into the nine
ordered literal work slots. Only the three source addresses, accumulator,
count, and output suffix are initially supplied.
-/

namespace EthInapproximability.CurrentPaper.SourceClauseGatePrepare

open Turing BitMachineEncoding SourceClauseGateBroadcast

noncomputable def program :=
  BitMachineRawSequence.program
    (BitMachineRawSequence.program
      (copyProgram literalSource literalTargets)
      (copyProgram prefixSource prefixTargets)
      CopyLabel.scan ((), none) ((), none))
    (copyProgram successorSource successorTargets)
    CopyLabel.scan
    (((), none), ((), none)) ((), none)

theorem run (literal baseWord successor saved output count : List Bool) :
    ∃ t ≤ 2 * (literal.length + baseWord.length + successor.length) + 11,
      ((advance program)^[t])
        (⟨some (BitMachineRawSequence.leftLabel
          (BitMachineRawSequence.leftLabel CopyLabel.scan)),
          ((((), none), ((), none)), ((), none)),
          initial literal baseWord successor saved output count⟩ :
          TM2.Cfg (fun _ : Stack => Bool)
            (BitMachineRawSequence.Label
              (BitMachineRawSequence.Label CopyLabel CopyLabel) CopyLabel)
            (((Unit × Option Bool) × (Unit × Option Bool)) ×
              (Unit × Option Bool))) =
        ⟨none, ((((), none), ((), none)), ((), none)),
          prepared literal baseWord successor saved output count⟩ := by
  let S₀ := initial literal baseWord successor saved output count
  let S₁ := first literal S₀
  let S₂ := second baseWord S₁
  let S₃ := third successor S₂
  have h₀ := first_run literal baseWord successor saved output count
  have h₁ := second_run literal baseWord successor saved output count
  have h₂ := third_run literal baseWord successor saved output count
  dsimp only at h₁ h₂
  obtain ⟨t₀₁, ht₀₁, h₀₁⟩ := BitMachineRawSequence.runs
    (copyProgram literalSource literalTargets)
    (copyProgram prefixSource prefixTargets)
    CopyLabel.scan CopyLabel.scan ((), none) ((), none) ((), none) ((), none)
    S₀ S₁ S₂ (2 * literal.length + 3) (2 * baseWord.length + 3) h₀ h₁
  obtain ⟨t, ht, hr⟩ := BitMachineRawSequence.runs
    (BitMachineRawSequence.program
      (copyProgram literalSource literalTargets)
      (copyProgram prefixSource prefixTargets)
      CopyLabel.scan ((), none) ((), none))
    (copyProgram successorSource successorTargets)
    (BitMachineRawSequence.leftLabel CopyLabel.scan) CopyLabel.scan
    (((), none), ((), none)) (((), none), ((), none))
    ((), none) ((), none)
    S₀ S₂ S₃ t₀₁ (2 * successor.length + 3) h₀₁ h₂
  exact ⟨t, by omega, hr⟩

def firstClause (p : ℕ) (l : EncodedCNF.Literal) : EncodedCNF.Clause :=
  ⟨SourceClauseEncoding.negate l,
    SourceClauseEncoding.positive (p + 1),
    SourceClauseEncoding.positive (p + 1)⟩

def secondClause (p : ℕ) : EncodedCNF.Clause :=
  ⟨SourceClauseEncoding.negative p,
    SourceClauseEncoding.positive (p + 1),
    SourceClauseEncoding.positive (p + 1)⟩

def thirdClause (p : ℕ) (l : EncodedCNF.Literal) : EncodedCNF.Clause :=
  ⟨l, SourceClauseEncoding.positive p,
    SourceClauseEncoding.negative (p + 1)⟩

theorem clauses_eq_orGate (p : ℕ) (l : EncodedCNF.Literal) :
    [firstClause p l, secondClause p, thirdClause p l] =
      SourceClauseEncoding.orGate p l := rfl

theorem prepared_inner (p : ℕ) (l : EncodedCNF.Literal)
    (saved output count : List Bool) :
    (fun k => prepared l.variable.bits p.bits (p + 1).bits
      saved output count (.inr k)) =
      SourceClauseGateSchedule.contents
        (SourceClauseGateSchedule.initialWords
          (firstClause p l) (secondClause p) (thirdClause p l))
        saved output count := by
  funext k
  cases k with
  | inl i =>
      change prepared l.variable.bits p.bits (p + 1).bits saved output count
        (word i) = _
      rw [prepared_word]
      fin_cases i <;>
        simp [SourceClauseGateSchedule.initialWords,
          SourceLiteralWriter.words, firstClause, secondClause, thirdClause,
          SourceClauseEncoding.negative, SourceClauseEncoding.positive,
          SourceClauseEncoding.negate, SourceClauseGateSchedule.contents]
  | inr j =>
      cases j with
      | inl i =>
          fin_cases i
          · exact prepared_saved ..
          · exact prepared_output ..
      | inr _ => exact prepared_count ..

end EthInapproximability.CurrentPaper.SourceClauseGatePrepare
