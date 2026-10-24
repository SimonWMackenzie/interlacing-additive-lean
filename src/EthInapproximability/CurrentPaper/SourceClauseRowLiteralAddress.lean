import EthInapproximability.CurrentPaper.SourceClauseRowQueryCopy
import EthInapproximability.CurrentPaper.SourceLabelAddressMachine

/-!
# A row query supplies the physical vertex address

For a fixed query position `j`, the checked unary query word is read in place
as the first argument of the multiply-add label machine. Its other arguments
are unary alphabet size and symbol. The whole validated row frame is preserved.
The binary result is the Boolean variable label `query(j) * a + s`.
-/

namespace EthInapproximability.CurrentPaper.SourceClauseRowLiteralAddress

open Turing BitMachineEncoding BitMachineStackEmbedding

abbrev Stack (q : ℕ) :=
  SourceCSPRowQueryFrame.Stack q ⊕ SourceLabelAddressMachine.Stack

noncomputable def embedding {q : ℕ} (j : Fin q) :
    SourceLabelAddressMachine.Stack ↪ Stack q where
  toFun k := if k = (.inl 0 : SourceLabelAddressMachine.Stack) then
      .inl (.inl (j, 1)) else .inr k
  inj' := by
    intro x y h
    by_cases hx : x = (.inl 0 : SourceLabelAddressMachine.Stack)
    · subst x
      by_cases hy : y = (.inl 0 : SourceLabelAddressMachine.Stack)
      · exact hy.symm
      · simp [hy] at h
    · by_cases hy : y = (.inl 0 : SourceLabelAddressMachine.Stack)
      · subst y; simp [hx] at h
      · simpa [hx, hy] using h

noncomputable def initial {q : ℕ}
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (r a s : ℕ) : Stack q → List Bool :=
  Sum.elim row (SourceLabelAddressMachine.inputs r a s)

noncomputable def finalBank {q : ℕ} (j : Fin q)
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (r a s : ℕ) : Stack q → List Bool :=
  bank (embedding j) (initial row r a s)
    (SourceLabelAddressMachine.outputs r a s)

noncomputable def program {q : ℕ} (j : Fin q)
    (l : SourceLabelAddressMachine.Label) :=
  stackStmt (embedding j) (SourceLabelAddressMachine.program l)

theorem initial_bank {q : ℕ} (j : Fin q)
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (r a s : ℕ) (h : row (.inl (j, 1)) = List.replicate r true) :
    bank (embedding j) (initial row r a s)
      (SourceLabelAddressMachine.inputs r a s) = initial row r a s := by
  apply bank_eq_self
  intro k
  by_cases hk : k = (.inl 0 : SourceLabelAddressMachine.Stack)
  · subst k
    simpa [embedding, initial, SourceLabelAddressMachine.inputs,
      SourceLabelAddressMachine.ambient] using h.symm
  · simp [embedding, hk, initial]

theorem run {q : ℕ} (j : Fin q)
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (r a s : ℕ) (h : row (.inl (j, 1)) = List.replicate r true) :
    ∃ t ≤ MatrixAddressMachine.exactTime r a s +
        UnaryBinaryEncoding.coefficient * (r * a + s + 1) ^ 2 + 1,
      ((advance (program j))^[t])
        (⟨some (BitMachineRawSequence.leftLabel .outer),
          (false, (SourceLabelAddressMachine.counter.initial, none)),
          initial row r a s⟩ :
          TM2.Cfg (fun _ : Stack q => Bool)
            SourceLabelAddressMachine.Label SourceLabelAddressMachine.Control) =
        ⟨none, (false, (SourceLabelAddressMachine.counter.initial, none)),
          finalBank j row r a s⟩ := by
  obtain ⟨t, ht, hr⟩ := SourceLabelAddressMachine.label_run r a s
  have he := BitMachineStackRun.run (embedding j) (initial row r a s)
    SourceLabelAddressMachine.program
    (⟨some (BitMachineRawSequence.leftLabel .outer),
      (false, (SourceLabelAddressMachine.counter.initial, none)),
      SourceLabelAddressMachine.inputs r a s⟩ : SourceLabelAddressMachine.Config) t
  rw [hr] at he
  simp only [stackCfg, initial_bank j row r a s h] at he
  exact ⟨t, ht, he⟩

theorem row_preserved {q : ℕ} (j : Fin q)
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (r a s : ℕ) (h : row (.inl (j, 1)) = List.replicate r true)
    (k : SourceCSPRowQueryFrame.Stack q) :
    finalBank j row r a s (.inl k) = row k := by
  by_cases hk : k = .inl (j, 1)
  · subst k
    change finalBank j row r a s (embedding j (.inl 0)) = _
    rw [finalBank, bank_at]
    simpa [SourceLabelAddressMachine.outputs,
      SourceLabelAddressMachine.ambient] using h.symm
  · rw [finalBank, bank_outside]
    · rfl
    · intro ⟨x, hx⟩
      by_cases hx0 : x = (.inl 0 : SourceLabelAddressMachine.Stack)
      · subst x
        exact hk (by simpa [embedding] using hx.symm)
      · simp [embedding, hx0] at hx

theorem binary_result {q : ℕ} (j : Fin q)
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (r a s : ℕ) :
    finalBank j row r a s
      (.inr (.inr (.inl SourceLabelAddressMachine.counter.input))) =
        (r * a + s).bits := by
  have hk : (.inr (.inl SourceLabelAddressMachine.counter.input) :
      SourceLabelAddressMachine.Stack) ≠ .inl 0 := by simp
  change finalBank j row r a s
    (embedding j (.inr (.inl SourceLabelAddressMachine.counter.input))) = _
  rw [finalBank, bank_at]
  simp [SourceLabelAddressMachine.outputs,
    SourceLabelAddressMachine.ambient, SourceUnaryBinaryCall.final_bank]

end EthInapproximability.CurrentPaper.SourceClauseRowLiteralAddress
