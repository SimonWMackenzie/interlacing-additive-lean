import EthInapproximability.CurrentPaper.SourceClauseCountFinalize

/-!
# Three-stage physical prefix-OR gate schedule

Source: frozen v8 `06-eth.tex`, ordered prefix-chain translation.
This module schedules three already proved counted clause writers on one
Boolean-stack bank. Its input is an internal nine-word work bank containing
the literal addresses of one OR gate; a separate physical broadcast stage
must produce that bank from the three source addresses before this schedule
is a complete gate machine. It does not accept encoded clauses or output bits.
-/

namespace EthInapproximability.CurrentPaper.SourceClauseGateSchedule

open Turing BitMachineEncoding BitMachineStackEmbedding

abbrev Stack := Fin 9 ⊕ (Fin 2 ⊕ Unit)

def contents (words : Fin 9 → List Bool) (saved output count : List Bool) :
    Stack → List Bool := Sum.elim words (Sum.elim ![saved, output] (fun _ => count))

noncomputable def select (i : Fin 3) : SourceClauseCountedStream.Stack ↪ Stack where
  toFun
    | .inl k => if h : k.val < 3 then .inl ⟨3 * i.val + k.val, by omega⟩
      else if k = 3 then .inr (.inl 0) else .inr (.inl 1)
    | .inr _ => .inr (.inr ())
  inj' := by
    intro k l h
    fin_cases i <;> fin_cases k <;> fin_cases l <;>
      simp_all [Fin.ext_iff]

noncomputable def stageProgram (i : Fin 3) (sign : Fin 3 → Bool)
    (l : SourceClauseCountedStream.Label) :=
  stackStmt (select i) (SourceClauseCountedStream.program sign l)

def positions (i : Fin 3) (c : EncodedCNF.Clause) : Fin 9 → List Bool :=
  fun k => if k.val = 3 * i.val then c.first.variable.bits
    else if k.val = 3 * i.val + 1 then c.second.variable.bits
    else if k.val = 3 * i.val + 2 then c.third.variable.bits else []

def supplied (i : Fin 3) (c : EncodedCNF.Clause)
    (S : Stack → List Bool) (saved output count : List Bool) : Prop :=
  (∀ j : Fin 3, S ((select i) (.inl ⟨j.val, by omega⟩)) =
    SourceLiteralWriter.words c j) ∧
  S (.inr (.inl 0)) = saved ∧ S (.inr (.inl 1)) = output ∧
    S (.inr (.inr ())) = count

noncomputable def after (i : Fin 3) (c : EncodedCNF.Clause)
    (S : Stack → List Bool) (saved output count : List Bool) : Stack → List Bool :=
  bank (select i) S
    (SourceClauseCountedStream.contents
      (SourceLiteralWriter.cfg none none (fun _ => [])
        ((EncodedCNF.encodeClause c).reverse ++ saved) output).stk
      (true :: count))

theorem stage_initial (i : Fin 3) (c : EncodedCNF.Clause)
    (S : Stack → List Bool) (saved output count : List Bool)
    (h : supplied i c S saved output count) :
    bank (select i) S
      (SourceClauseCountedStream.contents
        (SourceLiteralWriter.cfg (some (.begin 0)) none
          (SourceLiteralWriter.words c) saved output).stk count) = S := by
  apply bank_eq_self
  intro k
  cases k with
  | inr u => cases u; exact h.2.2.2.symm
  | inl j =>
      fin_cases j
      · exact (h.1 0).symm
      · exact (h.1 1).symm
      · exact (h.1 2).symm
      · exact h.2.1.symm
      · exact h.2.2.1.symm

theorem stage_run (i : Fin 3) (c : EncodedCNF.Clause)
    (S : Stack → List Bool) (saved output count : List Bool)
    (h : supplied i c S saved output count) :
    ∃ t ≤ SourceLiteralWriter.emitTime (SourceLiteralWriter.words c) + 3,
      ((advance (stageProgram i (SourceLiteralWriter.signs c)))^[t])
        (⟨some (BitMachineRawSequence.leftLabel (.begin 0)), (none, ()), S⟩ :
          TM2.Cfg (fun _ : Stack => Bool) SourceClauseCountedStream.Label
            SourceClauseCountedStream.Control) =
        ⟨none, (none, ()), after i c S saved output count⟩ := by
  obtain ⟨t, ht, hr⟩ := SourceClauseCountedStream.counted_clause c saved output count
  have he := BitMachineStackRun.run (select i) S
    (SourceClauseCountedStream.program (SourceLiteralWriter.signs c))
    (⟨some (BitMachineRawSequence.leftLabel (.begin 0)), (none, ()),
      SourceClauseCountedStream.contents
        (SourceLiteralWriter.cfg (some (.begin 0)) none
          (SourceLiteralWriter.words c) saved output).stk count⟩ :
          SourceClauseCountedStream.Config) t
  rw [hr] at he
  simp only [stackCfg, stage_initial i c S saved output count h] at he
  exact ⟨t, ht, he⟩

theorem after_saved (i : Fin 3) (c : EncodedCNF.Clause)
    (S : Stack → List Bool) (saved output count : List Bool) :
    after i c S saved output count (.inr (.inl 0)) =
      (EncodedCNF.encodeClause c).reverse ++ saved := by
  change after i c S saved output count ((select i) (.inl 3)) = _
  rw [after, bank_at]
  rfl

theorem after_output (i : Fin 3) (c : EncodedCNF.Clause)
    (S : Stack → List Bool) (saved output count : List Bool) :
    after i c S saved output count (.inr (.inl 1)) = output := by
  change after i c S saved output count ((select i) (.inl 4)) = _
  rw [after, bank_at]
  rfl

theorem after_count (i : Fin 3) (c : EncodedCNF.Clause)
    (S : Stack → List Bool) (saved output count : List Bool) :
    after i c S saved output count (.inr (.inr ())) = true :: count := by
  change after i c S saved output count ((select i) (.inr ())) = _
  rw [after, bank_at]
  rfl

theorem after_other_words (i j : Fin 3) (hij : i ≠ j)
    (c : EncodedCNF.Clause) (S : Stack → List Bool)
    (saved output count : List Bool) (k : Fin 3) :
    after i c S saved output count ((select j) (.inl ⟨k.val, by omega⟩)) =
      S ((select j) (.inl ⟨k.val, by omega⟩)) := by
  unfold after
  rw [bank_outside]
  intro ⟨u, hu⟩
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases u <;>
    simp_all [select]

theorem supplied_after (i j : Fin 3) (hij : i ≠ j)
    (c d : EncodedCNF.Clause) (S : Stack → List Bool)
    (saved output count : List Bool)
    (h : supplied j d S saved output count) :
    supplied j d (after i c S saved output count)
      ((EncodedCNF.encodeClause c).reverse ++ saved) output (true :: count) := by
  refine ⟨?_, after_saved i c S saved output count,
    after_output i c S saved output count,
    after_count i c S saved output count⟩
  intro k
  rw [after_other_words i j hij c S saved output count k]
  exact h.1 k

def initialWords (c₀ c₁ c₂ : EncodedCNF.Clause) : Fin 9 → List Bool :=
  fun k => if h : k.val < 3 then SourceLiteralWriter.words c₀ ⟨k.val, h⟩
    else if h : k.val < 6 then SourceLiteralWriter.words c₁ ⟨k.val - 3, by omega⟩
    else SourceLiteralWriter.words c₂ ⟨k.val - 6, by omega⟩

theorem initial_supplied (i : Fin 3) (c₀ c₁ c₂ : EncodedCNF.Clause)
    (saved output count : List Bool) :
    supplied i (![c₀, c₁, c₂] i)
      (contents (initialWords c₀ c₁ c₂) saved output count)
      saved output count := by
  refine ⟨?_, rfl, rfl, rfl⟩
  intro k
  fin_cases i <;> fin_cases k <;>
    simp [supplied, select, contents, initialWords, SourceLiteralWriter.words]

noncomputable def program (c₀ c₁ c₂ : EncodedCNF.Clause) :=
  BitMachineRawSequence.program
    (BitMachineRawSequence.program
      (stageProgram 0 (SourceLiteralWriter.signs c₀))
      (stageProgram 1 (SourceLiteralWriter.signs c₁))
      (BitMachineRawSequence.leftLabel (.begin 0)) (none, ()) (none, ()))
    (stageProgram 2 (SourceLiteralWriter.signs c₂))
    (BitMachineRawSequence.leftLabel (.begin 0))
    ((none, ()), (none, ())) (none, ())

/-- Three counted clause writers run in order on one fixed finite bank.
The nine internal variable words are consumed; the accumulator and unary
count reflect all three actual writes. Producing the nine words from the
three original gate addresses is the remaining preparation subroutine. -/
theorem three_run (c₀ c₁ c₂ : EncodedCNF.Clause)
    (saved output count : List Bool) :
    let S₀ := contents (initialWords c₀ c₁ c₂) saved output count
    let S₁ := after 0 c₀ S₀ saved output count
    let saved₁ := (EncodedCNF.encodeClause c₀).reverse ++ saved
    let S₂ := after 1 c₁ S₁ saved₁ output (true :: count)
    let saved₂ := (EncodedCNF.encodeClause c₁).reverse ++ saved₁
    let S₃ := after 2 c₂ S₂ saved₂ output (true :: true :: count)
    ∃ t ≤ SourceLiteralWriter.emitTime (SourceLiteralWriter.words c₀) +
        SourceLiteralWriter.emitTime (SourceLiteralWriter.words c₁) +
        SourceLiteralWriter.emitTime (SourceLiteralWriter.words c₂) + 11,
      ((advance (program c₀ c₁ c₂))^[t])
        (⟨some (BitMachineRawSequence.leftLabel
            (BitMachineRawSequence.leftLabel
              (BitMachineRawSequence.leftLabel (.begin 0)))),
          (((none, ()), (none, ())), (none, ())), S₀⟩ :
          TM2.Cfg (fun _ : Stack => Bool)
            (BitMachineRawSequence.Label
              (BitMachineRawSequence.Label SourceClauseCountedStream.Label
                SourceClauseCountedStream.Label) SourceClauseCountedStream.Label)
            ((SourceClauseCountedStream.Control × SourceClauseCountedStream.Control) ×
              SourceClauseCountedStream.Control)) =
        ⟨none, (((none, ()), (none, ())), (none, ())), S₃⟩ := by
  dsimp only
  let S₀ := contents (initialWords c₀ c₁ c₂) saved output count
  let S₁ := after 0 c₀ S₀ saved output count
  let saved₁ := (EncodedCNF.encodeClause c₀).reverse ++ saved
  let S₂ := after 1 c₁ S₁ saved₁ output (true :: count)
  let saved₂ := (EncodedCNF.encodeClause c₁).reverse ++ saved₁
  let S₃ := after 2 c₂ S₂ saved₂ output (true :: true :: count)
  obtain ⟨t₀, ht₀, h₀⟩ := stage_run 0 c₀ S₀ saved output count
    (initial_supplied 0 c₀ c₁ c₂ saved output count)
  have hready₁ : supplied 1 c₁ S₁ saved₁ output (true :: count) :=
    supplied_after 0 1 (by decide) c₀ c₁ S₀ saved output count
      (initial_supplied 1 c₀ c₁ c₂ saved output count)
  obtain ⟨t₁, ht₁, h₁⟩ := stage_run 1 c₁ S₁ saved₁ output (true :: count) hready₁
  have hready₂a : supplied 2 c₂ S₁ saved₁ output (true :: count) :=
    supplied_after 0 2 (by decide) c₀ c₂ S₀ saved output count
      (initial_supplied 2 c₀ c₁ c₂ saved output count)
  have hready₂ : supplied 2 c₂ S₂ saved₂ output (true :: true :: count) :=
    supplied_after 1 2 (by decide) c₁ c₂ S₁ saved₁ output (true :: count)
      hready₂a
  obtain ⟨t₂, ht₂, h₂⟩ := stage_run 2 c₂ S₂ saved₂ output
    (true :: true :: count) hready₂
  obtain ⟨t₀₁, ht₀₁, h₀₁⟩ := BitMachineRawSequence.runs
    (stageProgram 0 (SourceLiteralWriter.signs c₀))
    (stageProgram 1 (SourceLiteralWriter.signs c₁))
    (BitMachineRawSequence.leftLabel (.begin 0))
    (BitMachineRawSequence.leftLabel (.begin 0))
    (none, ()) (none, ()) (none, ()) (none, ())
    S₀ S₁ S₂ t₀ t₁ h₀ h₁
  obtain ⟨t, ht, hr⟩ := BitMachineRawSequence.runs
    (BitMachineRawSequence.program
      (stageProgram 0 (SourceLiteralWriter.signs c₀))
      (stageProgram 1 (SourceLiteralWriter.signs c₁))
      (BitMachineRawSequence.leftLabel (.begin 0)) (none, ()) (none, ()))
    (stageProgram 2 (SourceLiteralWriter.signs c₂))
    (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel (.begin 0)))
    (BitMachineRawSequence.leftLabel (.begin 0))
    ((none, ()), (none, ())) ((none, ()), (none, ()))
    (none, ()) (none, ())
    S₀ S₂ S₃ t₀₁ t₂ h₀₁ h₂
  exact ⟨t, by omega, hr⟩

end EthInapproximability.CurrentPaper.SourceClauseGateSchedule
