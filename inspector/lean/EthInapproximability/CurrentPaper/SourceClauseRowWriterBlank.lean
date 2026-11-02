import EthInapproximability.CurrentPaper.SourceClauseRowWriterRowAdvance

/-!
# Clean row-writer bank with persistent typed data

Only the checked source-row frame, three writer cells, and unary n/r words
are initially populated. Every arithmetic and transfer scratch cell is empty.
This is the entry shape for physical operand staging, not a supplied CNF.
-/

namespace EthInapproximability.CurrentPaper.SourceClauseRowWriterBlank

open scoped Classical

noncomputable def core {q : ℕ}
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (saved output count : List Bool) :
    SourceClauseRowWriterCore.Core q → List Bool :=
  Sum.elim row ![saved, output, count]

noncomputable def master {q : ℕ}
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (saved output count : List Bool) :
    SourceClauseRowWriterCore.Stack q → List Bool :=
  Sum.elim (core row saved output count) (fun _ => [])

noncomputable def bank {q : ℕ}
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r : ℕ) (saved output count : List Bool) :
    SourceClauseRowWriterOperands.Stack q → List Bool :=
  Sum.elim (master row saved output count)
    ![List.replicate n true, List.replicate r true, []]

theorem vertex {q : ℕ}
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r : ℕ) (saved output count : List Bool) :
    bank row n r saved output count SourceClauseRowWriterOperands.vertex =
      List.replicate n true := rfl

theorem row_index {q : ℕ}
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r : ℕ) (saved output count : List Bool) :
    bank row n r saved output count SourceClauseRowWriterOperands.rowIndex =
      List.replicate r true := rfl

theorem scratch {q : ℕ}
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r : ℕ) (saved output count : List Bool) :
    bank row n r saved output count SourceClauseRowWriterOperands.scratch =
      [] := rfl

theorem core_word {q : ℕ}
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r : ℕ) (saved output count : List Bool)
    (c : SourceClauseRowWriterCore.Core q) :
    bank row n r saved output count
      (.inl (.inl c)) = core row saved output count c := rfl

theorem row_word {q : ℕ}
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r : ℕ) (saved output count : List Bool)
    (x : SourceCSPRowQueryFrame.Stack q) :
    bank row n r saved output count
      (.inl (SourceClauseRowWriterCore.gateEmbedding
        (SourceClauseRowWriterCore.gateCore (.inl x)))) = row x := by
  rw [SourceClauseRowWriterCore.gate_cell]
  rfl

theorem saved_word {q : ℕ}
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r : ℕ) (saved output count : List Bool) :
    bank row n r saved output count
      (.inl (SourceClauseRowWriterCore.gateEmbedding
        (SourceClauseRowWriterCore.gateCore (.inr 0)))) = saved := by
  rw [SourceClauseRowWriterCore.gate_cell]
  rfl

theorem output_word {q : ℕ}
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r : ℕ) (saved output count : List Bool) :
    bank row n r saved output count
      (.inl (SourceClauseRowWriterCore.gateEmbedding
        (SourceClauseRowWriterCore.gateCore (.inr 1)))) = output := by
  rw [SourceClauseRowWriterCore.gate_cell]
  rfl

theorem count_word {q : ℕ}
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r : ℕ) (saved output count : List Bool) :
    bank row n r saved output count
      (.inl (SourceClauseRowWriterCore.gateEmbedding
        (SourceClauseRowWriterCore.gateCore (.inr 2)))) = count := by
  rw [SourceClauseRowWriterCore.gate_cell]
  rfl

theorem gate_scratch_empty {q : ℕ}
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r : ℕ) (saved output count : List Bool)
    (x : SourceClauseRowWriterCore.Gate q)
    (hx : x ∉ Set.range (SourceClauseRowWriterCore.gateCore (q := q))) :
    bank row n r saved output count
      (SourceClauseRowWriterOperands.gateCell x) = [] := by
  have he : SourceClauseRowWriterCore.gateEmbedding x =
      .inr (.inl ⟨x, hx⟩) := by
    exact SourceClauseSharedCore.left_outside
      SourceClauseRowWriterCore.gateCore SourceClauseRowWriterCore.unitCore x hx
  simp [bank, master, SourceClauseRowWriterOperands.gateCell, he]

theorem unit_scratch_empty {q : ℕ}
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r : ℕ) (saved output count : List Bool)
    (x : SourceClauseRowWriterCore.UnitBank q)
    (hx : x ∉ Set.range (SourceClauseRowWriterCore.unitCore (q := q))) :
    bank row n r saved output count
      (SourceClauseRowWriterOperands.unitCell x) = [] := by
  have he : SourceClauseRowWriterCore.unitEmbedding x =
      .inr (.inr ⟨x, hx⟩) := by
    exact SourceClauseSharedCore.right_outside
      SourceClauseRowWriterCore.gateCore SourceClauseRowWriterCore.unitCore x hx
  simp [bank, master, SourceClauseRowWriterOperands.unitCell, he]

end EthInapproximability.CurrentPaper.SourceClauseRowWriterBlank
