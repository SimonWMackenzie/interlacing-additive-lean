import EthInapproximability.CurrentPaper.SourceClauseRowWriterUnitClean
import EthInapproximability.CurrentPaper.SourceClauseRowTruthBranch

/-! The copied truth-table cursor is foreign to the shared clause writer. -/

namespace EthInapproximability.CurrentPaper.SourceClauseRowWriterTruthFrame

open Turing BitMachineEncoding BitMachineStackEmbedding
open scoped Classical

abbrev Stack (q : ℕ) := SourceClauseRowWriterOperands.Stack q ⊕ Fin 2

def rowCell {q : ℕ} (x : SourceCSPRowQueryFrame.Stack q) : Stack q :=
  .inl (SourceClauseRowWriterCleanup.rowCell x)

def truthEmbedding {q : ℕ} : SourceClauseRowTruthCopy.Stack q ↪ Stack q where
  toFun
    | .inl x => rowCell x
    | .inr i => .inr i
  inj' := by
    intro x y h
    cases x with
    | inl x =>
        cases y with
        | inl y =>
            simp [rowCell, SourceClauseRowWriterCleanup.rowCell] at h
            exact congrArg Sum.inl h
        | inr y => simp [rowCell] at h
    | inr x =>
        cases y with
        | inl y => simp [rowCell] at h
        | inr y => simpa using h

def writerEmbedding {q : ℕ} : SourceClauseRowWriterOperands.Stack q ↪ Stack q :=
  ⟨Sum.inl, Sum.inl_injective⟩

noncomputable def initial {q : ℕ}
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r : ℕ) (saved output count : List Bool) : Stack q → List Bool :=
  Sum.elim (SourceClauseRowWriterBlank.bank row n r saved output count)
    (fun _ => [])

theorem initial_truth_bank {q : ℕ}
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r : ℕ) (saved output count : List Bool) :
    bank truthEmbedding (initial row n r saved output count)
      (SourceClauseRowTruthCopy.initial row) =
      initial row n r saved output count := by
  apply bank_eq_self
  intro x
  cases x with
  | inl x =>
      change row x = _
      simp [initial, truthEmbedding, rowCell,
        SourceClauseRowWriterBlank.bank,
        SourceClauseRowWriterBlank.master,
        SourceClauseRowWriterBlank.core,
        SourceClauseRowWriterCleanup.rowCell,
        SourceClauseRowTruthCopy.initial]
  | inr x =>
      fin_cases x <;> rfl

noncomputable def afterCopy {q : ℕ}
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r : ℕ) (saved output count bits : List Bool) : Stack q → List Bool :=
  bank truthEmbedding (initial row n r saved output count)
    (SourceClauseRowTruthCopy.finalBank row bits)

noncomputable def copyProgram {q : ℕ} :=
  fun l => stackStmt (truthEmbedding (q := q))
    (SourceClauseRowTruthCopy.program l)

theorem copy_run {q : ℕ}
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r : ℕ) (saved output count bits : List Bool)
    (h : row (.inr 2) = bits) :
    ((advance (copyProgram (q := q)))^[2 * bits.length + 2])
      (⟨some BitMachineCopy.Label.scan, none,
        initial row n r saved output count⟩) =
      ⟨none, none, afterCopy row n r saved output count bits⟩ := by
  have he := BitMachineStackRun.run truthEmbedding
    (initial row n r saved output count)
    SourceClauseRowTruthCopy.program
    (⟨some BitMachineCopy.Label.scan, none,
      SourceClauseRowTruthCopy.initial row⟩) (2 * bits.length + 2)
  rw [SourceClauseRowTruthCopy.copy_run row bits h] at he
  simpa only [stackCfg, initial_truth_bank, copyProgram, afterCopy] using he

noncomputable def branchProgram {q N : ℕ} (k : Fin N) :=
  fun l => stackStmt (truthEmbedding (q := q))
    (SourceClauseRowTruthBranch.program k l)

noncomputable def afterBranch {q N : ℕ}
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r : ℕ) (saved output count : List Bool)
    (label : Option (SourceClauseRowTruthBranch.Label N))
    (control : Option Bool) (remaining : List Bool) : Stack q → List Bool :=
  bank truthEmbedding (initial row n r saved output count)
    (SourceClauseRowTruthBranch.state row label control remaining).stk

theorem after_copy_branch_input {q N : ℕ}
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r : ℕ) (saved output count : List Bool)
    (table : Fin N → Bool)
    (h : row (.inr 2) = true :: List.ofFn table) :
    afterCopy row n r saved output count (true :: List.ofFn table) =
      afterBranch (N := N) row n r saved output count (some .marker) none
        (true :: List.ofFn table) := by
  unfold afterCopy afterBranch
  rw [SourceClauseRowTruthBranch.copied_ready (N := N) row
    (List.ofFn table) h]

theorem branch_run {q N : ℕ} (k : Fin N)
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r : ℕ) (saved output count : List Bool)
    (table : Fin N → Bool)
    (h : row (.inr 2) = true :: List.ofFn table) :
    ((advance (branchProgram k))^[k.val + 2])
      (⟨some .marker, none,
        afterCopy row n r saved output count
          (true :: List.ofFn table)⟩) =
      ⟨some (SourceClauseRowTruthBranch.choice (table k) N),
        some (table k),
        afterBranch row n r saved output count
          (some (SourceClauseRowTruthBranch.choice (table k) N))
          (some (table k)) ((List.ofFn table).drop (k.val + 1))⟩ := by
  have he := BitMachineStackRun.run truthEmbedding
    (initial row n r saved output count)
    (SourceClauseRowTruthBranch.program k)
    (⟨some .marker, none,
      SourceClauseRowTruthCopy.finalBank row (true :: List.ofFn table)⟩)
    (k.val + 2)
  rw [SourceClauseRowTruthBranch.typed_branch_run k row table h] at he
  simpa only [stackCfg, branchProgram, afterCopy, afterBranch] using he

theorem after_branch_writer {q N : ℕ}
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r : ℕ) (saved output count remaining : List Bool)
    (label : Option (SourceClauseRowTruthBranch.Label N))
    (control : Option Bool)
    (x : SourceClauseRowWriterOperands.Stack q) :
    afterBranch row n r saved output count label control remaining (.inl x) =
      SourceClauseRowWriterBlank.bank row n r saved output count x := by
  cases x with
  | inl y =>
      cases y with
      | inl z =>
          cases z with
          | inl z =>
              change afterBranch row n r saved output count label control
                remaining (truthEmbedding (.inl z)) = _
              rw [afterBranch, bank_at]
              rfl
          | inr i =>
              rw [afterBranch, bank_outside]
              · rfl
              · rintro ⟨z, hz⟩
                cases z <;> simp [truthEmbedding, rowCell,
                  SourceClauseRowWriterCleanup.rowCell] at hz
      | inr z =>
          rw [afterBranch, bank_outside]
          · rfl
          · rintro ⟨y, hy⟩
            cases y <;> simp [truthEmbedding, rowCell,
              SourceClauseRowWriterCleanup.rowCell] at hy
  | inr i =>
      rw [afterBranch, bank_outside]
      · rfl
      · rintro ⟨y, hy⟩
        cases y <;> simp [truthEmbedding, rowCell,
          SourceClauseRowWriterCleanup.rowCell] at hy

end EthInapproximability.CurrentPaper.SourceClauseRowWriterTruthFrame
