import EthInapproximability.CurrentPaper.SourceClauseRowWriterTruthFrame
import EthInapproximability.CurrentPaper.SourceClauseRowTruthFlag

/-! The selected truth bit is physically retained while emitters run. -/

namespace EthInapproximability.CurrentPaper.SourceClauseRowWriterTruthFlagFrame

open Turing BitMachineEncoding BitMachineStackEmbedding
open scoped Classical

noncomputable def program {q N : ℕ} (k : Fin N) :=
  fun l => stackStmt (SourceClauseRowWriterTruthFrame.truthEmbedding (q := q))
    (SourceClauseRowTruthFlag.program k l)

noncomputable def afterFlag {q : ℕ}
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r : ℕ) (saved output count : List Bool)
    (b : Bool) (remaining : List Bool) :
    SourceClauseRowWriterTruthFrame.Stack q → List Bool :=
  bank SourceClauseRowWriterTruthFrame.truthEmbedding
    (SourceClauseRowWriterTruthFrame.initial row n r saved output count)
    (SourceClauseRowTruthFlag.flagged row b remaining)

theorem run {q N : ℕ} (k : Fin N)
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r : ℕ) (saved output count : List Bool)
    (table : Fin N → Bool)
    (h : row (.inr 2) = true :: List.ofFn table) :
    ((advance (program k))^[k.val + 3])
      (⟨some .marker, none,
        SourceClauseRowWriterTruthFrame.afterCopy row n r saved output count
          (true :: List.ofFn table)⟩) =
      ⟨none, some (table k),
        afterFlag row n r saved output count (table k)
          ((List.ofFn table).drop (k.val + 1))⟩ := by
  have he := BitMachineStackRun.run
    SourceClauseRowWriterTruthFrame.truthEmbedding
    (SourceClauseRowWriterTruthFrame.initial row n r saved output count)
    (SourceClauseRowTruthFlag.program k)
    (⟨some .marker, none,
      SourceClauseRowTruthCopy.finalBank row (true :: List.ofFn table)⟩)
    (k.val + 3)
  rw [SourceClauseRowTruthFlag.typed_flag_run k row table h] at he
  simpa only [stackCfg, program, SourceClauseRowWriterTruthFrame.afterCopy,
    afterFlag] using he

theorem flag_bit {q : ℕ}
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r : ℕ) (saved output count : List Bool)
    (b : Bool) (remaining : List Bool) :
    afterFlag row n r saved output count b remaining (.inr 1) = [b] := by
  change afterFlag row n r saved output count b remaining
    (SourceClauseRowWriterTruthFrame.truthEmbedding (.inr 1)) = [b]
  rw [afterFlag, bank_at]
  simp [SourceClauseRowTruthFlag.flagged, Function.update]

theorem writer_unchanged {q : ℕ}
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r : ℕ) (saved output count : List Bool)
    (b : Bool) (remaining : List Bool)
    (x : SourceClauseRowWriterOperands.Stack q) :
    afterFlag row n r saved output count b remaining (.inl x) =
      SourceClauseRowWriterBlank.bank row n r saved output count x := by
  cases x with
  | inl y =>
      cases y with
      | inl z =>
          cases z with
          | inl z =>
              change afterFlag row n r saved output count b remaining
                (SourceClauseRowWriterTruthFrame.truthEmbedding (.inl z)) = _
              rw [afterFlag, bank_at]
              simp [SourceClauseRowTruthFlag.flagged,
                SourceClauseRowWriterBlank.bank,
                SourceClauseRowWriterBlank.master,
                SourceClauseRowWriterBlank.core,
                Function.update]
          | inr i =>
              rw [afterFlag, bank_outside]
              · rfl
              · rintro ⟨z, hz⟩
                cases z <;> simp [SourceClauseRowWriterTruthFrame.truthEmbedding,
                  SourceClauseRowWriterTruthFrame.rowCell,
                  SourceClauseRowWriterCleanup.rowCell] at hz
      | inr z =>
          rw [afterFlag, bank_outside]
          · rfl
          · rintro ⟨y, hy⟩
            cases y <;> simp [SourceClauseRowWriterTruthFrame.truthEmbedding,
              SourceClauseRowWriterTruthFrame.rowCell,
              SourceClauseRowWriterCleanup.rowCell] at hy
  | inr i =>
      rw [afterFlag, bank_outside]
      · rfl
      · rintro ⟨y, hy⟩
        cases y <;> simp [SourceClauseRowWriterTruthFrame.truthEmbedding,
          SourceClauseRowWriterTruthFrame.rowCell,
          SourceClauseRowWriterCleanup.rowCell] at hy

end EthInapproximability.CurrentPaper.SourceClauseRowWriterTruthFlagFrame
