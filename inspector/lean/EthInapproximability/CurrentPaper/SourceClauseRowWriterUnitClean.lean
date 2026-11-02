import EthInapproximability.CurrentPaper.SourceClauseRowWriterNormalize
import EthInapproximability.CurrentPaper.SourceClauseRowWriterUnitReady

/-! A staged physical unit clause followed by charged whole-writer cleanup. -/

namespace EthInapproximability.CurrentPaper.SourceClauseRowWriterUnitClean

open Turing BitMachineEncoding BitMachineStackEmbedding
open scoped Classical

noncomputable def program {q : ℕ} (a k w ell : ℕ) (sign : Bool) :=
  BitMachineRawSequence.program
    (SourceClauseRowWriterUnitReady.program (q := q) a k w ell sign)
    (SourceClauseClearExcept.program (SourceClauseRowWriterCleanup.keep q))
    (SourceClauseClearExcept.Label.clear 0)
    (SourceClauseRowWriterUnitReady.stageControl,
      SourceClauseRowUnitMachine.startControl)
    ((), none)

noncomputable def result {q : ℕ}
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r a k w ell : ℕ) (sign : Bool)
    (saved output count : List Bool) :=
  SourceClauseRowWriterCleanup.clean
    (SourceClauseRowWriterUnitReady.unitFinalBank row n r a k w ell sign
      saved output count)

theorem row_cell {q : ℕ} (x : SourceCSPRowQueryFrame.Stack q) :
    SourceClauseRowWriterOperands.unitCell (.inl x) =
      SourceClauseRowWriterCleanup.rowCell x := by
  rw [SourceClauseRowWriterOperands.unitCell,
    ← show SourceClauseRowWriterCore.unitCore (.inl x) =
      (.inl x : SourceClauseRowWriterCore.UnitBank q) from rfl,
    SourceClauseRowWriterCore.unit_cell]
  rfl

theorem saved_cell {q : ℕ} :
    SourceClauseRowWriterOperands.unitCell
      (.inr SourceClauseRowUnitMachine.savedSlot) =
      SourceClauseRowWriterCleanup.savedCell (q := q) := by
  rw [SourceClauseRowWriterOperands.unitCell,
    ← show SourceClauseRowWriterCore.unitCore (.inr 0) =
      (.inr SourceClauseRowUnitMachine.savedSlot :
        SourceClauseRowWriterCore.UnitBank q) from rfl,
    SourceClauseRowWriterCore.unit_cell]
  rfl

theorem output_cell {q : ℕ} :
    SourceClauseRowWriterOperands.unitCell
      (.inr SourceClauseRowUnitMachine.outputSlot) =
      SourceClauseRowWriterCleanup.outputCell (q := q) := by
  rw [SourceClauseRowWriterOperands.unitCell,
    ← show SourceClauseRowWriterCore.unitCore (.inr 1) =
      (.inr SourceClauseRowUnitMachine.outputSlot :
        SourceClauseRowWriterCore.UnitBank q) from rfl,
    SourceClauseRowWriterCore.unit_cell]
  rfl

theorem count_cell {q : ℕ} :
    SourceClauseRowWriterOperands.unitCell
      (.inr SourceClauseRowUnitMachine.countSlot) =
      SourceClauseRowWriterCleanup.countCell (q := q) := by
  rw [SourceClauseRowWriterOperands.unitCell,
    ← show SourceClauseRowWriterCore.unitCore (.inr 2) =
      (.inr SourceClauseRowUnitMachine.countSlot :
        SourceClauseRowWriterCore.UnitBank q) from rfl,
    SourceClauseRowWriterCore.unit_cell]
  rfl

noncomputable def clearCost {q : ℕ}
    (S : SourceClauseRowWriterOperands.Stack q → List Bool) :=
  (∑ i : Fin (SourceClauseClearExcept.workCount
      (SourceClauseRowWriterCleanup.keep q)),
      (S (SourceClauseClearExcept.workBank
        (SourceClauseRowWriterCleanup.keep q) i)).length) +
    SourceClauseClearExcept.workCount (SourceClauseRowWriterCleanup.keep q) + 2

theorem run {q : ℕ}
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r a k w ell : ℕ) (sign : Bool)
    (saved output count : List Bool) :
    ∃ T ≤ SourceClauseRowWriterUnitReady.stageCost q n r a k w ell +
      SourceClauseRowUnitMachine.cost n r a q k w ell + 1 +
      clearCost (SourceClauseRowWriterUnitReady.unitFinalBank
        row n r a k w ell sign saved output count) + 1,
      ((advance (program (q := q) a k w ell sign))^[T])
        (⟨some (BitMachineRawSequence.leftLabel
          (BitMachineRawSequence.leftLabel
            (BitMachineRawSequence.leftLabel
              (BitMachineRawSequence.leftLabel
                SourceClausePreservingBroadcast.Label.scan)))),
          ((SourceClauseRowWriterUnitReady.stageControl,
            SourceClauseRowUnitMachine.startControl), ((), none)),
          SourceClauseRowWriterBlank.bank row n r saved output count⟩) =
        ⟨none,
          ((SourceClauseRowWriterUnitReady.stageControl,
            SourceClauseRowUnitMachine.startControl), ((), none)),
          result row n r a k w ell sign saved output count⟩ := by
  obtain ⟨tu, htu, hu⟩ := SourceClauseRowWriterUnitReady.run
    row n r a k w ell sign saved output count
  have hc := SourceClauseRowWriterCleanup.run
    (SourceClauseRowWriterUnitReady.unitFinalBank
      row n r a k w ell sign saved output count)
  obtain ⟨T, hT, hrun⟩ := BitMachineRawSequence.runs
    (SourceClauseRowWriterUnitReady.program (q := q) a k w ell sign)
    (SourceClauseClearExcept.program (SourceClauseRowWriterCleanup.keep q))
    (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel
        (BitMachineRawSequence.leftLabel
          SourceClausePreservingBroadcast.Label.scan)))
    (SourceClauseClearExcept.Label.clear 0)
    (SourceClauseRowWriterUnitReady.stageControl,
      SourceClauseRowUnitMachine.startControl)
    (SourceClauseRowWriterUnitReady.stageControl,
      SourceClauseRowUnitMachine.startControl)
    ((), none) ((), none)
    (SourceClauseRowWriterBlank.bank row n r saved output count)
    (SourceClauseRowWriterUnitReady.unitFinalBank
      row n r a k w ell sign saved output count)
    (result row n r a k w ell sign saved output count)
    tu (clearCost (SourceClauseRowWriterUnitReady.unitFinalBank
      row n r a k w ell sign saved output count)) hu hc
  exact ⟨T, by dsimp [clearCost] at *; omega, hrun⟩

def unitSaved (q n r a k w ell : ℕ) (sign : Bool)
    (saved : List Bool) : List Bool :=
  (EncodedCNF.encodeClause
    (SourceClauseUnitMachine.unitClause
      (SourceClauseRowUnitMachine.p n r a q k w ell) sign)).reverse ++ saved

theorem unit_blank {q : ℕ}
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r a k w ell : ℕ) (sign : Bool)
    (saved output count : List Bool) :
    result row n r a k w ell sign saved output count =
      SourceClauseRowWriterBlank.bank row n r
        (unitSaved q n r a k w ell sign saved) output (true :: count) := by
  unfold result
  apply SourceClauseRowWriterNormalize.cleanup_blank
  · intro x
    rw [← row_cell]
    exact SourceClauseRowWriterUnitReady.final_row
      row n r a k w ell sign saved output count x
  · rw [← saved_cell]
    exact SourceClauseRowWriterUnitReady.final_saved
      row n r a k w ell sign saved output count
  · rw [← output_cell]
    exact SourceClauseRowWriterUnitReady.final_output
      row n r a k w ell sign saved output count
  · rw [← count_cell]
    exact SourceClauseRowWriterUnitReady.final_count
      row n r a k w ell sign saved output count
  · exact SourceClauseRowWriterUnitReady.final_vertex
      row n r a k w ell sign saved output count
  · exact SourceClauseRowWriterUnitReady.final_row_index
      row n r a k w ell sign saved output count

end EthInapproximability.CurrentPaper.SourceClauseRowWriterUnitClean
