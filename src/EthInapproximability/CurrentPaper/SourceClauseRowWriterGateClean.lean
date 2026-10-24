import EthInapproximability.CurrentPaper.SourceClauseRowWriterCleanup

/-!
# One physical OR gate followed by whole-writer cleanup

This is the reusable gate endpoint for later literal-position iteration. Its
cleanup is a real pop loop over the complement of the retained row/accumulator
cells, not a functional reset.
-/

namespace EthInapproximability.CurrentPaper.SourceClauseRowWriterGateClean

open Turing BitMachineEncoding BitMachineStackEmbedding
open scoped Classical

noncomputable def program {q : ℕ} (j : Fin q)
    (a k s t w : ℕ) (sign : Bool) :=
  BitMachineRawSequence.program
    (SourceClauseRowWriterGateRun.program j a k s t w sign)
    (SourceClauseClearExcept.program (SourceClauseRowWriterCleanup.keep q))
    (SourceClauseClearExcept.Label.clear 0)
    (((((((), none), ((), none)), ()), ((), none))),
      ((SourceClauseRowIndexedGate.slotControl, ((), none)),
        SourceClauseRowIndexedGate.gateControl))
    ((), none)

noncomputable def clearCost {q : ℕ}
    (S : SourceClauseRowWriterCleanup.Stack q → List Bool) :=
  (∑ i : Fin (SourceClauseClearExcept.workCount
      (SourceClauseRowWriterCleanup.keep q)),
      (S (SourceClauseClearExcept.workBank
        (SourceClauseRowWriterCleanup.keep q) i)).length) +
    SourceClauseClearExcept.workCount (SourceClauseRowWriterCleanup.keep q) + 2

noncomputable def result {q : ℕ} (j : Fin q)
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r a k s t w : ℕ) (sign : Bool)
    (saved output count : List Bool) :=
  SourceClauseRowWriterCleanup.clean
    (SourceClauseRowWriterGateRun.result j row n r a k s t w sign
      saved output count)

theorem row_cell {q : ℕ} (x : SourceCSPRowQueryFrame.Stack q) :
    SourceClauseRowWriterOperands.gateCell
      (SourceClauseRowGateCleanup.rowCell x) =
    SourceClauseRowWriterCleanup.rowCell x := by
  rw [show SourceClauseRowGateCleanup.rowCell x =
      SourceClauseRowWriterCore.gateCore (.inl x) by rfl]
  rw [SourceClauseRowWriterOperands.gateCell,
    SourceClauseRowWriterCore.gate_cell]
  rfl

theorem saved_cell {q : ℕ} :
    SourceClauseRowWriterOperands.gateCell
      (SourceClauseRowGateCleanup.savedCell (q := q)) =
    SourceClauseRowWriterCleanup.savedCell := by
  rw [show SourceClauseRowGateCleanup.savedCell (q := q) =
      SourceClauseRowWriterCore.gateCore (.inr 0) by rfl]
  rw [SourceClauseRowWriterOperands.gateCell,
    SourceClauseRowWriterCore.gate_cell]
  rfl

theorem count_cell {q : ℕ} :
    SourceClauseRowWriterOperands.gateCell
      (SourceClauseRowGateCleanup.countCell (q := q)) =
    SourceClauseRowWriterCleanup.countCell := by
  rw [show SourceClauseRowGateCleanup.countCell (q := q) =
      SourceClauseRowWriterCore.gateCore (.inr 2) by rfl]
  rw [SourceClauseRowWriterOperands.gateCell,
    SourceClauseRowWriterCore.gate_cell]
  rfl

theorem output_cell {q : ℕ} :
    SourceClauseRowWriterOperands.gateCell
      (SourceClauseRowGateCleanup.outputCell (q := q)) =
    SourceClauseRowWriterCleanup.outputCell := by
  rw [show SourceClauseRowGateCleanup.outputCell (q := q) =
      SourceClauseRowWriterCore.gateCore (.inr 1) by rfl]
  rw [SourceClauseRowWriterOperands.gateCell,
    SourceClauseRowWriterCore.gate_cell]
  rfl

theorem gate_output {q : ℕ} (j : Fin q)
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r a k s t w : ℕ) (sign : Bool)
    (saved output count : List Bool) :
    SourceClauseRowWriterGateRun.result j row n r a k s t w sign
      saved output count
      (SourceClauseRowWriterOperands.gateCell
        SourceClauseRowGateCleanup.outputCell) = output := by
  change (bank (SourceClauseRowWriterGateRun.embedding (q := q))
    (SourceClauseRowWriterStageEcho.prepared j row n r a k s t w
      saved output count)
    (SourceClauseRowIndexedGate.finalBank j row n r a k s t w sign
      saved output count))
      (SourceClauseRowWriterGateRun.embedding
        SourceClauseRowGateCleanup.outputCell) = output
  rw [bank_at]
  change SourceClauseRowIndexedGate.finalBank j row n r a k s t w sign
      saved output count SourceClauseRowGateCleanup.outputCell = output
  simp only [SourceClauseRowGateCleanup.outputCell,
    SourceClauseRowIndexedGate.finalBank, bank_at,
    SourceClauseRowGate.finalBank, bank_at,
    SourceClauseGateSlotAddress.finalBank, bank_at,
    SourceClauseGateAffineAddress.finalBank, bank_at,
    SourceClauseGateTwoAddress.embedding, bank_at,
    SourceClauseGateMachine.embedding, bank_at,
    SourceClauseGateMachine.final_output]

theorem stage_vertex {q : ℕ} (j : Fin q)
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r a k s t w : ℕ) (saved output count : List Bool) :
    SourceClauseRowWriterStageEcho.prepared j row n r a k s t w
      saved output count SourceClauseRowWriterOperands.vertex =
      List.replicate n true := by
  rw [SourceClauseRowWriterStageEcho.prepared,
    SourceClauseRowWriterQueryEcho.after,
    SourceClausePreservingBroadcast.other_preserved]
  · rw [SourceClauseRowWriterStage.gateFinal,
      SourceClauseRowWriterOperands.gateFixedBank,
      SourceClauseFixedBatch.result_outside]
    · rw [SourceClauseRowWriterFanout.afterRow,
        SourceClausePreservingBroadcast.other_preserved]
      · rw [SourceClauseRowWriterFanout.afterVertex,
          SourceClausePreservingBroadcast.source_restored]
        simp [SourceClauseRowWriterOperands.vertex,
          SourceClauseRowWriterOperands.scratch]
      · simp [SourceClauseRowWriterOperands.vertex,
          SourceClauseRowWriterOperands.rowIndex]
      · simp [SourceClauseRowWriterOperands.vertex,
          SourceClauseRowWriterOperands.scratch]
      · simp [SourceClauseRowWriterOperands.gateRowTargets,
          SourceClauseRowWriterOperands.vertex,
          SourceClauseRowWriterOperands.gateCell]
    · intro i; fin_cases i <;>
        simp [SourceClauseRowWriterOperands.gateConstants,
          SourceClauseRowWriterOperands.vertex,
          SourceClauseRowWriterOperands.gateCell]
  · simp [SourceClauseRowWriterOperands.vertex,
      SourceClauseRowWriterQueryEcho.source]
  · simp [SourceClauseRowWriterOperands.vertex,
      SourceClauseRowWriterQueryEcho.temp,
      SourceClauseRowWriterOperands.scratch]
  · simp [SourceClauseRowWriterOperands.vertex,
      SourceClauseRowWriterQueryEcho.target,
      SourceClauseRowWriterOperands.gateCell]

theorem stage_row_index {q : ℕ} (j : Fin q)
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r a k s t w : ℕ) (saved output count : List Bool) :
    SourceClauseRowWriterStageEcho.prepared j row n r a k s t w
      saved output count SourceClauseRowWriterOperands.rowIndex =
      List.replicate r true := by
  rw [SourceClauseRowWriterStageEcho.prepared,
    SourceClauseRowWriterQueryEcho.after,
    SourceClausePreservingBroadcast.other_preserved]
  · rw [SourceClauseRowWriterStage.gateFinal,
      SourceClauseRowWriterOperands.gateFixedBank,
      SourceClauseFixedBatch.result_outside]
    · rw [SourceClauseRowWriterFanout.afterRow,
        SourceClausePreservingBroadcast.source_restored]
      simp [SourceClauseRowWriterOperands.rowIndex,
        SourceClauseRowWriterOperands.scratch]
    · intro i; fin_cases i <;>
        simp [SourceClauseRowWriterOperands.gateConstants,
          SourceClauseRowWriterOperands.rowIndex,
          SourceClauseRowWriterOperands.gateCell]
  · simp [SourceClauseRowWriterOperands.rowIndex,
      SourceClauseRowWriterQueryEcho.source]
  · simp [SourceClauseRowWriterOperands.rowIndex,
      SourceClauseRowWriterQueryEcho.temp,
      SourceClauseRowWriterOperands.scratch]
  · simp [SourceClauseRowWriterOperands.rowIndex,
      SourceClauseRowWriterQueryEcho.target,
      SourceClauseRowWriterOperands.gateCell]

theorem run {q : ℕ} (j : Fin q)
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r a k s t w : ℕ) (sign : Bool)
    (saved output count : List Bool)
    (h : row (.inl (j, 1)) =
      List.replicate (row (.inl (j, 1))).length true) :
    ∃ T ≤ SourceClauseRowWriterGateRun.stageCost j row n r a k s t w +
      SourceClauseRowIndexedGate.cost q n r a k
        (row (.inl (j, 1))).length s t w sign + 1 +
      clearCost (SourceClauseRowWriterGateRun.result j row n r a k s t w
        sign saved output count) + 1,
      ((advance (program j a k s t w sign))^[T])
        (⟨some (BitMachineRawSequence.leftLabel
          (BitMachineRawSequence.leftLabel
            (BitMachineRawSequence.leftLabel
              (BitMachineRawSequence.leftLabel
                (BitMachineRawSequence.leftLabel
                  SourceClausePreservingBroadcast.Label.scan))))),
          ((((((((), none), ((), none)), ()), ((), none))),
            ((SourceClauseRowIndexedGate.slotControl, ((), none)),
              SourceClauseRowIndexedGate.gateControl)), ((), none)),
          SourceClauseRowWriterBlank.bank row n r saved output count⟩) =
        ⟨none,
          ((((((((), none), ((), none)), ()), ((), none))),
            ((SourceClauseRowIndexedGate.slotControl, ((), none)),
              SourceClauseRowIndexedGate.gateControl)), ((), none)),
          result j row n r a k s t w sign saved output count⟩ := by
  obtain ⟨tg, htg, hg⟩ := SourceClauseRowWriterGateRun.run
    j row n r a k s t w sign saved output count h
  have hc := SourceClauseRowWriterCleanup.run
    (SourceClauseRowWriterGateRun.result j row n r a k s t w sign
      saved output count)
  obtain ⟨T, hT, hrun⟩ := BitMachineRawSequence.runs
    (SourceClauseRowWriterGateRun.program j a k s t w sign)
    (SourceClauseClearExcept.program (SourceClauseRowWriterCleanup.keep q))
    (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel
        (BitMachineRawSequence.leftLabel
          (BitMachineRawSequence.leftLabel
            SourceClausePreservingBroadcast.Label.scan))))
    (SourceClauseClearExcept.Label.clear 0)
    (((((((), none), ((), none)), ()), ((), none))),
      ((SourceClauseRowIndexedGate.slotControl, ((), none)),
        SourceClauseRowIndexedGate.gateControl))
    (((((((), none), ((), none)), ()), ((), none))),
      ((SourceClauseRowIndexedGate.slotControl, ((), none)),
        SourceClauseRowIndexedGate.gateControl))
    ((), none) ((), none)
    (SourceClauseRowWriterBlank.bank row n r saved output count)
    (SourceClauseRowWriterGateRun.result j row n r a k s t w sign
      saved output count)
    (result j row n r a k s t w sign saved output count)
    tg (clearCost (SourceClauseRowWriterGateRun.result j row n r a k s t w
      sign saved output count)) hg hc
  exact ⟨T, by dsimp [clearCost] at *; omega, hrun⟩

theorem final_row {q : ℕ} (j : Fin q)
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r a k s t w : ℕ) (sign : Bool)
    (saved output count : List Bool)
    (h : row (.inl (j, 1)) =
      List.replicate (row (.inl (j, 1))).length true)
    (x : SourceCSPRowQueryFrame.Stack q) :
    result j row n r a k s t w sign saved output count
      (SourceClauseRowWriterCleanup.rowCell x) = row x := by
  rw [result, SourceClauseRowWriterCleanup.retained _ _
    (SourceClauseRowWriterCleanup.row_mem x)]
  have he := SourceClauseRowWriterGateRun.final_row
    j row n r a k s t w sign saved output count h x
  rw [row_cell] at he
  exact he

theorem final_count {q : ℕ} (j : Fin q)
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r a k s t w : ℕ) (sign : Bool)
    (saved output count : List Bool) :
    result j row n r a k s t w sign saved output count
      SourceClauseRowWriterCleanup.countCell =
      true :: true :: true :: count := by
  rw [result, SourceClauseRowWriterCleanup.retained _ _
    SourceClauseRowWriterCleanup.count_mem]
  have he := SourceClauseRowWriterGateRun.final_count
    j row n r a k s t w sign saved output count
  rw [count_cell] at he
  exact he

theorem final_output {q : ℕ} (j : Fin q)
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r a k s t w : ℕ) (sign : Bool)
    (saved output count : List Bool) :
    result j row n r a k s t w sign saved output count
      SourceClauseRowWriterCleanup.outputCell = output := by
  rw [result, SourceClauseRowWriterCleanup.retained _ _
    SourceClauseRowWriterCleanup.output_mem]
  have he := gate_output j row n r a k s t w sign saved output count
  rw [output_cell] at he
  exact he

theorem final_saved {q : ℕ} (j : Fin q)
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r a k s t w : ℕ) (sign : Bool)
    (saved output count : List Bool) :
    let p := SourceClauseRowSlotAddress.slot n r a q k * w + (n * a + t)
    result j row n r a k s t w sign saved output count
      SourceClauseRowWriterCleanup.savedCell =
      (EncodedCNF.encodeClause
        (SourceClauseGatePrepare.thirdClause p
          ⟨(row (.inl (j, 1))).length * a + s, sign⟩)).reverse ++
      (EncodedCNF.encodeClause (SourceClauseGatePrepare.secondClause p)).reverse ++
      (EncodedCNF.encodeClause
        (SourceClauseGatePrepare.firstClause p
          ⟨(row (.inl (j, 1))).length * a + s, sign⟩)).reverse ++ saved := by
  rw [result, SourceClauseRowWriterCleanup.retained _ _
    SourceClauseRowWriterCleanup.saved_mem]
  have he := SourceClauseRowWriterGateRun.final_saved
    j row n r a k s t w sign saved output count
  rw [saved_cell] at he
  exact he

theorem final_vertex {q : ℕ} (j : Fin q)
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r a k s t w : ℕ) (sign : Bool)
    (saved output count : List Bool) :
    result j row n r a k s t w sign saved output count
      SourceClauseRowWriterOperands.vertex = List.replicate n true := by
  rw [result, SourceClauseRowWriterCleanup.retained _ _
    SourceClauseRowWriterCleanup.vertex_mem]
  rw [SourceClauseRowWriterGateRun.result]
  rw [bank_outside]
  · exact stage_vertex j row n r a k s t w saved output count
  · rintro ⟨x, hx⟩
    cases hx

theorem final_row_index {q : ℕ} (j : Fin q)
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r a k s t w : ℕ) (sign : Bool)
    (saved output count : List Bool) :
    result j row n r a k s t w sign saved output count
      SourceClauseRowWriterOperands.rowIndex = List.replicate r true := by
  rw [result, SourceClauseRowWriterCleanup.retained _ _
    SourceClauseRowWriterCleanup.row_index_mem]
  rw [SourceClauseRowWriterGateRun.result]
  rw [bank_outside]
  · exact stage_row_index j row n r a k s t w saved output count
  · rintro ⟨x, hx⟩
    cases hx

end EthInapproximability.CurrentPaper.SourceClauseRowWriterGateClean
