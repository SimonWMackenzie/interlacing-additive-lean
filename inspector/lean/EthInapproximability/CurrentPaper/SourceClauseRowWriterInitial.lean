import EthInapproximability.CurrentPaper.SourceClauseRowWriterStageReady

/-!
# Exact initial-bank compatibility for staged physical clause writers

The staged words are compared with the actual input banks of the gate and
unit machines, not with a separately supplied clause list.
-/

namespace EthInapproximability.CurrentPaper.SourceClauseRowWriterInitial

open scoped Classical

theorem gate_other_empty {q : ℕ}
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r a k s t w : ℕ) (saved output count : List Bool)
    (x : SourceClauseRowWriterCore.Gate q)
    (hcore : x ∉ Set.range (SourceClauseRowWriterCore.gateCore (q := q)))
    (hfixed : ∀ j : Fin 8,
      SourceClauseRowWriterOperands.gateConstants j ≠
        SourceClauseRowWriterOperands.gateCell x)
    (hn : SourceClauseRowWriterOperands.gateCell x ∉
      SourceClauseRowWriterOperands.gateVertexTargets)
    (hr : SourceClauseRowWriterOperands.gateCell x ∉
      SourceClauseRowWriterOperands.gateRowTargets) :
    SourceClauseRowWriterStage.gateFinal n r a k s t w
      (SourceClauseRowWriterBlank.bank row n r saved output count)
      (SourceClauseRowWriterOperands.gateCell x) = [] := by
  rw [SourceClauseRowWriterStageReady.gate_final_other n r a k s t w
    (SourceClauseRowWriterBlank.bank row n r saved output count)
    (SourceClauseRowWriterOperands.gateCell x) hfixed hn hr
    (by simp [SourceClauseRowWriterOperands.gateCell,
      SourceClauseRowWriterOperands.vertex])
    (by simp [SourceClauseRowWriterOperands.gateCell,
      SourceClauseRowWriterOperands.rowIndex])
    (by simp [SourceClauseRowWriterOperands.gateCell,
      SourceClauseRowWriterOperands.scratch])]
  exact SourceClauseRowWriterBlank.gate_scratch_empty
    row n r saved output count x hcore

theorem gate_first_slot_initial {q : ℕ} (j : Fin q)
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r a k s t w : ℕ) (saved output count : List Bool)
    (i : Fin 6) :
    SourceClauseRowWriterStage.gateFinal n r a k s t w
      (SourceClauseRowWriterBlank.bank row n r saved output count)
      (SourceClauseRowWriterOperands.gateCell (.inl (.inl i))) =
    SourceClauseRowIndexedGate.initial j row n r a k s t w
      saved output count (.inl (.inl i)) := by
  fin_cases i
  · simpa [SourceClauseRowWriterStageReady.gateVariableLocal,
      SourceClauseRowWriterOperands.gateSlot,
      SourceClauseRowIndexedGate.initial, SourceClauseRowSlotAddress.initial,
      MatrixAddressMachine.cfg] using
      SourceClauseRowWriterStageReady.gate_variable_inputs
        row n r a k s t w saved output count 0
  · simpa [SourceClauseRowWriterStageReady.gateConstantLocal,
      SourceClauseRowWriterOperands.gateSlot,
      SourceClauseRowWriterOperands.gateSizes,
      SourceClauseRowIndexedGate.initial, SourceClauseRowSlotAddress.initial,
      MatrixAddressMachine.cfg] using
      SourceClauseRowWriterStageReady.gate_fixed_inputs
        row n r a k s t w saved output count 0
  all_goals
    rw [SourceClauseRowWriterStageReady.gate_final_other]
    · simp only [SourceClauseRowIndexedGate.initial,
        SourceClauseRowSlotAddress.initial, MatrixAddressMachine.cfg,
        SourceClauseRowWriterOperands.gateCell,
        SourceClauseRowWriterCore.gateEmbedding]
      apply SourceClauseRowWriterBlank.gate_scratch_empty
      rintro ⟨c, hc⟩
      cases c with
      | inl x =>
          simp [SourceClauseRowWriterCore.gateCore,
            SourceClauseRowWriterCore.gateCoreCell,
            SourceClauseRowGateCleanup.rowCell,
            SourceClauseRowIndexedGate.gateEmbedding,
            SourceClauseRowGate.addressEmbedding] at hc
      | inr z =>
          fin_cases z <;>
            simp [SourceClauseRowWriterCore.gateCore,
              SourceClauseRowWriterCore.gateCoreCell,
              SourceClauseRowGateCleanup.savedCell,
              SourceClauseRowGateCleanup.outputCell,
              SourceClauseRowGateCleanup.countCell,
              SourceClauseRowIndexedGate.gateEmbedding,
              SourceClauseRowGate.gateEmbedding] at hc
    /- The remaining subgoals discharge disjointness from the fixed targets. -/
    · intro z; fin_cases z <;>
        simp [SourceClauseRowWriterOperands.gateConstants,
          SourceClauseRowWriterOperands.gateCell,
          SourceClauseRowWriterOperands.gateSlot,
          SourceClauseRowWriterOperands.gateLiteral,
          SourceClauseRowWriterOperands.gateOffset,
          SourceClauseRowWriterOperands.gateAffine,
          SourceClauseRowWriterCore.gateEmbedding,
          SourceClauseRowIndexedGate.gateEmbedding]
    · simp [SourceClauseRowWriterOperands.gateVertexTargets,
        SourceClauseRowWriterOperands.gateCell,
        SourceClauseRowWriterOperands.gateSlot,
        SourceClauseRowWriterOperands.gateOffset,
        SourceClauseRowWriterCore.gateEmbedding,
        SourceClauseRowIndexedGate.gateEmbedding]
    · simp [SourceClauseRowWriterOperands.gateRowTargets,
        SourceClauseRowWriterOperands.gateCell,
        SourceClauseRowWriterOperands.gateSlot,
        SourceClauseRowWriterCore.gateEmbedding]
    · simp [SourceClauseRowWriterOperands.gateCell,
        SourceClauseRowWriterOperands.vertex]
    · simp [SourceClauseRowWriterOperands.gateCell,
        SourceClauseRowWriterOperands.rowIndex]
    · simp [SourceClauseRowWriterOperands.gateCell,
        SourceClauseRowWriterOperands.scratch]

theorem gate_second_slot_initial {q : ℕ} (j : Fin q)
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r a k s t w : ℕ) (saved output count : List Bool)
    (i : Fin 6) :
    SourceClauseRowWriterStage.gateFinal n r a k s t w
      (SourceClauseRowWriterBlank.bank row n r saved output count)
      (SourceClauseRowWriterOperands.gateCell (.inl (.inr (.inl i)))) =
    SourceClauseRowIndexedGate.initial j row n r a k s t w
      saved output count (.inl (.inr (.inl i))) := by
  fin_cases i
  · simpa [SourceClauseRowWriterStageReady.gateVariableLocal,
      SourceClauseRowWriterOperands.gateSlot,
      SourceClauseRowIndexedGate.initial, SourceClauseRowSlotAddress.initial,
      MatrixAddressMachine.cfg] using
      SourceClauseRowWriterStageReady.gate_variable_inputs
        row n r a k s t w saved output count 2
  · simpa [SourceClauseRowWriterStageReady.gateConstantLocal,
      SourceClauseRowWriterOperands.gateSlot,
      SourceClauseRowWriterOperands.gateSizes,
      SourceClauseRowIndexedGate.initial, SourceClauseRowSlotAddress.initial,
      MatrixAddressMachine.cfg] using
      SourceClauseRowWriterStageReady.gate_fixed_inputs
        row n r a k s t w saved output count 1
  · simpa [SourceClauseRowWriterStageReady.gateConstantLocal,
      SourceClauseRowWriterOperands.gateSlot,
      SourceClauseRowWriterOperands.gateSizes,
      SourceClauseRowIndexedGate.initial, SourceClauseRowSlotAddress.initial,
      MatrixAddressMachine.cfg] using
      SourceClauseRowWriterStageReady.gate_fixed_inputs
        row n r a k s t w saved output count 2
  all_goals
    simp only [SourceClauseRowIndexedGate.initial,
      SourceClauseRowSlotAddress.initial, MatrixAddressMachine.cfg]
    apply gate_other_empty
    · rintro ⟨c, hc⟩
      cases c with
      | inl x =>
          simp [SourceClauseRowWriterCore.gateCore,
            SourceClauseRowWriterCore.gateCoreCell,
            SourceClauseRowGateCleanup.rowCell,
            SourceClauseRowIndexedGate.gateEmbedding] at hc
      | inr z =>
          fin_cases z <;>
            simp [SourceClauseRowWriterCore.gateCore,
              SourceClauseRowWriterCore.gateCoreCell,
              SourceClauseRowGateCleanup.savedCell,
              SourceClauseRowGateCleanup.outputCell,
              SourceClauseRowGateCleanup.countCell,
              SourceClauseRowIndexedGate.gateEmbedding,
              SourceClauseRowGate.gateEmbedding] at hc
    · intro z; fin_cases z <;>
        simp [SourceClauseRowWriterOperands.gateConstants,
          SourceClauseRowWriterOperands.gateCell,
          SourceClauseRowWriterOperands.gateSlot,
          SourceClauseRowWriterOperands.gateLiteral,
          SourceClauseRowWriterOperands.gateOffset,
          SourceClauseRowWriterOperands.gateAffine,
          SourceClauseRowWriterCore.gateEmbedding,
          SourceClauseRowIndexedGate.gateEmbedding]
    · simp [SourceClauseRowWriterOperands.gateVertexTargets,
        SourceClauseRowWriterOperands.gateCell,
        SourceClauseRowWriterOperands.gateSlot,
        SourceClauseRowWriterOperands.gateOffset,
        SourceClauseRowWriterCore.gateEmbedding,
        SourceClauseRowIndexedGate.gateEmbedding]
    · simp [SourceClauseRowWriterOperands.gateRowTargets,
        SourceClauseRowWriterOperands.gateCell,
        SourceClauseRowWriterOperands.gateSlot,
        SourceClauseRowWriterCore.gateEmbedding]

theorem gate_slot_temp_initial {q : ℕ} (j : Fin q)
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r a k s t w : ℕ) (saved output count : List Bool) :
    SourceClauseRowWriterStage.gateFinal n r a k s t w
      (SourceClauseRowWriterBlank.bank row n r saved output count)
      (SourceClauseRowWriterOperands.gateCell (.inl (.inr (.inr 0)))) =
    SourceClauseRowIndexedGate.initial j row n r a k s t w
      saved output count (.inl (.inr (.inr 0))) := by
  simp only [SourceClauseRowIndexedGate.initial,
    SourceClauseRowSlotAddress.initial, MatrixAddressMachine.cfg]
  apply gate_other_empty
  · rintro ⟨c, hc⟩
    cases c with
    | inl x =>
        simp [SourceClauseRowWriterCore.gateCore,
          SourceClauseRowWriterCore.gateCoreCell,
          SourceClauseRowGateCleanup.rowCell,
          SourceClauseRowIndexedGate.gateEmbedding] at hc
    | inr z =>
        fin_cases z <;>
          simp [SourceClauseRowWriterCore.gateCore,
            SourceClauseRowWriterCore.gateCoreCell,
            SourceClauseRowGateCleanup.savedCell,
            SourceClauseRowGateCleanup.outputCell,
            SourceClauseRowGateCleanup.countCell,
            SourceClauseRowIndexedGate.gateEmbedding,
            SourceClauseRowGate.gateEmbedding] at hc
  · intro z; fin_cases z <;>
      simp [SourceClauseRowWriterOperands.gateConstants,
        SourceClauseRowWriterOperands.gateCell,
        SourceClauseRowWriterOperands.gateSlot,
        SourceClauseRowWriterOperands.gateLiteral,
        SourceClauseRowWriterOperands.gateOffset,
        SourceClauseRowWriterOperands.gateAffine,
        SourceClauseRowWriterCore.gateEmbedding,
        SourceClauseRowIndexedGate.gateEmbedding]
  · simp [SourceClauseRowWriterOperands.gateVertexTargets,
      SourceClauseRowWriterOperands.gateCell,
      SourceClauseRowWriterOperands.gateSlot,
      SourceClauseRowWriterOperands.gateOffset,
      SourceClauseRowWriterCore.gateEmbedding,
      SourceClauseRowIndexedGate.gateEmbedding]
  · simp [SourceClauseRowWriterOperands.gateRowTargets,
      SourceClauseRowWriterOperands.gateCell,
      SourceClauseRowWriterOperands.gateSlot,
      SourceClauseRowWriterCore.gateEmbedding]

theorem gate_slot_initial {q : ℕ} (j : Fin q)
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r a k s t w : ℕ) (saved output count : List Bool)
    (x : SourceClauseRowSlotAddress.Stack) :
    SourceClauseRowWriterStage.gateFinal n r a k s t w
      (SourceClauseRowWriterBlank.bank row n r saved output count)
      (SourceClauseRowWriterOperands.gateCell (.inl x)) =
    SourceClauseRowIndexedGate.initial j row n r a k s t w
      saved output count (.inl x) := by
  cases x with
  | inl i =>
      exact gate_first_slot_initial j row n r a k s t w
        saved output count i
  | inr y =>
      cases y with
      | inl i =>
          exact gate_second_slot_initial j row n r a k s t w
            saved output count i
      | inr i =>
          fin_cases i
          exact gate_slot_temp_initial j row n r a k s t w saved output count

theorem gate_core_initial {q : ℕ} (j : Fin q)
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r a k s t w : ℕ) (saved output count : List Bool)
    (c : SourceClauseRowWriterCore.Core q) :
    SourceClauseRowWriterStage.gateFinal n r a k s t w
      (SourceClauseRowWriterBlank.bank row n r saved output count)
      (SourceClauseRowWriterOperands.gateCell
        (SourceClauseRowWriterCore.gateCore c)) =
    SourceClauseRowIndexedGate.initial j row n r a k s t w
      saved output count (SourceClauseRowWriterCore.gateCore c) := by
  rw [SourceClauseRowWriterOperands.gateCell,
    SourceClauseRowWriterCore.gate_cell,
    SourceClauseRowWriterStageReady.gate_core_preserved]
  cases c with
  | inl x =>
      simp [SourceClauseRowWriterBlank.core,
        SourceClauseRowWriterCore.gateCore,
        SourceClauseRowWriterCore.gateCoreCell,
        SourceClauseRowGateCleanup.rowCell,
        SourceClauseRowIndexedGate.initial,
        SourceClauseRowIndexedGate.gateEmbedding,
        SourceClauseRowGate.initial,
        SourceClauseRowLiteralAddress.initial]
  | inr i =>
      fin_cases i <;>
        simp [SourceClauseRowWriterBlank.core,
          SourceClauseRowWriterCore.gateCore,
          SourceClauseRowWriterCore.gateCoreCell,
          SourceClauseRowGateCleanup.savedCell,
          SourceClauseRowGateCleanup.outputCell,
          SourceClauseRowGateCleanup.countCell,
          SourceClauseRowIndexedGate.initial,
          SourceClauseRowIndexedGate.gateEmbedding,
          SourceClauseRowGate.initial,
          SourceClauseRowGate.gateEmbedding,
          SourceClauseGateSlotAddress.initial,
          SourceClauseGateSlotAddress.gateEmbedding,
          SourceClauseGateAffineAddress.initial,
          SourceClauseGateAffineAddress.gateEmbedding,
          SourceClauseGateTwoAddress.embedding,
          SourceClauseGateMachine.embedding,
          SourceClauseGateSuccessor.initial,
          SourceClauseGateBroadcast.initial,
          SourceClauseGateSchedule.contents]

theorem unit_core_initial {q : ℕ}
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r a k w ell : ℕ) (saved output count : List Bool)
    (c : SourceClauseRowWriterCore.Core q) :
    SourceClauseRowWriterStage.unitFinal n r a k w ell
      (SourceClauseRowWriterBlank.bank row n r saved output count)
      (SourceClauseRowWriterOperands.unitCell
        (SourceClauseRowWriterCore.unitCore c)) =
    SourceClauseRowUnitFrame.initial row n r a k w ell
      saved output count (SourceClauseRowWriterCore.unitCore c) := by
  rw [SourceClauseRowWriterOperands.unitCell,
    SourceClauseRowWriterCore.unit_cell,
    SourceClauseRowWriterStageReady.unit_core_preserved]
  cases c with
  | inl x =>
      rfl
  | inr i =>
      fin_cases i <;>
        simp [SourceClauseRowWriterBlank.core,
          SourceClauseRowWriterCore.unitCore,
          SourceClauseRowWriterCore.unitCoreCell,
          SourceClauseRowUnitFrame.initial,
          SourceClauseRowUnitMachine.initial,
          SourceClauseUnitMachine.initial,
          SourceClauseCountedStream.contents,
          SourceLiteralWriter.cfg,
          SourceLiteralWriter.contents,
          SourceClauseRowUnitMachine.savedSlot,
          SourceClauseRowUnitMachine.outputSlot,
          SourceClauseRowUnitMachine.countSlot]

end EthInapproximability.CurrentPaper.SourceClauseRowWriterInitial
