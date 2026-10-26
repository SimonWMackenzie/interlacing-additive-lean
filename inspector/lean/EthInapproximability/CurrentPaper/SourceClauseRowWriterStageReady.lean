import EthInapproximability.CurrentPaper.SourceClauseRowWriterStage

/-!
# Physical operand staging readback at the exact arithmetic cells

The fixed-word phase and preserving n/r fanout must populate only scratch,
leaving the validated row and writer accumulator untouched. Full equality to
each local clause machine's initial bank is a subsequent finite-bank audit.
-/

namespace EthInapproximability.CurrentPaper.SourceClauseRowWriterStageReady

open scoped Classical

def gateConstantLocal {q : ℕ} : Fin 8 → SourceClauseRowWriterCore.Gate q :=
  ![SourceClauseRowWriterOperands.gateSlot (.inl 1),
    SourceClauseRowWriterOperands.gateSlot (.inr (.inl 1)),
    SourceClauseRowWriterOperands.gateSlot (.inr (.inl 2)),
    SourceClauseRowWriterOperands.gateLiteral (.inl 1),
    SourceClauseRowWriterOperands.gateLiteral (.inl 2),
    SourceClauseRowWriterOperands.gateOffset 1,
    SourceClauseRowWriterOperands.gateOffset 2,
    SourceClauseRowWriterOperands.gateAffine (.inl 1)]

def unitConstantLocal {q : ℕ} : Fin 6 → SourceClauseRowWriterCore.UnitBank q :=
  ![SourceClauseRowWriterOperands.unitAddress
      (SourceClauseRowUnitAddress.slotEmbedding (.inl 1)),
    SourceClauseRowWriterOperands.unitAddress
      (SourceClauseRowUnitAddress.slotEmbedding (.inr (.inl 1))),
    SourceClauseRowWriterOperands.unitAddress
      (SourceClauseRowUnitAddress.slotEmbedding (.inr (.inl 2))),
    SourceClauseRowWriterOperands.unitAddress
      (SourceClauseRowUnitAddress.offsetEmbedding 1),
    SourceClauseRowWriterOperands.unitAddress
      (SourceClauseRowUnitAddress.offsetEmbedding 2),
    SourceClauseRowWriterOperands.unitAddress
      (SourceClauseRowUnitAddress.labelEmbedding (.inl 1))]

theorem gate_constant_cell {q : ℕ} (i : Fin 8) :
    (SourceClauseRowWriterOperands.gateConstants (q := q)) i =
      SourceClauseRowWriterOperands.gateCell (gateConstantLocal (q := q) i) := by
  fin_cases i <;> simp [SourceClauseRowWriterOperands.gateConstants,
    gateConstantLocal]

theorem unit_constant_cell {q : ℕ} (i : Fin 6) :
    (SourceClauseRowWriterOperands.unitConstants (q := q)) i =
      SourceClauseRowWriterOperands.unitCell (unitConstantLocal (q := q) i) := by
  fin_cases i <;> simp [SourceClauseRowWriterOperands.unitConstants,
    unitConstantLocal]

theorem gate_constant_scratch {q : ℕ} (i : Fin 8) :
    gateConstantLocal (q := q) i ∉
      Set.range (SourceClauseRowWriterCore.gateCore (q := q)) := by
  intro ⟨c, hc⟩
  fin_cases i <;> cases c with
  | inl x =>
      simp [gateConstantLocal, SourceClauseRowWriterCore.gateCore,
        SourceClauseRowWriterCore.gateCoreCell,
        SourceClauseRowWriterOperands.gateSlot,
        SourceClauseRowWriterOperands.gateLiteral,
        SourceClauseRowWriterOperands.gateOffset,
        SourceClauseRowWriterOperands.gateAffine,
        SourceClauseRowGateCleanup.rowCell,
        SourceClauseRowGateCleanup.savedCell,
        SourceClauseRowGateCleanup.outputCell,
        SourceClauseRowGateCleanup.countCell,
        SourceClauseRowIndexedGate.gateEmbedding,
        SourceClauseRowGate.addressEmbedding,
        SourceClauseRowGate.gateEmbedding,
        SourceClauseGateSlotAddress.offsetEmbedding,
        SourceClauseGateSlotAddress.gateEmbedding,
        SourceClauseGateAffineAddress.addressEmbedding] at hc
  | inr j =>
      fin_cases j <;>
        simp [gateConstantLocal, SourceClauseRowWriterCore.gateCore,
          SourceClauseRowWriterCore.gateCoreCell,
          SourceClauseRowWriterOperands.gateSlot,
          SourceClauseRowWriterOperands.gateLiteral,
          SourceClauseRowWriterOperands.gateOffset,
          SourceClauseRowWriterOperands.gateAffine,
          SourceClauseRowGateCleanup.savedCell,
          SourceClauseRowGateCleanup.outputCell,
          SourceClauseRowGateCleanup.countCell,
          SourceClauseRowIndexedGate.gateEmbedding,
          SourceClauseRowGate.addressEmbedding,
          SourceClauseRowGate.gateEmbedding,
          SourceClauseGateSlotAddress.offsetEmbedding,
          SourceClauseGateSlotAddress.gateEmbedding,
          SourceClauseGateAffineAddress.addressEmbedding,
          SourceClauseGateAffineAddress.gateEmbedding,
          SourceClauseGateTwoAddress.embedding,
          SourceClauseGateMachine.embedding] at hc

theorem unit_constant_scratch {q : ℕ} (i : Fin 6) :
    unitConstantLocal (q := q) i ∉
      Set.range (SourceClauseRowWriterCore.unitCore (q := q)) := by
  intro ⟨c, hc⟩
  fin_cases i <;> cases c with
  | inl x =>
      simp [unitConstantLocal, SourceClauseRowWriterCore.unitCore,
        SourceClauseRowWriterCore.unitCoreCell,
        SourceClauseRowWriterOperands.unitAddress,
        SourceClauseRowUnitMachine.addressEmbedding,
        SourceClauseRowUnitAddress.slotEmbedding,
        SourceClauseRowUnitAddress.offsetEmbedding,
        SourceClauseRowUnitAddress.labelEmbedding] at hc
  | inr j =>
      fin_cases j <;>
        simp [unitConstantLocal, SourceClauseRowWriterCore.unitCore,
          SourceClauseRowWriterCore.unitCoreCell,
          SourceClauseRowWriterOperands.unitAddress,
          SourceClauseRowUnitMachine.addressEmbedding,
          SourceClauseRowUnitAddress.slotEmbedding,
          SourceClauseRowUnitAddress.offsetEmbedding,
          SourceClauseRowUnitAddress.labelEmbedding,
          SourceClauseRowUnitMachine.savedSlot,
          SourceClauseRowUnitMachine.outputSlot,
          SourceClauseRowUnitMachine.countSlot] at hc

theorem gate_constant_blank {q : ℕ}
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r : ℕ) (saved output count : List Bool) (i : Fin 8) :
    SourceClauseRowWriterBlank.bank row n r saved output count
      (SourceClauseRowWriterOperands.gateConstants i) = [] := by
  rw [gate_constant_cell]
  exact SourceClauseRowWriterBlank.gate_scratch_empty
    row n r saved output count _ (gate_constant_scratch i)

theorem unit_constant_blank {q : ℕ}
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r : ℕ) (saved output count : List Bool) (i : Fin 6) :
    SourceClauseRowWriterBlank.bank row n r saved output count
      (SourceClauseRowWriterOperands.unitConstants i) = [] := by
  rw [unit_constant_cell]
  exact SourceClauseRowWriterBlank.unit_scratch_empty
    row n r saved output count _ (unit_constant_scratch i)

def gateVariableLocal {q : ℕ} : Fin 3 → SourceClauseRowWriterCore.Gate q :=
  ![SourceClauseRowWriterOperands.gateSlot (.inl 0),
    SourceClauseRowWriterOperands.gateOffset 0,
    SourceClauseRowWriterOperands.gateSlot (.inr (.inl 0))]

def unitVariableLocal {q : ℕ} : Fin 3 → SourceClauseRowWriterCore.UnitBank q :=
  ![SourceClauseRowWriterOperands.unitAddress
      (SourceClauseRowUnitAddress.slotEmbedding (.inl 0)),
    SourceClauseRowWriterOperands.unitAddress
      (SourceClauseRowUnitAddress.offsetEmbedding 0),
    SourceClauseRowWriterOperands.unitAddress
      (SourceClauseRowUnitAddress.slotEmbedding (.inr (.inl 0)))]

theorem gate_variable_scratch {q : ℕ} (i : Fin 3) :
    gateVariableLocal (q := q) i ∉
      Set.range (SourceClauseRowWriterCore.gateCore (q := q)) := by
  intro ⟨c, hc⟩
  fin_cases i <;> cases c with
  | inl x =>
      simp [gateVariableLocal, SourceClauseRowWriterCore.gateCore,
        SourceClauseRowWriterCore.gateCoreCell,
        SourceClauseRowWriterOperands.gateSlot,
        SourceClauseRowWriterOperands.gateOffset,
        SourceClauseRowGateCleanup.rowCell,
        SourceClauseRowIndexedGate.gateEmbedding,
        SourceClauseRowGate.gateEmbedding,
        SourceClauseGateSlotAddress.offsetEmbedding] at hc
  | inr j =>
      fin_cases j <;>
        simp [gateVariableLocal, SourceClauseRowWriterCore.gateCore,
          SourceClauseRowWriterCore.gateCoreCell,
          SourceClauseRowWriterOperands.gateSlot,
          SourceClauseRowWriterOperands.gateOffset,
          SourceClauseRowGateCleanup.savedCell,
          SourceClauseRowGateCleanup.outputCell,
          SourceClauseRowGateCleanup.countCell,
          SourceClauseRowIndexedGate.gateEmbedding,
          SourceClauseRowGate.gateEmbedding,
          SourceClauseGateSlotAddress.offsetEmbedding,
          SourceClauseGateSlotAddress.gateEmbedding,
          SourceClauseGateAffineAddress.gateEmbedding,
          SourceClauseGateTwoAddress.embedding,
          SourceClauseGateMachine.embedding] at hc

theorem unit_variable_scratch {q : ℕ} (i : Fin 3) :
    unitVariableLocal (q := q) i ∉
      Set.range (SourceClauseRowWriterCore.unitCore (q := q)) := by
  intro ⟨c, hc⟩
  fin_cases i <;> cases c with
  | inl x =>
      simp [unitVariableLocal, SourceClauseRowWriterCore.unitCore,
        SourceClauseRowWriterCore.unitCoreCell,
        SourceClauseRowWriterOperands.unitAddress,
        SourceClauseRowUnitMachine.addressEmbedding,
        SourceClauseRowUnitAddress.slotEmbedding,
        SourceClauseRowUnitAddress.offsetEmbedding] at hc
  | inr j =>
      fin_cases j <;>
        simp [unitVariableLocal, SourceClauseRowWriterCore.unitCore,
          SourceClauseRowWriterCore.unitCoreCell,
          SourceClauseRowWriterOperands.unitAddress,
          SourceClauseRowUnitMachine.addressEmbedding,
          SourceClauseRowUnitAddress.slotEmbedding,
          SourceClauseRowUnitAddress.offsetEmbedding,
          SourceClauseRowUnitMachine.savedSlot,
          SourceClauseRowUnitMachine.outputSlot,
          SourceClauseRowUnitMachine.countSlot] at hc

theorem gate_variable_blank {q : ℕ}
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r : ℕ) (saved output count : List Bool) (i : Fin 3) :
    SourceClauseRowWriterBlank.bank row n r saved output count
      (SourceClauseRowWriterOperands.gateCell (gateVariableLocal i)) = [] :=
  SourceClauseRowWriterBlank.gate_scratch_empty row n r saved output count
    _ (gate_variable_scratch i)

theorem unit_variable_blank {q : ℕ}
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r : ℕ) (saved output count : List Bool) (i : Fin 3) :
    SourceClauseRowWriterBlank.bank row n r saved output count
      (SourceClauseRowWriterOperands.unitCell (unitVariableLocal i)) = [] :=
  SourceClauseRowWriterBlank.unit_scratch_empty row n r saved output count
    _ (unit_variable_scratch i)

theorem gate_variable_not_constant {q : ℕ}
    (i : Fin 3) (j : Fin 8) :
    SourceClauseRowWriterOperands.gateCell
      (gateVariableLocal (q := q) i) ≠
      SourceClauseRowWriterOperands.gateConstants j := by
  rw [gate_constant_cell]
  intro h
  have hh := (SourceClauseRowWriterCore.gateEmbedding (q := q)).injective
    (Sum.inl.inj h)
  fin_cases i <;> fin_cases j <;>
    simp [gateVariableLocal, gateConstantLocal,
      SourceClauseRowWriterOperands.gateSlot,
      SourceClauseRowWriterOperands.gateLiteral,
      SourceClauseRowWriterOperands.gateOffset,
      SourceClauseRowWriterOperands.gateAffine,
      SourceClauseRowIndexedGate.gateEmbedding,
      SourceClauseRowGate.addressEmbedding,
      SourceClauseRowGate.gateEmbedding,
      SourceClauseGateSlotAddress.offsetEmbedding,
      SourceClauseGateSlotAddress.gateEmbedding,
      SourceClauseGateAffineAddress.addressEmbedding] at hh

theorem unit_variable_not_constant {q : ℕ}
    (i : Fin 3) (j : Fin 6) :
    SourceClauseRowWriterOperands.unitCell
      (unitVariableLocal (q := q) i) ≠
      SourceClauseRowWriterOperands.unitConstants j := by
  rw [unit_constant_cell]
  intro h
  have hh := (SourceClauseRowWriterCore.unitEmbedding (q := q)).injective
    (Sum.inl.inj h)
  fin_cases i <;> fin_cases j <;>
    simp [unitVariableLocal, unitConstantLocal,
      SourceClauseRowWriterOperands.unitAddress,
      SourceClauseRowUnitMachine.addressEmbedding,
      SourceClauseRowUnitAddress.slotEmbedding,
      SourceClauseRowUnitAddress.offsetEmbedding,
      SourceClauseRowUnitAddress.labelEmbedding] at hh

theorem gate_vertex_targets {q : ℕ} :
    SourceClauseRowWriterOperands.gateVertexTargets (q := q) =
      [SourceClauseRowWriterOperands.gateCell (gateVariableLocal 0),
        SourceClauseRowWriterOperands.gateCell (gateVariableLocal 1)] := rfl

theorem gate_row_targets {q : ℕ} :
    SourceClauseRowWriterOperands.gateRowTargets (q := q) =
      [SourceClauseRowWriterOperands.gateCell (gateVariableLocal 2)] := rfl

theorem unit_vertex_targets {q : ℕ} :
    SourceClauseRowWriterOperands.unitVertexTargets (q := q) =
      [SourceClauseRowWriterOperands.unitCell (unitVariableLocal 0),
        SourceClauseRowWriterOperands.unitCell (unitVariableLocal 1)] := rfl

theorem unit_row_targets {q : ℕ} :
    SourceClauseRowWriterOperands.unitRowTargets (q := q) =
      [SourceClauseRowWriterOperands.unitCell (unitVariableLocal 2)] := rfl

theorem gate_constant_outside_fanout {q : ℕ} (j : Fin 8) :
    SourceClauseRowWriterOperands.gateConstants (q := q) j ∉
      SourceClauseRowWriterOperands.gateVertexTargets ∧
    SourceClauseRowWriterOperands.gateConstants (q := q) j ∉
      SourceClauseRowWriterOperands.gateRowTargets := by
  rw [gate_vertex_targets, gate_row_targets]
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
  exact ⟨⟨(gate_variable_not_constant 0 j).symm,
    (gate_variable_not_constant 1 j).symm⟩,
    (gate_variable_not_constant 2 j).symm⟩

theorem unit_constant_outside_fanout {q : ℕ} (j : Fin 6) :
    SourceClauseRowWriterOperands.unitConstants (q := q) j ∉
      SourceClauseRowWriterOperands.unitVertexTargets ∧
    SourceClauseRowWriterOperands.unitConstants (q := q) j ∉
      SourceClauseRowWriterOperands.unitRowTargets := by
  rw [unit_vertex_targets, unit_row_targets]
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
  exact ⟨⟨(unit_variable_not_constant 0 j).symm,
    (unit_variable_not_constant 1 j).symm⟩,
    (unit_variable_not_constant 2 j).symm⟩

theorem gate_constant_after_fanout {q : ℕ}
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r a k s t w : ℕ) (saved output count : List Bool)
    (j : Fin 8) :
    SourceClauseRowWriterFanout.afterRow
      SourceClauseRowWriterOperands.gateVertexTargets
      SourceClauseRowWriterOperands.gateRowTargets n r
      (SourceClauseRowWriterBlank.bank row n r saved output count)
      (SourceClauseRowWriterOperands.gateConstants j) = [] := by
  obtain ⟨hn, hr⟩ := gate_constant_outside_fanout j
  rw [SourceClauseRowWriterFanout.afterRow,
    SourceClausePreservingBroadcast.other_preserved
      SourceClauseRowWriterOperands.rowIndex
      SourceClauseRowWriterOperands.scratch
      SourceClauseRowWriterOperands.gateRowTargets
      (List.replicate r true) _ _
      (by simp [gate_constant_cell,
        SourceClauseRowWriterOperands.gateCell,
        SourceClauseRowWriterOperands.rowIndex])
      (by simp [gate_constant_cell,
        SourceClauseRowWriterOperands.gateCell,
        SourceClauseRowWriterOperands.scratch]) hr,
    SourceClauseRowWriterFanout.afterVertex,
    SourceClausePreservingBroadcast.other_preserved
      SourceClauseRowWriterOperands.vertex
      SourceClauseRowWriterOperands.scratch
      SourceClauseRowWriterOperands.gateVertexTargets
      (List.replicate n true) _ _
      (by simp [gate_constant_cell,
        SourceClauseRowWriterOperands.gateCell,
        SourceClauseRowWriterOperands.vertex])
      (by simp [gate_constant_cell,
        SourceClauseRowWriterOperands.gateCell,
        SourceClauseRowWriterOperands.scratch]) hn]
  exact gate_constant_blank row n r saved output count j

theorem unit_constant_after_fanout {q : ℕ}
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r a k w ell : ℕ) (saved output count : List Bool)
    (j : Fin 6) :
    SourceClauseRowWriterFanout.afterRow
      SourceClauseRowWriterOperands.unitVertexTargets
      SourceClauseRowWriterOperands.unitRowTargets n r
      (SourceClauseRowWriterBlank.bank row n r saved output count)
      (SourceClauseRowWriterOperands.unitConstants j) = [] := by
  obtain ⟨hn, hr⟩ := unit_constant_outside_fanout j
  rw [SourceClauseRowWriterFanout.afterRow,
    SourceClausePreservingBroadcast.other_preserved
      SourceClauseRowWriterOperands.rowIndex
      SourceClauseRowWriterOperands.scratch
      SourceClauseRowWriterOperands.unitRowTargets
      (List.replicate r true) _ _
      (by simp [unit_constant_cell,
        SourceClauseRowWriterOperands.unitCell,
        SourceClauseRowWriterOperands.rowIndex])
      (by simp [unit_constant_cell,
        SourceClauseRowWriterOperands.unitCell,
        SourceClauseRowWriterOperands.scratch]) hr,
    SourceClauseRowWriterFanout.afterVertex,
    SourceClausePreservingBroadcast.other_preserved
      SourceClauseRowWriterOperands.vertex
      SourceClauseRowWriterOperands.scratch
      SourceClauseRowWriterOperands.unitVertexTargets
      (List.replicate n true) _ _
      (by simp [unit_constant_cell,
        SourceClauseRowWriterOperands.unitCell,
        SourceClauseRowWriterOperands.vertex])
      (by simp [unit_constant_cell,
        SourceClauseRowWriterOperands.unitCell,
        SourceClauseRowWriterOperands.scratch]) hn]
  exact unit_constant_blank row n r saved output count j

theorem gate_fixed_inputs {q : ℕ}
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r a k s t w : ℕ) (saved output count : List Bool)
    (j : Fin 8) :
    SourceClauseRowWriterStage.gateFinal n r a k s t w
      (SourceClauseRowWriterBlank.bank row n r saved output count)
      (SourceClauseRowWriterOperands.gateConstants j) =
      List.replicate (SourceClauseRowWriterOperands.gateSizes a q k s t w j)
        true := by
  rw [SourceClauseRowWriterStage.gateFinal,
    SourceClauseRowWriterOperands.gate_fixed_word]
  simp [gate_constant_after_fanout row n r a k s t w saved output count j]

theorem unit_fixed_inputs {q : ℕ}
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r a k w ell : ℕ) (saved output count : List Bool)
    (j : Fin 6) :
    SourceClauseRowWriterStage.unitFinal n r a k w ell
      (SourceClauseRowWriterBlank.bank row n r saved output count)
      (SourceClauseRowWriterOperands.unitConstants j) =
      List.replicate (SourceClauseRowWriterOperands.unitSizes a q k w ell j)
        true := by
  rw [SourceClauseRowWriterStage.unitFinal,
    SourceClauseRowWriterOperands.unit_fixed_word]
  simp [unit_constant_after_fanout row n r a k w ell saved output count j]

theorem gate_variable_after_fanout {q : ℕ}
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r : ℕ) (saved output count : List Bool) (i : Fin 3) :
    SourceClauseRowWriterFanout.afterRow
      SourceClauseRowWriterOperands.gateVertexTargets
      SourceClauseRowWriterOperands.gateRowTargets n r
      (SourceClauseRowWriterBlank.bank row n r saved output count)
      (SourceClauseRowWriterOperands.gateCell (gateVariableLocal i)) =
      List.replicate (if i = 2 then r else n) true := by
  fin_cases i
  · have h := SourceClauseRowWriterFanout.vertex_target_written
      SourceClauseRowWriterOperands.gateVertexTargets
      SourceClauseRowWriterOperands.gateRowTargets
      (SourceClauseRowWriterFanout.gate_wellformed (q := q)).2.2.1
      (SourceClauseRowWriterFanout.gate_wellformed (q := q)).2.2.2.1
      n r (SourceClauseRowWriterBlank.bank row n r saved output count)
      (SourceClauseRowWriterOperands.gateCell (gateVariableLocal 0))
      (by simp [gate_vertex_targets])
      (by simp [gate_row_targets, gateVariableLocal,
        SourceClauseRowWriterOperands.gateCell,
        SourceClauseRowWriterOperands.gateSlot,
        SourceClauseRowWriterCore.gateEmbedding])
      (by simp [SourceClauseRowWriterOperands.gateCell,
        SourceClauseRowWriterOperands.rowIndex])
      (by simp [SourceClauseRowWriterOperands.gateCell,
        SourceClauseRowWriterOperands.scratch])
    simpa [gate_variable_blank row n r saved output count 0] using h
  · have h := SourceClauseRowWriterFanout.vertex_target_written
      SourceClauseRowWriterOperands.gateVertexTargets
      SourceClauseRowWriterOperands.gateRowTargets
      (SourceClauseRowWriterFanout.gate_wellformed (q := q)).2.2.1
      (SourceClauseRowWriterFanout.gate_wellformed (q := q)).2.2.2.1
      n r (SourceClauseRowWriterBlank.bank row n r saved output count)
      (SourceClauseRowWriterOperands.gateCell (gateVariableLocal 1))
      (by simp [gate_vertex_targets])
      (by simp [gate_row_targets, gateVariableLocal,
        SourceClauseRowWriterOperands.gateCell,
        SourceClauseRowWriterOperands.gateOffset,
        SourceClauseRowWriterOperands.gateSlot,
        SourceClauseRowIndexedGate.gateEmbedding,
        SourceClauseRowGate.gateEmbedding,
        SourceClauseGateSlotAddress.offsetEmbedding])
      (by simp [SourceClauseRowWriterOperands.gateCell,
        SourceClauseRowWriterOperands.rowIndex])
      (by simp [SourceClauseRowWriterOperands.gateCell,
        SourceClauseRowWriterOperands.scratch])
    simpa [gate_variable_blank row n r saved output count 1] using h
  · have h := SourceClauseRowWriterFanout.row_target_written
      SourceClauseRowWriterOperands.gateVertexTargets
      SourceClauseRowWriterOperands.gateRowTargets
      (SourceClauseRowWriterFanout.gate_wellformed (q := q)).2.2.2.2.2.2.1
      (SourceClauseRowWriterFanout.gate_wellformed (q := q)).2.2.2.2.2.2.2
      n r (SourceClauseRowWriterBlank.bank row n r saved output count)
      (SourceClauseRowWriterOperands.gateCell (gateVariableLocal 2))
      (by simp [gate_row_targets])
      (by simp [gate_vertex_targets, gateVariableLocal,
        SourceClauseRowWriterOperands.gateCell,
        SourceClauseRowWriterOperands.gateSlot,
        SourceClauseRowWriterOperands.gateOffset,
        SourceClauseRowIndexedGate.gateEmbedding,
        SourceClauseRowGate.gateEmbedding,
        SourceClauseGateSlotAddress.offsetEmbedding])
      (by simp [SourceClauseRowWriterOperands.gateCell,
        SourceClauseRowWriterOperands.vertex])
      (by simp [SourceClauseRowWriterOperands.gateCell,
        SourceClauseRowWriterOperands.scratch])
    simpa [gate_variable_blank row n r saved output count 2] using h

theorem unit_variable_after_fanout {q : ℕ}
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r : ℕ) (saved output count : List Bool) (i : Fin 3) :
    SourceClauseRowWriterFanout.afterRow
      SourceClauseRowWriterOperands.unitVertexTargets
      SourceClauseRowWriterOperands.unitRowTargets n r
      (SourceClauseRowWriterBlank.bank row n r saved output count)
      (SourceClauseRowWriterOperands.unitCell (unitVariableLocal i)) =
      List.replicate (if i = 2 then r else n) true := by
  have hw := SourceClauseRowWriterFanout.unit_wellformed (q := q)
  obtain ⟨_, _, hnv, hns, _, _, hrr, hrs⟩ := hw
  fin_cases i
  · have h := SourceClauseRowWriterFanout.vertex_target_written
      SourceClauseRowWriterOperands.unitVertexTargets
      SourceClauseRowWriterOperands.unitRowTargets hnv hns
      n r (SourceClauseRowWriterBlank.bank row n r saved output count)
      (SourceClauseRowWriterOperands.unitCell (unitVariableLocal 0))
      (by simp [unit_vertex_targets])
      (by simp [unit_row_targets, unitVariableLocal,
        SourceClauseRowWriterOperands.unitCell,
        SourceClauseRowWriterOperands.unitAddress,
        SourceClauseRowUnitAddress.slotEmbedding,
        SourceClauseRowUnitAddress.offsetEmbedding])
      (by simp [SourceClauseRowWriterOperands.unitCell,
        SourceClauseRowWriterOperands.rowIndex])
      (by simp [SourceClauseRowWriterOperands.unitCell,
        SourceClauseRowWriterOperands.scratch])
    simpa [unit_variable_blank row n r saved output count 0] using h
  · have h := SourceClauseRowWriterFanout.vertex_target_written
      SourceClauseRowWriterOperands.unitVertexTargets
      SourceClauseRowWriterOperands.unitRowTargets hnv hns
      n r (SourceClauseRowWriterBlank.bank row n r saved output count)
      (SourceClauseRowWriterOperands.unitCell (unitVariableLocal 1))
      (by simp [unit_vertex_targets])
      (by simp [unit_row_targets, unitVariableLocal,
        SourceClauseRowWriterOperands.unitCell,
        SourceClauseRowWriterOperands.unitAddress,
        SourceClauseRowUnitAddress.slotEmbedding,
        SourceClauseRowUnitAddress.offsetEmbedding])
      (by simp [SourceClauseRowWriterOperands.unitCell,
        SourceClauseRowWriterOperands.rowIndex])
      (by simp [SourceClauseRowWriterOperands.unitCell,
        SourceClauseRowWriterOperands.scratch])
    simpa [unit_variable_blank row n r saved output count 1] using h
  · have h := SourceClauseRowWriterFanout.row_target_written
      SourceClauseRowWriterOperands.unitVertexTargets
      SourceClauseRowWriterOperands.unitRowTargets hrr hrs
      n r (SourceClauseRowWriterBlank.bank row n r saved output count)
      (SourceClauseRowWriterOperands.unitCell (unitVariableLocal 2))
      (by simp [unit_row_targets])
      (by simp [unit_vertex_targets, unitVariableLocal,
        SourceClauseRowWriterOperands.unitCell,
        SourceClauseRowWriterOperands.unitAddress,
        SourceClauseRowUnitAddress.slotEmbedding,
        SourceClauseRowUnitAddress.offsetEmbedding])
      (by simp [SourceClauseRowWriterOperands.unitCell,
        SourceClauseRowWriterOperands.vertex])
      (by simp [SourceClauseRowWriterOperands.unitCell,
        SourceClauseRowWriterOperands.scratch])
    simpa [unit_variable_blank row n r saved output count 2] using h

theorem gate_variable_inputs {q : ℕ}
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r a k s t w : ℕ) (saved output count : List Bool)
    (i : Fin 3) :
    SourceClauseRowWriterStage.gateFinal n r a k s t w
      (SourceClauseRowWriterBlank.bank row n r saved output count)
      (SourceClauseRowWriterOperands.gateCell (gateVariableLocal i)) =
      List.replicate (if i = 2 then r else n) true := by
  rw [SourceClauseRowWriterStage.gateFinal,
    SourceClauseRowWriterOperands.gateFixedBank,
    SourceClauseFixedBatch.result_outside
      SourceClauseRowWriterOperands.gateConstants
      (SourceClauseRowWriterOperands.gateSizes a q k s t w)
      (SourceClauseRowWriterFanout.afterRow
        SourceClauseRowWriterOperands.gateVertexTargets
        SourceClauseRowWriterOperands.gateRowTargets n r
        (SourceClauseRowWriterBlank.bank row n r saved output count))
      (SourceClauseRowWriterOperands.gateCell (gateVariableLocal i))
      (fun j => (gate_variable_not_constant i j).symm)]
  exact gate_variable_after_fanout row n r saved output count i

theorem unit_variable_inputs {q : ℕ}
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r a k w ell : ℕ) (saved output count : List Bool)
    (i : Fin 3) :
    SourceClauseRowWriterStage.unitFinal n r a k w ell
      (SourceClauseRowWriterBlank.bank row n r saved output count)
      (SourceClauseRowWriterOperands.unitCell (unitVariableLocal i)) =
      List.replicate (if i = 2 then r else n) true := by
  rw [SourceClauseRowWriterStage.unitFinal,
    SourceClauseRowWriterOperands.unitFixedBank,
    SourceClauseFixedBatch.result_outside
      SourceClauseRowWriterOperands.unitConstants
      (SourceClauseRowWriterOperands.unitSizes a q k w ell)
      (SourceClauseRowWriterFanout.afterRow
        SourceClauseRowWriterOperands.unitVertexTargets
        SourceClauseRowWriterOperands.unitRowTargets n r
        (SourceClauseRowWriterBlank.bank row n r saved output count))
      (SourceClauseRowWriterOperands.unitCell (unitVariableLocal i))
      (fun j => (unit_variable_not_constant i j).symm)]
  exact unit_variable_after_fanout row n r saved output count i

theorem gate_final_other {q : ℕ} (n r a k s t w : ℕ)
    (S : SourceClauseRowWriterOperands.Stack q → List Bool)
    (x : SourceClauseRowWriterOperands.Stack q)
    (hc : ∀ j : Fin 8, SourceClauseRowWriterOperands.gateConstants j ≠ x)
    (hn : x ∉ SourceClauseRowWriterOperands.gateVertexTargets)
    (hr : x ∉ SourceClauseRowWriterOperands.gateRowTargets)
    (hv : x ≠ SourceClauseRowWriterOperands.vertex)
    (hrow : x ≠ SourceClauseRowWriterOperands.rowIndex)
    (hs : x ≠ SourceClauseRowWriterOperands.scratch) :
    SourceClauseRowWriterStage.gateFinal n r a k s t w S x = S x := by
  rw [SourceClauseRowWriterStage.gateFinal,
    SourceClauseRowWriterOperands.gateFixedBank,
    SourceClauseFixedBatch.result_outside
      SourceClauseRowWriterOperands.gateConstants
      (SourceClauseRowWriterOperands.gateSizes a q k s t w)
      (SourceClauseRowWriterFanout.afterRow
        SourceClauseRowWriterOperands.gateVertexTargets
        SourceClauseRowWriterOperands.gateRowTargets n r S) x hc,
    SourceClauseRowWriterFanout.afterRow,
    SourceClausePreservingBroadcast.other_preserved
      SourceClauseRowWriterOperands.rowIndex
      SourceClauseRowWriterOperands.scratch
      SourceClauseRowWriterOperands.gateRowTargets
      (List.replicate r true) _ x hrow hs hr,
    SourceClauseRowWriterFanout.afterVertex,
    SourceClausePreservingBroadcast.other_preserved
      SourceClauseRowWriterOperands.vertex
      SourceClauseRowWriterOperands.scratch
      SourceClauseRowWriterOperands.gateVertexTargets
      (List.replicate n true) S x hv hs hn]

theorem unit_final_other {q : ℕ} (n r a k w ell : ℕ)
    (S : SourceClauseRowWriterOperands.Stack q → List Bool)
    (x : SourceClauseRowWriterOperands.Stack q)
    (hc : ∀ j : Fin 6, SourceClauseRowWriterOperands.unitConstants j ≠ x)
    (hn : x ∉ SourceClauseRowWriterOperands.unitVertexTargets)
    (hr : x ∉ SourceClauseRowWriterOperands.unitRowTargets)
    (hv : x ≠ SourceClauseRowWriterOperands.vertex)
    (hrow : x ≠ SourceClauseRowWriterOperands.rowIndex)
    (hs : x ≠ SourceClauseRowWriterOperands.scratch) :
    SourceClauseRowWriterStage.unitFinal n r a k w ell S x = S x := by
  rw [SourceClauseRowWriterStage.unitFinal,
    SourceClauseRowWriterOperands.unitFixedBank,
    SourceClauseFixedBatch.result_outside
      SourceClauseRowWriterOperands.unitConstants
      (SourceClauseRowWriterOperands.unitSizes a q k w ell)
      (SourceClauseRowWriterFanout.afterRow
        SourceClauseRowWriterOperands.unitVertexTargets
        SourceClauseRowWriterOperands.unitRowTargets n r S) x hc,
    SourceClauseRowWriterFanout.afterRow,
    SourceClausePreservingBroadcast.other_preserved
      SourceClauseRowWriterOperands.rowIndex
      SourceClauseRowWriterOperands.scratch
      SourceClauseRowWriterOperands.unitRowTargets
      (List.replicate r true) _ x hrow hs hr,
    SourceClauseRowWriterFanout.afterVertex,
    SourceClausePreservingBroadcast.other_preserved
      SourceClauseRowWriterOperands.vertex
      SourceClauseRowWriterOperands.scratch
      SourceClauseRowWriterOperands.unitVertexTargets
      (List.replicate n true) S x hv hs hn]

theorem gate_scratch_ne_core {q : ℕ}
    (x : SourceClauseRowWriterCore.Gate q)
    (hx : x ∉ Set.range (SourceClauseRowWriterCore.gateCore (q := q)))
    (c : SourceClauseRowWriterCore.Core q) :
    SourceClauseRowWriterOperands.gateCell x ≠ (.inl (.inl c) :
      SourceClauseRowWriterOperands.Stack q) := by
  intro h
  have he : SourceClauseRowWriterCore.gateEmbedding x =
      SourceClauseRowWriterCore.gateEmbedding
        (SourceClauseRowWriterCore.gateCore c) := by
    simpa only [SourceClauseRowWriterOperands.gateCell,
      SourceClauseRowWriterCore.gate_cell] using Sum.inl.inj h
  exact hx ⟨c, (SourceClauseRowWriterCore.gateEmbedding.injective he).symm⟩

theorem unit_scratch_ne_core {q : ℕ}
    (x : SourceClauseRowWriterCore.UnitBank q)
    (hx : x ∉ Set.range (SourceClauseRowWriterCore.unitCore (q := q)))
    (c : SourceClauseRowWriterCore.Core q) :
    SourceClauseRowWriterOperands.unitCell x ≠ (.inl (.inl c) :
      SourceClauseRowWriterOperands.Stack q) := by
  intro h
  have he : SourceClauseRowWriterCore.unitEmbedding x =
      SourceClauseRowWriterCore.unitEmbedding
        (SourceClauseRowWriterCore.unitCore c) := by
    simpa only [SourceClauseRowWriterOperands.unitCell,
      SourceClauseRowWriterCore.unit_cell] using Sum.inl.inj h
  exact hx ⟨c, (SourceClauseRowWriterCore.unitEmbedding.injective he).symm⟩

theorem gate_core_preserved {q : ℕ}
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r a k s t w : ℕ) (saved output count : List Bool)
    (c : SourceClauseRowWriterCore.Core q) :
    SourceClauseRowWriterStage.gateFinal n r a k s t w
      (SourceClauseRowWriterBlank.bank row n r saved output count)
      (.inl (.inl c)) = SourceClauseRowWriterBlank.core row saved output count c := by
  have hc : ∀ j : Fin 8,
      SourceClauseRowWriterOperands.gateConstants j ≠
        (.inl (.inl c) : SourceClauseRowWriterOperands.Stack q) := by
    intro j
    rw [gate_constant_cell]
    exact gate_scratch_ne_core _ (gate_constant_scratch j) c
  have hv : ∀ i : Fin 3,
      SourceClauseRowWriterOperands.gateCell (gateVariableLocal i) ≠
        (.inl (.inl c) : SourceClauseRowWriterOperands.Stack q) := by
    intro i
    exact gate_scratch_ne_core _ (gate_variable_scratch i) c
  rw [gate_final_other n r a k s t w
    (SourceClauseRowWriterBlank.bank row n r saved output count)
    (.inl (.inl c)) hc
    (by simpa [gate_vertex_targets] using
      (show (.inl (.inl c) : SourceClauseRowWriterOperands.Stack q) ≠
          SourceClauseRowWriterOperands.gateCell (gateVariableLocal 0) ∧
          (.inl (.inl c) : SourceClauseRowWriterOperands.Stack q) ≠
          SourceClauseRowWriterOperands.gateCell (gateVariableLocal 1) from
        ⟨(hv 0).symm, (hv 1).symm⟩))
    (by simpa [gate_row_targets] using (hv 2).symm)
    (by simp [SourceClauseRowWriterOperands.vertex])
    (by simp [SourceClauseRowWriterOperands.rowIndex])
    (by simp [SourceClauseRowWriterOperands.scratch])]
  rfl

theorem unit_core_preserved {q : ℕ}
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r a k w ell : ℕ) (saved output count : List Bool)
    (c : SourceClauseRowWriterCore.Core q) :
    SourceClauseRowWriterStage.unitFinal n r a k w ell
      (SourceClauseRowWriterBlank.bank row n r saved output count)
      (.inl (.inl c)) = SourceClauseRowWriterBlank.core row saved output count c := by
  have hc : ∀ j : Fin 6,
      SourceClauseRowWriterOperands.unitConstants j ≠
        (.inl (.inl c) : SourceClauseRowWriterOperands.Stack q) := by
    intro j
    rw [unit_constant_cell]
    exact unit_scratch_ne_core _ (unit_constant_scratch j) c
  have hv : ∀ i : Fin 3,
      SourceClauseRowWriterOperands.unitCell (unitVariableLocal i) ≠
        (.inl (.inl c) : SourceClauseRowWriterOperands.Stack q) := by
    intro i
    exact unit_scratch_ne_core _ (unit_variable_scratch i) c
  rw [unit_final_other n r a k w ell
    (SourceClauseRowWriterBlank.bank row n r saved output count)
    (.inl (.inl c)) hc
    (by simpa [unit_vertex_targets] using
      (show (.inl (.inl c) : SourceClauseRowWriterOperands.Stack q) ≠
          SourceClauseRowWriterOperands.unitCell (unitVariableLocal 0) ∧
          (.inl (.inl c) : SourceClauseRowWriterOperands.Stack q) ≠
          SourceClauseRowWriterOperands.unitCell (unitVariableLocal 1) from
        ⟨(hv 0).symm, (hv 1).symm⟩))
    (by simpa [unit_row_targets] using (hv 2).symm)
    (by simp [SourceClauseRowWriterOperands.vertex])
    (by simp [SourceClauseRowWriterOperands.rowIndex])
    (by simp [SourceClauseRowWriterOperands.scratch])]
  rfl

end EthInapproximability.CurrentPaper.SourceClauseRowWriterStageReady
