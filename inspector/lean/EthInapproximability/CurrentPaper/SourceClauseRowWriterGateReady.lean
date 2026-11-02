import EthInapproximability.CurrentPaper.SourceClauseRowWriterStageEcho

/-!
# Remaining physical OR-gate initial-bank compatibility

This file checks the finite address and writer scratch branches after the
charged n/r, fixed-word, and checked-query staging sequence.
-/

namespace EthInapproximability.CurrentPaper.SourceClauseRowWriterGateReady

open scoped Classical

theorem variable_after_echo {q : ℕ} (j : Fin q)
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r a k s t w : ℕ) (saved output count : List Bool)
    (i : Fin 3) :
    SourceClauseRowWriterStageEcho.prepared j row n r a k s t w
      saved output count
      (SourceClauseRowWriterOperands.gateCell
        (SourceClauseRowWriterStageReady.gateVariableLocal i)) =
    List.replicate (if i = 2 then r else n) true := by
  have hs : SourceClauseRowWriterOperands.gateCell
      (SourceClauseRowWriterStageReady.gateVariableLocal i) ≠
      SourceClauseRowWriterQueryEcho.source j := by
    have h := SourceClauseRowWriterStageReady.gate_scratch_ne_core
      (SourceClauseRowWriterStageReady.gateVariableLocal i)
      (SourceClauseRowWriterStageReady.gate_variable_scratch i)
      (.inl (.inl (j, 1)) : SourceClauseRowWriterCore.Core q)
    simpa [SourceClauseRowWriterQueryEcho.source] using h
  have ht : SourceClauseRowWriterOperands.gateCell
      (SourceClauseRowWriterStageReady.gateVariableLocal (q := q) i) ≠
      (SourceClauseRowWriterQueryEcho.temp :
        SourceClauseRowWriterOperands.Stack q) := by
    simp [SourceClauseRowWriterOperands.gateCell,
      SourceClauseRowWriterQueryEcho.temp,
      SourceClauseRowWriterOperands.scratch]
  have hx : SourceClauseRowWriterOperands.gateCell
      (SourceClauseRowWriterStageReady.gateVariableLocal (q := q) i) ∉
      [SourceClauseRowWriterQueryEcho.target (q := q)] := by
    fin_cases i <;>
      simp [SourceClauseRowWriterStageReady.gateVariableLocal,
        SourceClauseRowWriterQueryEcho.target,
        SourceClauseRowWriterOperands.gateCell,
        SourceClauseRowWriterOperands.gateSlot,
        SourceClauseRowWriterOperands.gateLiteral,
        SourceClauseRowWriterOperands.gateOffset,
        SourceClauseRowIndexedGate.gateEmbedding,
        SourceClauseRowGate.addressEmbedding,
        SourceClauseRowGate.gateEmbedding,
        SourceClauseGateSlotAddress.offsetEmbedding]
  rw [SourceClauseRowWriterStageEcho.prepared,
    SourceClauseRowWriterQueryEcho.after,
    SourceClausePreservingBroadcast.other_preserved
      (SourceClauseRowWriterQueryEcho.source j)
      SourceClauseRowWriterQueryEcho.temp
      [SourceClauseRowWriterQueryEcho.target]
      (row (.inl (j, 1)))
      (SourceClauseRowWriterStage.gateFinal n r a k s t w
        (SourceClauseRowWriterBlank.bank row n r saved output count))
      (SourceClauseRowWriterOperands.gateCell
        (SourceClauseRowWriterStageReady.gateVariableLocal i)) hs ht hx]
  exact SourceClauseRowWriterStageReady.gate_variable_inputs
    row n r a k s t w saved output count i

theorem offset_other {q : ℕ} (j : Fin q)
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r a k s t w : ℕ) (saved output count : List Bool)
    (i : Fin 6) (h0 : i ≠ 0) (h1 : i ≠ 1) (h2 : i ≠ 2) :
    SourceClauseRowWriterStageEcho.prepared j row n r a k s t w
      saved output count
      (SourceClauseRowWriterOperands.gateCell
        (SourceClauseRowWriterOperands.gateOffset i)) =
    SourceClauseRowIndexedGate.initial j row n r a k s t w
      saved output count (SourceClauseRowWriterOperands.gateOffset i) := by
  have hz : SourceClauseRowIndexedGate.initial j row n r a k s t w
      saved output count (SourceClauseRowWriterOperands.gateOffset i) = [] := by
    fin_cases i <;>
      simp_all [SourceClauseRowWriterOperands.gateOffset,
        SourceClauseRowIndexedGate.initial,
        SourceClauseRowIndexedGate.gateEmbedding,
        SourceClauseRowGate.initial,
        SourceClauseRowGate.gateEmbedding,
        SourceClauseGateSlotAddress.initial,
        SourceClauseGateSlotAddress.offsetEmbedding,
        SourceClauseGateSlotAddress.offsetInput,
        MatrixAddressMachine.cfg]
  rw [hz]
  apply SourceClauseRowWriterStageEcho.other_empty_after_echo
  · rintro ⟨c, hc⟩
    cases c with
    | inl x =>
        simp [SourceClauseRowWriterOperands.gateOffset,
          SourceClauseRowWriterCore.gateCore,
          SourceClauseRowWriterCore.gateCoreCell,
          SourceClauseRowGateCleanup.rowCell,
          SourceClauseRowIndexedGate.gateEmbedding,
          SourceClauseRowGate.gateEmbedding] at hc
    | inr z =>
        fin_cases z <;>
          simp [SourceClauseRowWriterOperands.gateOffset,
            SourceClauseRowWriterCore.gateCore,
            SourceClauseRowWriterCore.gateCoreCell,
            SourceClauseRowGateCleanup.savedCell,
            SourceClauseRowGateCleanup.outputCell,
            SourceClauseRowGateCleanup.countCell,
            SourceClauseRowIndexedGate.gateEmbedding,
            SourceClauseRowGate.gateEmbedding,
            SourceClauseGateSlotAddress.offsetEmbedding,
            SourceClauseGateSlotAddress.gateEmbedding,
            SourceClauseGateAffineAddress.gateEmbedding] at hc
  · intro z; fin_cases z <;>
      simp_all [SourceClauseRowWriterOperands.gateConstants,
        SourceClauseRowWriterOperands.gateCell,
        SourceClauseRowWriterOperands.gateSlot,
        SourceClauseRowWriterOperands.gateLiteral,
        SourceClauseRowWriterOperands.gateOffset,
        SourceClauseRowWriterOperands.gateAffine,
        SourceClauseRowIndexedGate.gateEmbedding,
        SourceClauseRowGate.addressEmbedding,
        SourceClauseRowGate.gateEmbedding,
        SourceClauseGateSlotAddress.offsetEmbedding,
        SourceClauseGateSlotAddress.gateEmbedding,
        SourceClauseGateAffineAddress.addressEmbedding] <;>
      first | exact fun h => h1 h.symm | exact fun h => h2 h.symm
  · simp [SourceClauseRowWriterOperands.gateVertexTargets,
      SourceClauseRowWriterOperands.gateCell,
      SourceClauseRowWriterOperands.gateSlot,
      SourceClauseRowWriterOperands.gateOffset,
      SourceClauseRowIndexedGate.gateEmbedding,
      SourceClauseRowGate.gateEmbedding,
      SourceClauseGateSlotAddress.offsetEmbedding,
      h0]
  · simp [SourceClauseRowWriterOperands.gateRowTargets,
      SourceClauseRowWriterOperands.gateCell,
      SourceClauseRowWriterOperands.gateSlot,
      SourceClauseRowWriterOperands.gateOffset,
      SourceClauseRowIndexedGate.gateEmbedding,
      SourceClauseRowGate.gateEmbedding]
  · simp [SourceClauseRowWriterOperands.gateOffset,
      SourceClauseRowWriterOperands.gateLiteral,
      SourceClauseRowIndexedGate.gateEmbedding,
      SourceClauseRowGate.addressEmbedding,
      SourceClauseRowGate.gateEmbedding]

theorem offset_input {q : ℕ} (j : Fin q)
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r a k s t w : ℕ) (saved output count : List Bool)
    (i : Fin 6) :
    SourceClauseRowWriterStageEcho.prepared j row n r a k s t w
      saved output count
      (SourceClauseRowWriterOperands.gateCell
        (SourceClauseRowWriterOperands.gateOffset i)) =
    SourceClauseRowIndexedGate.initial j row n r a k s t w
      saved output count (SourceClauseRowWriterOperands.gateOffset i) := by
  fin_cases i
  · simpa [SourceClauseRowWriterStageReady.gateVariableLocal,
      SourceClauseRowWriterOperands.gateOffset,
      SourceClauseRowIndexedGate.initial,
      SourceClauseRowGate.initial,
      SourceClauseGateSlotAddress.initial,
      SourceClauseGateSlotAddress.offsetInput,
      MatrixAddressMachine.cfg] using
      variable_after_echo
        j row n r a k s t w saved output count 1
  · simpa [SourceClauseRowWriterStageReady.gateConstantLocal,
      SourceClauseRowWriterOperands.gateOffset,
      SourceClauseRowWriterOperands.gateSizes,
      SourceClauseRowIndexedGate.initial,
      SourceClauseRowGate.initial,
      SourceClauseGateSlotAddress.initial,
      SourceClauseGateSlotAddress.offsetInput,
      MatrixAddressMachine.cfg] using
      SourceClauseRowWriterStageEcho.fixed_after_echo
        j row n r a k s t w saved output count 5
  · simpa [SourceClauseRowWriterStageReady.gateConstantLocal,
      SourceClauseRowWriterOperands.gateOffset,
      SourceClauseRowWriterOperands.gateSizes,
      SourceClauseRowIndexedGate.initial,
      SourceClauseRowGate.initial,
      SourceClauseGateSlotAddress.initial,
      SourceClauseGateSlotAddress.offsetInput,
      MatrixAddressMachine.cfg] using
      SourceClauseRowWriterStageEcho.fixed_after_echo
        j row n r a k s t w saved output count 6
  all_goals
    apply offset_other j row n r a k s t w saved output count
    all_goals decide

theorem affine_other {q : ℕ} (j : Fin q)
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r a k s t w : ℕ) (saved output count : List Bool)
    (x : SourceLabelAddressMachine.Stack) (h1 : x ≠ .inl 1) :
    SourceClauseRowWriterStageEcho.prepared j row n r a k s t w
      saved output count
      (SourceClauseRowWriterOperands.gateCell
        (SourceClauseRowWriterOperands.gateAffine x)) =
    SourceClauseRowIndexedGate.initial j row n r a k s t w
      saved output count (SourceClauseRowWriterOperands.gateAffine x) := by
  have hz : SourceClauseRowIndexedGate.initial j row n r a k s t w
      saved output count (SourceClauseRowWriterOperands.gateAffine x) = [] := by
    cases x with
    | inl i =>
        fin_cases i <;>
          simp_all [SourceClauseRowWriterOperands.gateAffine,
            SourceClauseRowIndexedGate.initial,
            SourceClauseRowIndexedGate.gateEmbedding,
            SourceClauseRowGate.initial,
            SourceClauseRowGate.gateEmbedding,
            SourceClauseGateSlotAddress.initial,
            SourceClauseGateSlotAddress.gateEmbedding,
            SourceClauseGateAffineAddress.initial,
            SourceClauseGateAffineAddress.addressEmbedding,
            SourceLabelAddressMachine.inputs,
            SourceLabelAddressMachine.ambient]
    | inr y =>
        simp [SourceClauseRowWriterOperands.gateAffine,
          SourceClauseRowIndexedGate.initial,
          SourceClauseRowIndexedGate.gateEmbedding,
          SourceClauseRowGate.initial,
          SourceClauseRowGate.gateEmbedding,
          SourceClauseGateSlotAddress.initial,
          SourceClauseGateSlotAddress.gateEmbedding,
          SourceClauseGateAffineAddress.initial,
          SourceClauseGateAffineAddress.addressEmbedding,
          SourceLabelAddressMachine.inputs,
          SourceLabelAddressMachine.ambient]
  rw [hz]
  apply SourceClauseRowWriterStageEcho.other_empty_after_echo
  · rintro ⟨c, hc⟩
    cases c with
    | inl y =>
        simp [SourceClauseRowWriterOperands.gateAffine,
          SourceClauseRowWriterCore.gateCore,
          SourceClauseRowWriterCore.gateCoreCell,
          SourceClauseRowGateCleanup.rowCell,
          SourceClauseRowIndexedGate.gateEmbedding,
          SourceClauseRowGate.gateEmbedding] at hc
    | inr z =>
        fin_cases z <;>
          simp [SourceClauseRowWriterOperands.gateAffine,
            SourceClauseRowWriterCore.gateCore,
            SourceClauseRowWriterCore.gateCoreCell,
            SourceClauseRowGateCleanup.savedCell,
            SourceClauseRowGateCleanup.outputCell,
            SourceClauseRowGateCleanup.countCell,
            SourceClauseRowIndexedGate.gateEmbedding,
            SourceClauseRowGate.gateEmbedding,
            SourceClauseGateSlotAddress.gateEmbedding,
            SourceClauseGateAffineAddress.addressEmbedding,
            SourceClauseGateAffineAddress.gateEmbedding] at hc
  · intro z; fin_cases z <;>
      simp_all [SourceClauseRowWriterOperands.gateConstants,
        SourceClauseRowWriterOperands.gateCell,
        SourceClauseRowWriterOperands.gateSlot,
        SourceClauseRowWriterOperands.gateLiteral,
        SourceClauseRowWriterOperands.gateOffset,
        SourceClauseRowWriterOperands.gateAffine,
        SourceClauseRowIndexedGate.gateEmbedding,
        SourceClauseRowGate.addressEmbedding,
        SourceClauseRowGate.gateEmbedding,
        SourceClauseGateSlotAddress.offsetEmbedding,
        SourceClauseGateSlotAddress.gateEmbedding,
        SourceClauseGateAffineAddress.addressEmbedding] <;>
      exact fun h => h1 h.symm
  · simp [SourceClauseRowWriterOperands.gateVertexTargets,
      SourceClauseRowWriterOperands.gateCell,
      SourceClauseRowWriterOperands.gateSlot,
      SourceClauseRowWriterOperands.gateOffset,
      SourceClauseRowWriterOperands.gateAffine,
      SourceClauseRowIndexedGate.gateEmbedding,
      SourceClauseRowGate.gateEmbedding,
      SourceClauseGateSlotAddress.offsetEmbedding,
      SourceClauseGateSlotAddress.gateEmbedding]
  · simp [SourceClauseRowWriterOperands.gateRowTargets,
      SourceClauseRowWriterOperands.gateCell,
      SourceClauseRowWriterOperands.gateSlot,
      SourceClauseRowWriterOperands.gateAffine,
      SourceClauseRowIndexedGate.gateEmbedding,
      SourceClauseRowGate.gateEmbedding]
  · simp [SourceClauseRowWriterOperands.gateAffine,
      SourceClauseRowWriterOperands.gateLiteral,
      SourceClauseRowIndexedGate.gateEmbedding,
      SourceClauseRowGate.addressEmbedding,
      SourceClauseRowGate.gateEmbedding]

theorem affine_input {q : ℕ} (j : Fin q)
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r a k s t w : ℕ) (saved output count : List Bool)
    (x : SourceLabelAddressMachine.Stack) :
    SourceClauseRowWriterStageEcho.prepared j row n r a k s t w
      saved output count
      (SourceClauseRowWriterOperands.gateCell
        (SourceClauseRowWriterOperands.gateAffine x)) =
    SourceClauseRowIndexedGate.initial j row n r a k s t w
      saved output count (SourceClauseRowWriterOperands.gateAffine x) := by
  by_cases h : x = (.inl 1 : SourceLabelAddressMachine.Stack)
  · subst x
    simpa [SourceClauseRowWriterStageReady.gateConstantLocal,
      SourceClauseRowWriterOperands.gateAffine,
      SourceClauseRowWriterOperands.gateSizes,
      SourceClauseRowIndexedGate.initial,
      SourceClauseRowGate.initial,
      SourceClauseGateSlotAddress.initial,
      SourceClauseGateAffineAddress.initial,
      SourceLabelAddressMachine.inputs,
      SourceLabelAddressMachine.ambient] using
      SourceClauseRowWriterStageEcho.fixed_after_echo
        j row n r a k s t w saved output count 7
  · exact affine_other j row n r a k s t w saved output count x h

def twoCell {q : ℕ} (x : SourceClauseGateTwoAddress.Stack) :
    SourceClauseRowWriterCore.Gate q :=
  SourceClauseRowIndexedGate.gateEmbedding
    (SourceClauseRowGate.gateEmbedding
      (SourceClauseGateSlotAddress.gateEmbedding
        (SourceClauseGateAffineAddress.gateEmbedding x)))

def twoSaved : SourceClauseGateTwoAddress.Stack :=
  .inr (.inr (.inr (.inl 0)))
def twoOutput : SourceClauseGateTwoAddress.Stack :=
  .inr (.inr (.inr (.inl 1)))
def twoCount : SourceClauseGateTwoAddress.Stack :=
  .inr (.inr (.inr (.inr ())))

theorem two_other {q : ℕ} (j : Fin q)
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r a k s t w : ℕ) (saved output count : List Bool)
    (x : SourceClauseGateTwoAddress.Stack)
    (hs : x ≠ twoSaved) (ho : x ≠ twoOutput) (hc : x ≠ twoCount) :
    SourceClauseRowWriterStageEcho.prepared j row n r a k s t w
      saved output count (SourceClauseRowWriterOperands.gateCell (twoCell x)) =
    SourceClauseRowIndexedGate.initial j row n r a k s t w
      saved output count (twoCell x) := by
  have hz : SourceClauseRowIndexedGate.initial j row n r a k s t w
      saved output count (twoCell x) = [] := by
    cases x with
    | inl i =>
        fin_cases i <;>
          simp [twoCell, SourceClauseRowIndexedGate.initial,
            SourceClauseRowIndexedGate.gateEmbedding,
            SourceClauseRowGate.initial,
            SourceClauseRowGate.gateEmbedding,
            SourceClauseGateSlotAddress.initial,
            SourceClauseGateSlotAddress.gateEmbedding,
            SourceClauseGateAffineAddress.initial,
            SourceClauseGateAffineAddress.gateEmbedding,
            SourceClauseGateSuccessor.initial]
    | inr y =>
        cases y with
        | inl i =>
            fin_cases i <;>
              simp [twoCell, SourceClauseRowIndexedGate.initial,
                SourceClauseRowIndexedGate.gateEmbedding,
                SourceClauseRowGate.initial,
                SourceClauseRowGate.gateEmbedding,
                SourceClauseGateSlotAddress.initial,
                SourceClauseGateSlotAddress.gateEmbedding,
                SourceClauseGateAffineAddress.initial,
                SourceClauseGateAffineAddress.gateEmbedding,
                SourceClauseGateSuccessor.initial,
                SourceClauseGateBroadcast.initial]
        | inr z =>
            cases z with
            | inl i =>
                simp [twoCell, SourceClauseRowIndexedGate.initial,
                  SourceClauseRowIndexedGate.gateEmbedding,
                  SourceClauseRowGate.initial,
                  SourceClauseRowGate.gateEmbedding,
                  SourceClauseGateSlotAddress.initial,
                  SourceClauseGateSlotAddress.gateEmbedding,
                  SourceClauseGateAffineAddress.initial,
                  SourceClauseGateAffineAddress.gateEmbedding,
                  SourceClauseGateSuccessor.initial,
                  SourceClauseGateBroadcast.initial,
                  SourceClauseGateSchedule.contents]
            | inr v =>
                cases v with
                | inl i => fin_cases i <;> simp_all [twoSaved, twoOutput]
                | inr u => cases u; exact (hc rfl).elim
  rw [hz]
  apply SourceClauseRowWriterStageEcho.other_empty_after_echo
  · rintro ⟨c, he⟩
    cases c with
    | inl y =>
        simp [twoCell, SourceClauseRowWriterCore.gateCore,
          SourceClauseRowWriterCore.gateCoreCell,
          SourceClauseRowGateCleanup.rowCell,
          SourceClauseRowIndexedGate.gateEmbedding,
          SourceClauseRowGate.gateEmbedding] at he
    | inr z =>
        fin_cases z <;>
          simp_all [twoCell, twoSaved, twoOutput, twoCount,
            SourceClauseRowWriterCore.gateCore,
            SourceClauseRowWriterCore.gateCoreCell,
            SourceClauseRowGateCleanup.savedCell,
            SourceClauseRowGateCleanup.outputCell,
            SourceClauseRowGateCleanup.countCell,
            SourceClauseRowIndexedGate.gateEmbedding,
            SourceClauseRowGate.gateEmbedding,
            SourceClauseGateSlotAddress.gateEmbedding,
            SourceClauseGateAffineAddress.gateEmbedding,
            SourceClauseGateTwoAddress.embedding,
            SourceClauseGateMachine.embedding]
  · intro z; fin_cases z <;>
      simp [twoCell, SourceClauseRowWriterOperands.gateConstants,
        SourceClauseRowWriterOperands.gateCell,
        SourceClauseRowWriterOperands.gateSlot,
        SourceClauseRowWriterOperands.gateLiteral,
        SourceClauseRowWriterOperands.gateOffset,
        SourceClauseRowWriterOperands.gateAffine,
        SourceClauseRowIndexedGate.gateEmbedding,
        SourceClauseRowGate.addressEmbedding,
        SourceClauseRowGate.gateEmbedding,
        SourceClauseGateSlotAddress.offsetEmbedding,
        SourceClauseGateSlotAddress.gateEmbedding,
        SourceClauseGateAffineAddress.addressEmbedding,
        SourceClauseGateAffineAddress.gateEmbedding]
  · simp [twoCell, SourceClauseRowWriterOperands.gateVertexTargets,
      SourceClauseRowWriterOperands.gateCell,
      SourceClauseRowWriterOperands.gateSlot,
      SourceClauseRowWriterOperands.gateOffset,
      SourceClauseRowIndexedGate.gateEmbedding,
      SourceClauseRowGate.gateEmbedding,
      SourceClauseGateSlotAddress.offsetEmbedding,
      SourceClauseGateSlotAddress.gateEmbedding]
  · simp [twoCell, SourceClauseRowWriterOperands.gateRowTargets,
      SourceClauseRowWriterOperands.gateCell,
      SourceClauseRowWriterOperands.gateSlot,
      SourceClauseRowIndexedGate.gateEmbedding,
      SourceClauseRowGate.gateEmbedding]
  · simp [twoCell, SourceClauseRowWriterOperands.gateLiteral,
      SourceClauseRowIndexedGate.gateEmbedding,
      SourceClauseRowGate.addressEmbedding,
      SourceClauseRowGate.gateEmbedding]

theorem two_input {q : ℕ} (j : Fin q)
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r a k s t w : ℕ) (saved output count : List Bool)
    (x : SourceClauseGateTwoAddress.Stack) :
    SourceClauseRowWriterStageEcho.prepared j row n r a k s t w
      saved output count (SourceClauseRowWriterOperands.gateCell (twoCell x)) =
    SourceClauseRowIndexedGate.initial j row n r a k s t w
      saved output count (twoCell x) := by
  by_cases hs : x = twoSaved
  · subst x
    simpa [twoCell, twoSaved,
      SourceClauseRowWriterCore.gateCore,
      SourceClauseRowWriterCore.gateCoreCell,
      SourceClauseRowGateCleanup.savedCell,
      SourceClauseRowIndexedGate.gateEmbedding,
      SourceClauseRowGate.gateEmbedding,
      SourceClauseGateSlotAddress.gateEmbedding,
      SourceClauseGateAffineAddress.gateEmbedding,
      SourceClauseGateTwoAddress.embedding,
      SourceClauseGateMachine.embedding] using
      SourceClauseRowWriterStageEcho.core_after_echo
        j row n r a k s t w saved output count (.inr 0)
  by_cases ho : x = twoOutput
  · subst x
    simpa [twoCell, twoOutput,
      SourceClauseRowWriterCore.gateCore,
      SourceClauseRowWriterCore.gateCoreCell,
      SourceClauseRowGateCleanup.outputCell,
      SourceClauseRowIndexedGate.gateEmbedding,
      SourceClauseRowGate.gateEmbedding,
      SourceClauseGateSlotAddress.gateEmbedding,
      SourceClauseGateAffineAddress.gateEmbedding,
      SourceClauseGateTwoAddress.embedding,
      SourceClauseGateMachine.embedding] using
      SourceClauseRowWriterStageEcho.core_after_echo
        j row n r a k s t w saved output count (.inr 1)
  by_cases hc : x = twoCount
  · subst x
    simpa [twoCell, twoCount,
      SourceClauseRowWriterCore.gateCore,
      SourceClauseRowWriterCore.gateCoreCell,
      SourceClauseRowGateCleanup.countCell,
      SourceClauseRowIndexedGate.gateEmbedding,
      SourceClauseRowGate.gateEmbedding,
      SourceClauseGateSlotAddress.gateEmbedding,
      SourceClauseGateAffineAddress.gateEmbedding,
      SourceClauseGateTwoAddress.embedding,
      SourceClauseGateMachine.embedding] using
      SourceClauseRowWriterStageEcho.core_after_echo
        j row n r a k s t w saved output count (.inr 2)
  exact two_other j row n r a k s t w saved output count x hs ho hc

theorem row_temp_input {q : ℕ} (j : Fin q)
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r a k s t w : ℕ) (saved output count : List Bool) :
    SourceClauseRowWriterStageEcho.prepared j row n r a k s t w
      saved output count
      (SourceClauseRowWriterOperands.gateCell
        (SourceClauseRowIndexedGate.gateEmbedding (.inr (.inr 0)))) =
    SourceClauseRowIndexedGate.initial j row n r a k s t w
      saved output count
      (SourceClauseRowIndexedGate.gateEmbedding (.inr (.inr 0))) := by
  simp only [SourceClauseRowIndexedGate.initial,
    SourceClauseRowIndexedGate.gateEmbedding,
    SourceClauseRowGate.initial]
  apply SourceClauseRowWriterStageEcho.other_empty_after_echo
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
        SourceClauseRowIndexedGate.gateEmbedding,
        SourceClauseRowGate.addressEmbedding,
        SourceClauseRowGate.gateEmbedding]
  · simp [SourceClauseRowWriterOperands.gateVertexTargets,
      SourceClauseRowWriterOperands.gateCell,
      SourceClauseRowWriterOperands.gateSlot,
      SourceClauseRowWriterOperands.gateOffset,
      SourceClauseRowIndexedGate.gateEmbedding,
      SourceClauseRowGate.gateEmbedding]
  · simp [SourceClauseRowWriterOperands.gateRowTargets,
      SourceClauseRowWriterOperands.gateCell,
      SourceClauseRowWriterOperands.gateSlot,
      SourceClauseRowIndexedGate.gateEmbedding]
  · simp [SourceClauseRowWriterOperands.gateLiteral,
      SourceClauseRowIndexedGate.gateEmbedding,
      SourceClauseRowGate.addressEmbedding]

theorem outer_temp_input {q : ℕ} (j : Fin q)
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r a k s t w : ℕ) (saved output count : List Bool) :
    SourceClauseRowWriterStageEcho.prepared j row n r a k s t w
      saved output count
      (SourceClauseRowWriterOperands.gateCell (.inr (.inr 0))) =
    SourceClauseRowIndexedGate.initial j row n r a k s t w
      saved output count (.inr (.inr 0)) := by
  simp only [SourceClauseRowIndexedGate.initial]
  apply SourceClauseRowWriterStageEcho.other_empty_after_echo
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
            SourceClauseRowIndexedGate.gateEmbedding] at hc
  · intro z; fin_cases z <;>
      simp [SourceClauseRowWriterOperands.gateConstants,
        SourceClauseRowWriterOperands.gateCell,
        SourceClauseRowWriterOperands.gateSlot,
        SourceClauseRowWriterOperands.gateLiteral,
        SourceClauseRowWriterOperands.gateOffset,
        SourceClauseRowWriterOperands.gateAffine,
        SourceClauseRowIndexedGate.gateEmbedding]
  · simp [SourceClauseRowWriterOperands.gateVertexTargets,
      SourceClauseRowWriterOperands.gateCell,
      SourceClauseRowWriterOperands.gateSlot,
      SourceClauseRowWriterOperands.gateOffset,
      SourceClauseRowIndexedGate.gateEmbedding]
  · simp [SourceClauseRowWriterOperands.gateRowTargets,
      SourceClauseRowWriterOperands.gateCell,
      SourceClauseRowWriterOperands.gateSlot,
      SourceClauseRowIndexedGate.gateEmbedding]
  · simp [SourceClauseRowWriterOperands.gateLiteral,
      SourceClauseRowIndexedGate.gateEmbedding]

theorem gate_initial_bank {q : ℕ} (j : Fin q)
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r a k s t w : ℕ) (saved output count : List Bool)
    (h : row (.inl (j, 1)) =
      List.replicate (row (.inl (j, 1))).length true)
    (x : SourceClauseRowWriterCore.Gate q) :
    SourceClauseRowWriterStageEcho.prepared j row n r a k s t w
      saved output count (SourceClauseRowWriterOperands.gateCell x) =
    SourceClauseRowIndexedGate.initial j row n r a k s t w
      saved output count x := by
  cases x with
  | inl slot =>
      exact SourceClauseRowWriterStageEcho.slot_after_echo
        j row n r a k s t w saved output count slot
  | inr y =>
      cases y with
      | inl g =>
          cases g with
          | inl address =>
              cases address with
              | inl word =>
                  simpa [SourceClauseRowWriterCore.gateCore,
                    SourceClauseRowWriterCore.gateCoreCell,
                    SourceClauseRowGateCleanup.rowCell,
                    SourceClauseRowIndexedGate.gateEmbedding] using
                    SourceClauseRowWriterStageEcho.core_after_echo
                      j row n r a k s t w saved output count (.inl word)
              | inr word =>
                  exact SourceClauseRowWriterStageEcho.literal_input_after_echo
                    j row n r a k s t w saved output count h word
          | inr u =>
              cases u with
              | inl gate =>
                  cases gate with
                  | inl offset =>
                      exact offset_input j row n r a k s t w
                        saved output count offset
                  | inr affine =>
                      cases affine with
                      | inl label =>
                          exact affine_input j row n r a k s t w
                            saved output count label
                      | inr two =>
                          exact two_input j row n r a k s t w
                            saved output count two
              | inr temp =>
                  fin_cases temp
                  exact row_temp_input j row n r a k s t w saved output count
      | inr temp =>
          fin_cases temp
          exact outer_temp_input j row n r a k s t w saved output count

end EthInapproximability.CurrentPaper.SourceClauseRowWriterGateReady
