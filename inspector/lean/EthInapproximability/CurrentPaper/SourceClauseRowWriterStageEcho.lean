import EthInapproximability.CurrentPaper.SourceClauseRowWriterQueryEcho

/-!
# Charged gate staging followed by a physical checked-query copy

This sequence prepares fixed and varying arithmetic words, then copies the
validated unary query into the frozen gate's duplicate initial input.
-/

namespace EthInapproximability.CurrentPaper.SourceClauseRowWriterStageEcho

open Turing BitMachineEncoding
open scoped Classical

noncomputable def program {q : ℕ} (j : Fin q) (a k s t w : ℕ) :=
  BitMachineRawSequence.program
    (SourceClauseRowWriterStage.gateProgram (q := q) a k s t w)
    (SourceClauseRowWriterQueryEcho.program j)
    SourceClausePreservingBroadcast.Label.scan
    ((((), none), ((), none)), ()) ((), none)

noncomputable def prepared {q : ℕ} (j : Fin q)
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r a k s t w : ℕ) (saved output count : List Bool) :=
  SourceClauseRowWriterQueryEcho.after j
    (row (.inl (j, 1)))
    (SourceClauseRowWriterStage.gateFinal n r a k s t w
      (SourceClauseRowWriterBlank.bank row n r saved output count))

theorem source_after_stage {q : ℕ} (j : Fin q)
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r a k s t w : ℕ) (saved output count : List Bool) :
    SourceClauseRowWriterStage.gateFinal n r a k s t w
      (SourceClauseRowWriterBlank.bank row n r saved output count)
      (SourceClauseRowWriterQueryEcho.source j) = row (.inl (j, 1)) := by
  simpa [SourceClauseRowWriterQueryEcho.source,
    SourceClauseRowWriterBlank.core] using
    SourceClauseRowWriterStageReady.gate_core_preserved
      row n r a k s t w saved output count
      (.inl (.inl (j, 1)))

theorem scratch_after_stage {q : ℕ}
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r a k s t w : ℕ) (saved output count : List Bool) :
    SourceClauseRowWriterStage.gateFinal n r a k s t w
      (SourceClauseRowWriterBlank.bank row n r saved output count)
      SourceClauseRowWriterQueryEcho.temp = [] := by
  rw [SourceClauseRowWriterStage.gateFinal,
    SourceClauseRowWriterOperands.gateFixedBank,
    SourceClauseFixedBatch.result_outside]
  · exact SourceClausePreservingBroadcast.temp_empty
      SourceClauseRowWriterOperands.rowIndex
      SourceClauseRowWriterOperands.scratch
      SourceClauseRowWriterOperands.gateRowTargets
      (List.replicate r true)
      (SourceClauseRowWriterFanout.afterVertex
        SourceClauseRowWriterOperands.gateVertexTargets n
        (SourceClauseRowWriterBlank.bank row n r saved output count))
  · intro i; fin_cases i <;>
      simp [SourceClauseRowWriterQueryEcho.temp,
        SourceClauseRowWriterOperands.gateConstants,
        SourceClauseRowWriterOperands.gateCell,
        SourceClauseRowWriterOperands.scratch]

theorem target_blank_after_stage {q : ℕ} (j : Fin q)
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r a k s t w : ℕ) (saved output count : List Bool) :
    SourceClauseRowWriterStage.gateFinal n r a k s t w
      (SourceClauseRowWriterBlank.bank row n r saved output count)
      SourceClauseRowWriterQueryEcho.target = [] := by
  apply SourceClauseRowWriterInitial.gate_other_empty
  · rintro ⟨c, hc⟩
    cases c with
    | inl x =>
        simp [SourceClauseRowWriterOperands.gateLiteral,
          SourceClauseRowWriterCore.gateCore,
          SourceClauseRowWriterCore.gateCoreCell,
          SourceClauseRowGateCleanup.rowCell,
          SourceClauseRowIndexedGate.gateEmbedding,
          SourceClauseRowGate.addressEmbedding] at hc
    | inr z =>
        fin_cases z <;>
          simp [SourceClauseRowWriterOperands.gateLiteral,
            SourceClauseRowWriterCore.gateCore,
            SourceClauseRowWriterCore.gateCoreCell,
            SourceClauseRowGateCleanup.savedCell,
            SourceClauseRowGateCleanup.outputCell,
            SourceClauseRowGateCleanup.countCell,
            SourceClauseRowIndexedGate.gateEmbedding,
            SourceClauseRowGate.gateEmbedding,
            SourceClauseRowGate.addressEmbedding] at hc
  · intro i; fin_cases i <;>
      simp [SourceClauseRowWriterOperands.gateConstants,
        SourceClauseRowWriterOperands.gateCell,
        SourceClauseRowWriterOperands.gateLiteral,
        SourceClauseRowWriterOperands.gateSlot,
        SourceClauseRowWriterOperands.gateOffset,
        SourceClauseRowWriterOperands.gateAffine,
        SourceClauseRowIndexedGate.gateEmbedding,
        SourceClauseRowGate.addressEmbedding,
        SourceClauseRowGate.gateEmbedding,
        SourceClauseGateSlotAddress.offsetEmbedding,
        SourceClauseGateSlotAddress.gateEmbedding,
        SourceClauseGateAffineAddress.addressEmbedding]
  · simp [SourceClauseRowWriterOperands.gateVertexTargets,
      SourceClauseRowWriterOperands.gateCell,
      SourceClauseRowWriterOperands.gateLiteral,
      SourceClauseRowWriterOperands.gateSlot,
      SourceClauseRowWriterOperands.gateOffset,
      SourceClauseRowIndexedGate.gateEmbedding,
      SourceClauseRowGate.addressEmbedding,
      SourceClauseRowGate.gateEmbedding,
      SourceClauseGateSlotAddress.offsetEmbedding]
  · simp [SourceClauseRowWriterOperands.gateRowTargets,
      SourceClauseRowWriterOperands.gateCell,
      SourceClauseRowWriterOperands.gateLiteral,
      SourceClauseRowWriterOperands.gateSlot,
      SourceClauseRowIndexedGate.gateEmbedding,
      SourceClauseRowGate.addressEmbedding]

theorem target_after_echo {q : ℕ} (j : Fin q)
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r a k s t w : ℕ) (saved output count : List Bool) :
    prepared j row n r a k s t w saved output count
      SourceClauseRowWriterQueryEcho.target = row (.inl (j, 1)) := by
  rw [prepared, SourceClauseRowWriterQueryEcho.after,
    SourceClausePreservingBroadcast.target_written]
  · simp [target_blank_after_stage j row n r a k s t w saved output count]
  · simp [SourceClauseRowWriterQueryEcho.temp_ne_target]
  · simp [SourceClauseRowWriterQueryEcho.source_ne_target j]
  · exact SourceClauseRowWriterQueryEcho.source_ne_temp j
  · simp

theorem fixed_after_echo {q : ℕ} (j : Fin q)
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r a k s t w : ℕ) (saved output count : List Bool)
    (i : Fin 8) :
    prepared j row n r a k s t w saved output count
      (SourceClauseRowWriterOperands.gateConstants i) =
      List.replicate (SourceClauseRowWriterOperands.gateSizes a q k s t w i)
        true := by
  have hs : SourceClauseRowWriterOperands.gateConstants i ≠
      SourceClauseRowWriterQueryEcho.source j := by
    rw [SourceClauseRowWriterStageReady.gate_constant_cell]
    have h := SourceClauseRowWriterStageReady.gate_scratch_ne_core
      (SourceClauseRowWriterStageReady.gateConstantLocal i)
      (SourceClauseRowWriterStageReady.gate_constant_scratch i)
      (.inl (.inl (j, 1)) : SourceClauseRowWriterCore.Core q)
    simpa [SourceClauseRowWriterQueryEcho.source] using h
  have ht : SourceClauseRowWriterOperands.gateConstants i ≠
      (SourceClauseRowWriterQueryEcho.temp : SourceClauseRowWriterOperands.Stack q) := by
    fin_cases i <;> simp [SourceClauseRowWriterOperands.gateConstants,
      SourceClauseRowWriterOperands.gateCell,
      SourceClauseRowWriterQueryEcho.temp,
      SourceClauseRowWriterOperands.scratch]
  have hx : SourceClauseRowWriterOperands.gateConstants i ∉
      [SourceClauseRowWriterQueryEcho.target (q := q)] := by
    fin_cases i <;>
      simp [SourceClauseRowWriterOperands.gateConstants,
        SourceClauseRowWriterQueryEcho.target,
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
        SourceClauseGateAffineAddress.addressEmbedding]
  rw [prepared, SourceClauseRowWriterQueryEcho.after,
    SourceClausePreservingBroadcast.other_preserved
      (SourceClauseRowWriterQueryEcho.source j)
      SourceClauseRowWriterQueryEcho.temp
      [SourceClauseRowWriterQueryEcho.target]
      (row (.inl (j, 1)))
      (SourceClauseRowWriterStage.gateFinal n r a k s t w
        (SourceClauseRowWriterBlank.bank row n r saved output count))
      (SourceClauseRowWriterOperands.gateConstants i) hs ht hx]
  exact SourceClauseRowWriterStageReady.gate_fixed_inputs
    row n r a k s t w saved output count i

theorem slot_after_echo {q : ℕ} (j : Fin q)
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r a k s t w : ℕ) (saved output count : List Bool)
    (x : SourceClauseRowSlotAddress.Stack) :
    prepared j row n r a k s t w saved output count
      (SourceClauseRowWriterOperands.gateCell (.inl x)) =
    SourceClauseRowIndexedGate.initial j row n r a k s t w
      saved output count (.inl x) := by
  have hcore : (.inl x : SourceClauseRowWriterCore.Gate q) ∉
      Set.range (SourceClauseRowWriterCore.gateCore (q := q)) := by
    rintro ⟨c, hc⟩
    cases c with
    | inl y =>
        simp [SourceClauseRowWriterCore.gateCore,
          SourceClauseRowWriterCore.gateCoreCell,
          SourceClauseRowGateCleanup.rowCell,
          SourceClauseRowIndexedGate.gateEmbedding] at hc
    | inr y =>
        fin_cases y <;>
          simp [SourceClauseRowWriterCore.gateCore,
            SourceClauseRowWriterCore.gateCoreCell,
            SourceClauseRowGateCleanup.savedCell,
            SourceClauseRowGateCleanup.outputCell,
            SourceClauseRowGateCleanup.countCell,
            SourceClauseRowIndexedGate.gateEmbedding] at hc
  have hs := SourceClauseRowWriterStageReady.gate_scratch_ne_core
    (.inl x : SourceClauseRowWriterCore.Gate q) hcore
    (.inl (.inl (j, 1)) : SourceClauseRowWriterCore.Core q)
  rw [prepared, SourceClauseRowWriterQueryEcho.after,
    SourceClausePreservingBroadcast.other_preserved]
  · exact SourceClauseRowWriterInitial.gate_slot_initial
      j row n r a k s t w saved output count x
  · simpa [SourceClauseRowWriterQueryEcho.source,
      SourceClauseRowWriterOperands.gateCell] using hs
  · simp [SourceClauseRowWriterQueryEcho.temp,
      SourceClauseRowWriterOperands.gateCell,
      SourceClauseRowWriterOperands.scratch]
  · simp [SourceClauseRowWriterQueryEcho.target,
      SourceClauseRowWriterOperands.gateCell,
      SourceClauseRowWriterOperands.gateLiteral,
      SourceClauseRowIndexedGate.gateEmbedding]

theorem other_empty_after_echo {q : ℕ} (j : Fin q)
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r a k s t w : ℕ) (saved output count : List Bool)
    (x : SourceClauseRowWriterCore.Gate q)
    (hcore : x ∉ Set.range (SourceClauseRowWriterCore.gateCore (q := q)))
    (hfixed : ∀ i : Fin 8,
      SourceClauseRowWriterOperands.gateConstants i ≠
        SourceClauseRowWriterOperands.gateCell x)
    (hv : SourceClauseRowWriterOperands.gateCell x ∉
      SourceClauseRowWriterOperands.gateVertexTargets)
    (hr : SourceClauseRowWriterOperands.gateCell x ∉
      SourceClauseRowWriterOperands.gateRowTargets)
    (hghost : x ≠ SourceClauseRowWriterOperands.gateLiteral (.inl 0)) :
    prepared j row n r a k s t w saved output count
      (SourceClauseRowWriterOperands.gateCell x) = [] := by
  have hs := SourceClauseRowWriterStageReady.gate_scratch_ne_core x hcore
    (.inl (.inl (j, 1)) : SourceClauseRowWriterCore.Core q)
  rw [prepared, SourceClauseRowWriterQueryEcho.after,
    SourceClausePreservingBroadcast.other_preserved]
  · exact SourceClauseRowWriterInitial.gate_other_empty
      row n r a k s t w saved output count x hcore hfixed hv hr
  · simpa [SourceClauseRowWriterQueryEcho.source,
      SourceClauseRowWriterOperands.gateCell] using hs
  · simp [SourceClauseRowWriterQueryEcho.temp,
      SourceClauseRowWriterOperands.gateCell,
      SourceClauseRowWriterOperands.scratch]
  · simpa [SourceClauseRowWriterQueryEcho.target,
      SourceClauseRowWriterOperands.gateCell] using hghost

theorem literal_other_after_echo {q : ℕ} (j : Fin q)
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r a k s t w : ℕ) (saved output count : List Bool)
    (x : SourceLabelAddressMachine.Stack)
    (h0 : x ≠ .inl 0) (h1 : x ≠ .inl 1) (h2 : x ≠ .inl 2) :
    prepared j row n r a k s t w saved output count
      (SourceClauseRowWriterOperands.gateCell
        (SourceClauseRowWriterOperands.gateLiteral x)) =
    SourceClauseRowIndexedGate.initial j row n r a k s t w
      saved output count
      (SourceClauseRowWriterOperands.gateLiteral x) := by
  have hzero : SourceClauseRowIndexedGate.initial j row n r a k s t w
      saved output count
      (SourceClauseRowWriterOperands.gateLiteral x) = [] := by
    cases x with
    | inl i =>
        fin_cases i <;>
          simp_all [SourceClauseRowWriterOperands.gateLiteral,
            SourceClauseRowIndexedGate.initial,
            SourceClauseRowIndexedGate.gateEmbedding,
            SourceClauseRowGate.initial,
            SourceClauseRowGate.addressEmbedding,
            SourceClauseRowLiteralAddress.initial,
            SourceLabelAddressMachine.inputs,
            SourceLabelAddressMachine.ambient]
    | inr y =>
        simp [SourceClauseRowWriterOperands.gateLiteral,
          SourceClauseRowIndexedGate.initial,
          SourceClauseRowIndexedGate.gateEmbedding,
          SourceClauseRowGate.initial,
          SourceClauseRowGate.addressEmbedding,
          SourceClauseRowLiteralAddress.initial,
          SourceLabelAddressMachine.inputs,
          SourceLabelAddressMachine.ambient]
  rw [hzero]
  apply other_empty_after_echo
  · rintro ⟨c, hc⟩
    cases c with
    | inl y =>
        simp [SourceClauseRowWriterOperands.gateLiteral,
          SourceClauseRowWriterCore.gateCore,
          SourceClauseRowWriterCore.gateCoreCell,
          SourceClauseRowGateCleanup.rowCell,
          SourceClauseRowIndexedGate.gateEmbedding,
          SourceClauseRowGate.addressEmbedding] at hc
    | inr z =>
        fin_cases z <;>
          simp [SourceClauseRowWriterOperands.gateLiteral,
            SourceClauseRowWriterCore.gateCore,
            SourceClauseRowWriterCore.gateCoreCell,
            SourceClauseRowGateCleanup.savedCell,
            SourceClauseRowGateCleanup.outputCell,
            SourceClauseRowGateCleanup.countCell,
            SourceClauseRowIndexedGate.gateEmbedding,
            SourceClauseRowGate.gateEmbedding,
            SourceClauseRowGate.addressEmbedding] at hc
  · intro i; fin_cases i <;>
      simp_all [SourceClauseRowWriterOperands.gateConstants,
        SourceClauseRowWriterOperands.gateCell,
        SourceClauseRowWriterOperands.gateLiteral,
        SourceClauseRowWriterOperands.gateSlot,
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
      SourceClauseRowWriterOperands.gateLiteral,
      SourceClauseRowWriterOperands.gateSlot,
      SourceClauseRowWriterOperands.gateOffset,
      SourceClauseRowIndexedGate.gateEmbedding,
      SourceClauseRowGate.addressEmbedding,
      SourceClauseRowGate.gateEmbedding,
      SourceClauseGateSlotAddress.offsetEmbedding]
  · simp [SourceClauseRowWriterOperands.gateRowTargets,
      SourceClauseRowWriterOperands.gateCell,
      SourceClauseRowWriterOperands.gateLiteral,
      SourceClauseRowWriterOperands.gateSlot,
      SourceClauseRowIndexedGate.gateEmbedding,
      SourceClauseRowGate.addressEmbedding]
  · simpa [SourceClauseRowWriterOperands.gateLiteral,
      SourceClauseRowIndexedGate.gateEmbedding,
      SourceClauseRowGate.addressEmbedding] using h0

theorem literal_input_after_echo {q : ℕ} (j : Fin q)
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r a k s t w : ℕ) (saved output count : List Bool)
    (h : row (.inl (j, 1)) =
      List.replicate (row (.inl (j, 1))).length true)
    (x : SourceLabelAddressMachine.Stack) :
    prepared j row n r a k s t w saved output count
      (SourceClauseRowWriterOperands.gateCell
        (SourceClauseRowWriterOperands.gateLiteral x)) =
    SourceClauseRowIndexedGate.initial j row n r a k s t w
      saved output count
      (SourceClauseRowWriterOperands.gateLiteral x) := by
  cases x with
  | inl i =>
      fin_cases i
      · simpa [SourceClauseRowWriterQueryEcho.target,
          SourceClauseRowWriterOperands.gateLiteral,
          SourceClauseRowIndexedGate.initial,
          SourceClauseRowGate.initial,
          SourceClauseRowLiteralAddress.initial,
          SourceLabelAddressMachine.inputs,
          SourceLabelAddressMachine.ambient] using
          (SourceClauseRowWriterStageEcho.target_after_echo
            j row n r a k s t w saved output count).trans h
      · simpa [SourceClauseRowWriterStageReady.gateConstantLocal,
          SourceClauseRowWriterOperands.gateLiteral,
          SourceClauseRowWriterOperands.gateSizes,
          SourceClauseRowIndexedGate.initial,
          SourceClauseRowGate.initial,
          SourceClauseRowLiteralAddress.initial,
          SourceLabelAddressMachine.inputs,
          SourceLabelAddressMachine.ambient] using
          fixed_after_echo j row n r a k s t w saved output count 3
      · simpa [SourceClauseRowWriterStageReady.gateConstantLocal,
          SourceClauseRowWriterOperands.gateLiteral,
          SourceClauseRowWriterOperands.gateSizes,
          SourceClauseRowIndexedGate.initial,
          SourceClauseRowGate.initial,
          SourceClauseRowLiteralAddress.initial,
          SourceLabelAddressMachine.inputs,
          SourceLabelAddressMachine.ambient] using
          fixed_after_echo j row n r a k s t w saved output count 4
      · exact literal_other_after_echo j row n r a k s t w
          saved output count (.inl 3) (by decide) (by decide) (by decide)
      · exact literal_other_after_echo j row n r a k s t w
          saved output count (.inl 4) (by decide) (by decide) (by decide)
  | inr y =>
      exact literal_other_after_echo j row n r a k s t w
        saved output count (.inr y) (by simp) (by simp) (by simp)

theorem core_after_echo {q : ℕ} (j : Fin q)
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r a k s t w : ℕ) (saved output count : List Bool)
    (c : SourceClauseRowWriterCore.Core q) :
    prepared j row n r a k s t w saved output count
      (SourceClauseRowWriterOperands.gateCell
        (SourceClauseRowWriterCore.gateCore c)) =
    SourceClauseRowIndexedGate.initial j row n r a k s t w
      saved output count (SourceClauseRowWriterCore.gateCore c) := by
  by_cases hc : c = (.inl (.inl (j, 1)) : SourceClauseRowWriterCore.Core q)
  · subst c
    rw [SourceClauseRowWriterOperands.gateCell,
      SourceClauseRowWriterCore.gate_cell]
    simpa [prepared, SourceClauseRowWriterQueryEcho.source,
      SourceClauseRowIndexedGate.initial,
      SourceClauseRowIndexedGate.gateEmbedding,
      SourceClauseRowWriterCore.gateCore,
      SourceClauseRowWriterCore.gateCoreCell,
      SourceClauseRowGateCleanup.rowCell,
      SourceClauseRowGate.initial,
      SourceClauseRowLiteralAddress.initial] using
      SourceClauseRowWriterQueryEcho.source_restored j
        (row (.inl (j, 1)))
        (SourceClauseRowWriterStage.gateFinal n r a k s t w
          (SourceClauseRowWriterBlank.bank row n r saved output count))
  · have hs : SourceClauseRowWriterOperands.gateCell
        (SourceClauseRowWriterCore.gateCore c) ≠
        SourceClauseRowWriterQueryEcho.source j := by
      intro he
      apply hc
      have hq : SourceClauseRowWriterQueryEcho.source j =
          SourceClauseRowWriterOperands.gateCell
            (SourceClauseRowWriterCore.gateCore
              (.inl (.inl (j, 1)) : SourceClauseRowWriterCore.Core q)) := by
        simp [SourceClauseRowWriterQueryEcho.source,
          SourceClauseRowWriterOperands.gateCell,
          SourceClauseRowWriterCore.gate_cell]
      rw [hq] at he
      exact SourceClauseRowWriterCore.gateCore.injective
        (SourceClauseRowWriterCore.gateEmbedding.injective (Sum.inl.inj he))
    have ht : SourceClauseRowWriterOperands.gateCell
        (SourceClauseRowWriterCore.gateCore c) ≠
        SourceClauseRowWriterQueryEcho.temp := by
      simp [SourceClauseRowWriterQueryEcho.temp,
        SourceClauseRowWriterOperands.gateCell,
        SourceClauseRowWriterOperands.scratch]
    have hx : SourceClauseRowWriterOperands.gateCell
        (SourceClauseRowWriterCore.gateCore c) ∉
        [SourceClauseRowWriterQueryEcho.target] := by
      simp only [List.mem_singleton]
      have hne := SourceClauseRowWriterStageReady.gate_scratch_ne_core
        (SourceClauseRowWriterOperands.gateLiteral (.inl 0))
        SourceClauseRowWriterQueryEcho.target_local_not_core c
      simpa only [SourceClauseRowWriterQueryEcho.target,
        SourceClauseRowWriterOperands.gateCell,
        SourceClauseRowWriterCore.gate_cell] using hne.symm
    rw [prepared, SourceClauseRowWriterQueryEcho.after,
      SourceClausePreservingBroadcast.other_preserved
        (SourceClauseRowWriterQueryEcho.source j)
        SourceClauseRowWriterQueryEcho.temp
        [SourceClauseRowWriterQueryEcho.target]
        (row (.inl (j, 1)))
        (SourceClauseRowWriterStage.gateFinal n r a k s t w
          (SourceClauseRowWriterBlank.bank row n r saved output count))
        (SourceClauseRowWriterOperands.gateCell
          (SourceClauseRowWriterCore.gateCore c)) hs ht hx]
    exact SourceClauseRowWriterInitial.gate_core_initial
      j row n r a k s t w saved output count c

theorem run {q : ℕ} (j : Fin q)
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r a k s t w : ℕ) (saved output count : List Bool)
    (h : row (.inl (j, 1)) =
      List.replicate (row (.inl (j, 1))).length true) :
    ∃ T ≤ (((2 * n + 3) + (2 * r + 3) + 1) +
      (SourceClauseFixedBatch.costPrefix
        (SourceClauseRowWriterOperands.gateSizes a q k s t w) 8 + 1) + 1) +
      (2 * (row (.inl (j, 1))).length + 3) + 1,
      ((advance (program j a k s t w))^[T])
        (⟨some (BitMachineRawSequence.leftLabel
          (BitMachineRawSequence.leftLabel
            (BitMachineRawSequence.leftLabel
              SourceClausePreservingBroadcast.Label.scan))),
          ((((((), none), ((), none)), ()), ((), none))),
          SourceClauseRowWriterBlank.bank row n r saved output count⟩) =
        ⟨none, ((((((), none), ((), none)), ()), ((), none))),
          prepared j row n r a k s t w saved output count⟩ := by
  obtain ⟨ts, hts, hs⟩ := SourceClauseRowWriterStage.gate_run
    n r a k s t w (SourceClauseRowWriterBlank.bank row n r saved output count)
    (SourceClauseRowWriterBlank.vertex row n r saved output count)
    (SourceClauseRowWriterBlank.row_index row n r saved output count)
    (SourceClauseRowWriterBlank.scratch row n r saved output count)
  have he := SourceClauseRowWriterQueryEcho.run j
    (row (.inl (j, 1)))
    (SourceClauseRowWriterStage.gateFinal n r a k s t w
      (SourceClauseRowWriterBlank.bank row n r saved output count))
    (source_after_stage j row n r a k s t w saved output count)
    (scratch_after_stage row n r a k s t w saved output count)
  obtain ⟨T, hT, hrun⟩ := BitMachineRawSequence.runs
    (SourceClauseRowWriterStage.gateProgram (q := q) a k s t w)
    (SourceClauseRowWriterQueryEcho.program j)
    (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel
        SourceClausePreservingBroadcast.Label.scan))
    SourceClausePreservingBroadcast.Label.scan
    ((((), none), ((), none)), ()) ((((), none), ((), none)), ())
    ((), none) ((), none)
    (SourceClauseRowWriterBlank.bank row n r saved output count)
    (SourceClauseRowWriterStage.gateFinal n r a k s t w
      (SourceClauseRowWriterBlank.bank row n r saved output count))
    (prepared j row n r a k s t w saved output count)
    ts (2 * (row (.inl (j, 1))).length + 3) hs he
  exact ⟨T, by omega, hrun⟩

end EthInapproximability.CurrentPaper.SourceClauseRowWriterStageEcho
