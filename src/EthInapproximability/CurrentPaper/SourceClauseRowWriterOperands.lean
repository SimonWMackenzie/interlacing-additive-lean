import EthInapproximability.CurrentPaper.SourceClauseRowWriterRuns
import EthInapproximability.CurrentPaper.SourceClauseFixedBatch
import EthInapproximability.CurrentPaper.SourceClausePreservingBroadcast

/-!
# Arithmetic inputs of the shared source-row clause writers

The varying unary vertex count and row ordinal live outside the writer bank.
Fixed tuple/position values are enumerated in finite control. This module
names the actual scratch destinations of both existing physical writers.
-/

namespace EthInapproximability.CurrentPaper.SourceClauseRowWriterOperands

open Turing BitMachineEncoding
open scoped Classical

noncomputable abbrev Stack (q : ℕ) :=
  SourceClauseRowWriterCore.Stack q ⊕ Fin 3

def vertex {q : ℕ} : Stack q := .inr 0
def rowIndex {q : ℕ} : Stack q := .inr 1
def scratch {q : ℕ} : Stack q := .inr 2

noncomputable def gateCell {q : ℕ} (x : SourceClauseRowWriterCore.Gate q) :
    Stack q := .inl (SourceClauseRowWriterCore.gateEmbedding x)
noncomputable def unitCell {q : ℕ} (x : SourceClauseRowWriterCore.UnitBank q) :
    Stack q := .inl (SourceClauseRowWriterCore.unitEmbedding x)

def gateSlot {q : ℕ} (x : SourceClauseRowSlotAddress.Stack) :
    SourceClauseRowWriterCore.Gate q := .inl x
def gateLiteral {q : ℕ} (x : SourceLabelAddressMachine.Stack) :
    SourceClauseRowWriterCore.Gate q :=
  SourceClauseRowIndexedGate.gateEmbedding
    (SourceClauseRowGate.addressEmbedding (.inr x))
def gateOffset {q : ℕ} (x : Fin 6) : SourceClauseRowWriterCore.Gate q :=
  SourceClauseRowIndexedGate.gateEmbedding
    (SourceClauseRowGate.gateEmbedding
      (SourceClauseGateSlotAddress.offsetEmbedding x))
def gateAffine {q : ℕ} (x : SourceLabelAddressMachine.Stack) :
    SourceClauseRowWriterCore.Gate q :=
  SourceClauseRowIndexedGate.gateEmbedding
    (SourceClauseRowGate.gateEmbedding
      (SourceClauseGateSlotAddress.gateEmbedding
        (SourceClauseGateAffineAddress.addressEmbedding x)))

def unitAddress {q : ℕ} (x : SourceClauseRowUnitAddress.Stack) :
    SourceClauseRowWriterCore.UnitBank q :=
  .inr (SourceClauseRowUnitMachine.addressEmbedding x)

noncomputable def gateConstants {q : ℕ} : Fin 8 → Stack q :=
  ![gateCell (gateSlot (.inl 1)),
    gateCell (gateSlot (.inr (.inl 1))),
    gateCell (gateSlot (.inr (.inl 2))),
    gateCell (gateLiteral (.inl 1)),
    gateCell (gateLiteral (.inl 2)),
    gateCell (gateOffset 1),
    gateCell (gateOffset 2),
    gateCell (gateAffine (.inl 1))]

def gateSizes (a q k s t w : ℕ) : Fin 8 → ℕ :=
  ![1 + a * a, a ^ q, k, a, s, a, t, w]

noncomputable def unitConstants {q : ℕ} : Fin 6 → Stack q :=
  ![unitCell (unitAddress (SourceClauseRowUnitAddress.slotEmbedding (.inl 1))),
    unitCell (unitAddress (SourceClauseRowUnitAddress.slotEmbedding (.inr (.inl 1)))),
    unitCell (unitAddress (SourceClauseRowUnitAddress.slotEmbedding (.inr (.inl 2)))),
    unitCell (unitAddress (SourceClauseRowUnitAddress.offsetEmbedding 1)),
    unitCell (unitAddress (SourceClauseRowUnitAddress.offsetEmbedding 2)),
    unitCell (unitAddress (SourceClauseRowUnitAddress.labelEmbedding (.inl 1)))]

def unitSizes (a q k w ell : ℕ) : Fin 6 → ℕ :=
  ![1 + a * a, a ^ q, k, a, ell, w]

noncomputable def gateVertexTargets {q : ℕ} : List (Stack q) :=
  [gateCell (gateSlot (.inl 0)), gateCell (gateOffset 0)]
noncomputable def gateRowTargets {q : ℕ} : List (Stack q) :=
  [gateCell (gateSlot (.inr (.inl 0)))]
noncomputable def unitVertexTargets {q : ℕ} : List (Stack q) :=
  [unitCell (unitAddress (SourceClauseRowUnitAddress.slotEmbedding (.inl 0))),
    unitCell (unitAddress (SourceClauseRowUnitAddress.offsetEmbedding 0))]
noncomputable def unitRowTargets {q : ℕ} : List (Stack q) :=
  [unitCell (unitAddress
    (SourceClauseRowUnitAddress.slotEmbedding (.inr (.inl 0))))]

theorem gateConstants_injective {q : ℕ} :
    Function.Injective (gateConstants (q := q)) := by
  intro i j h
  fin_cases i <;> fin_cases j <;>
    simp_all [gateConstants, gateCell, gateSlot, gateLiteral,
      gateOffset, gateAffine, SourceClauseRowWriterCore.gateEmbedding,
      SourceClauseRowWriterCore.gateCoreCell,
      SourceClauseRowGateCleanup.keep,
      SourceClauseRowIndexedGate.gateEmbedding,
      SourceClauseRowGate.addressEmbedding,
      SourceClauseRowGate.gateEmbedding,
      SourceClauseGateSlotAddress.offsetEmbedding,
      SourceClauseGateSlotAddress.gateEmbedding,
      SourceClauseGateAffineAddress.addressEmbedding]

theorem unitConstants_injective {q : ℕ} :
    Function.Injective (unitConstants (q := q)) := by
  intro i j h
  fin_cases i <;> fin_cases j <;>
    simp_all [unitConstants, unitCell, unitAddress,
      SourceClauseRowWriterCore.unitEmbedding,
      SourceClauseRowUnitAddress.slotEmbedding,
      SourceClauseRowUnitAddress.offsetEmbedding,
      SourceClauseRowUnitAddress.labelEmbedding]

noncomputable def gateFixedBank {q : ℕ} (a k s t w : ℕ)
    (S : Stack q → List Bool) : Stack q → List Bool :=
  SourceClauseFixedBatch.bankPrefix gateConstants (gateSizes a q k s t w) S 8

noncomputable def unitFixedBank {q : ℕ} (a k w ell : ℕ)
    (S : Stack q → List Bool) : Stack q → List Bool :=
  SourceClauseFixedBatch.bankPrefix unitConstants (unitSizes a q k w ell) S 6

theorem gate_fixed_run {q : ℕ} (a k s t w : ℕ)
    (S : Stack q → List Bool) :
    ((advance (SourceClauseFixedBatch.program gateConstants
      (gateSizes a q k s t w)))^[
        SourceClauseFixedBatch.costPrefix (gateSizes a q k s t w) 8 + 1])
      (⟨some (SourceClauseFixedBatch.labelAt
        (gateSizes a q k s t w) 0), (), S⟩) =
      ⟨none, (), gateFixedBank a k s t w S⟩ := by
  exact SourceClauseFixedBatch.run gateConstants (gateSizes a q k s t w) S

theorem unit_fixed_run {q : ℕ} (a k w ell : ℕ)
    (S : Stack q → List Bool) :
    ((advance (SourceClauseFixedBatch.program unitConstants
      (unitSizes a q k w ell)))^[
        SourceClauseFixedBatch.costPrefix (unitSizes a q k w ell) 6 + 1])
      (⟨some (SourceClauseFixedBatch.labelAt
        (unitSizes a q k w ell) 0), (), S⟩) =
      ⟨none, (), unitFixedBank a k w ell S⟩ := by
  exact SourceClauseFixedBatch.run unitConstants (unitSizes a q k w ell) S

theorem gate_fixed_word {q : ℕ} (a k s t w : ℕ)
    (S : Stack q → List Bool) (i : Fin 8) :
    gateFixedBank a k s t w S (gateConstants i) =
      List.replicate (gateSizes a q k s t w i) true ++ S (gateConstants i) := by
  exact SourceClauseFixedBatch.result_target gateConstants
    (gateSizes a q k s t w) S gateConstants_injective i

theorem unit_fixed_word {q : ℕ} (a k w ell : ℕ)
    (S : Stack q → List Bool) (i : Fin 6) :
    unitFixedBank a k w ell S (unitConstants i) =
      List.replicate (unitSizes a q k w ell i) true ++ S (unitConstants i) := by
  exact SourceClauseFixedBatch.result_target unitConstants
    (unitSizes a q k w ell) S unitConstants_injective i

end EthInapproximability.CurrentPaper.SourceClauseRowWriterOperands
