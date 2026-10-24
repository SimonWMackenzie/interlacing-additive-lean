import EthInapproximability.CurrentPaper.SourceClausePrefixSharedGateN
import EthInapproximability.CurrentPaper.SourceClauseFixedBatch
import EthInapproximability.CurrentPaper.SourceClausePreservingBroadcast

/-!
Physical preparers for one prefix OR gate on the shared unit/gate carrier.
Fixed unary operands are pushed from finite control. The varying vertex
ordinal is copied from the shared core, preserving its source. The final
ready-bank equality is a separate obligation.
-/

namespace EthInapproximability.CurrentPaper.SourceBooleanPrefix.PrefixGateOperands

open Turing BitMachineEncoding
open scoped Classical
noncomputable section

abbrev Stack := PrefixSharedCore.Stack
noncomputable instance : DecidableEq Stack := Classical.decEq _

def gateCell (x : PrefixSharedCore.Gate) : Stack :=
  PrefixSharedCore.gateEmbedding x

def vertex : Stack := .inl 1
def temp : Stack := gateCell (SourceClauseRowGate.temp (q := 1))

def literalIndex : Stack :=
  gateCell (SourceClauseRowGate.addressEmbedding
    (.inr (.inl 0)))
def literalLocal : PrefixSharedCore.Gate :=
  SourceClauseRowGate.addressEmbedding (.inr (.inl 0))
def literalAlphabet : Stack :=
  gateCell (SourceClauseRowGate.addressEmbedding
    (.inr (.inl 1)))
def literalOffset : Stack :=
  gateCell (SourceClauseRowGate.addressEmbedding
    (.inr (.inl 2)))

def gateAlphabet : Stack :=
  gateCell (SourceClauseRowGate.gateEmbedding (.inl 1))
def gateOffset : Stack :=
  gateCell (SourceClauseRowGate.gateEmbedding (.inl 2))
def gateIndex : Stack :=
  gateCell (SourceClauseRowGate.gateEmbedding
    (SourceClauseGateSlotAddress.gateEmbedding
      (SourceClauseGateAffineAddress.addressEmbedding (.inl 0))))
def gateWidth : Stack :=
  gateCell (SourceClauseRowGate.gateEmbedding
    (SourceClauseGateSlotAddress.gateEmbedding
      (SourceClauseGateAffineAddress.addressEmbedding (.inl 1))))

def constantTarget : Fin 5 → Stack
  | 0 => literalAlphabet
  | 1 => literalOffset
  | 2 => gateAlphabet
  | 3 => gateOffset
  | 4 => gateWidth

def constantLocal : Fin 5 → PrefixSharedCore.Gate
  | 0 => SourceClauseRowGate.addressEmbedding (.inr (.inl 1))
  | 1 => SourceClauseRowGate.addressEmbedding (.inr (.inl 2))
  | 2 => SourceClauseRowGate.gateEmbedding (.inl 1)
  | 3 => SourceClauseRowGate.gateEmbedding (.inl 2)
  | 4 => SourceClauseRowGate.gateEmbedding
      (SourceClauseGateSlotAddress.gateEmbedding
        (SourceClauseGateAffineAddress.addressEmbedding (.inl 1)))

theorem constantTarget_eq (i : Fin 5) :
    constantTarget i = gateCell (constantLocal i) := by
  fin_cases i <;> rfl

def constantSize (s w : ℕ) : Fin 5 → ℕ
  | 0 => 2
  | 1 => s
  | 2 => 2
  | 3 => s
  | 4 => w

theorem constantTarget_injective : Function.Injective constantTarget := by
  intro i j h
  fin_cases i <;> fin_cases j <;>
    simp [constantTarget, literalAlphabet, literalOffset,
      gateAlphabet, gateOffset, gateWidth, gateCell,
      PrefixSharedCore.gateEmbedding,
      SourceClauseRowGate.addressEmbedding,
      SourceClauseRowGate.gateEmbedding,
      SourceClauseGateSlotAddress.gateEmbedding,
      SourceClauseGateAffineAddress.addressEmbedding] at h ⊢

noncomputable def fixed (s w : ℕ) (S : Stack → List Bool) :
    Stack → List Bool :=
  SourceClauseFixedBatch.bankPrefix constantTarget (constantSize s w) S 5

theorem fixed_run (s w : ℕ) (S : Stack → List Bool) :
    ((advance (SourceClauseFixedBatch.program constantTarget
      (constantSize s w)))^[SourceClauseFixedBatch.costPrefix
        (constantSize s w) 5 + 1])
      (⟨some (SourceClauseFixedBatch.labelAt (constantSize s w) 0), (), S⟩) =
      ⟨none, (), fixed s w S⟩ := by
  exact SourceClauseFixedBatch.run constantTarget (constantSize s w) S

def vertexTargets : List Stack := [literalIndex, gateIndex]

theorem literalIndex_not_core :
    literalLocal ∉
      Set.range PrefixSharedCore.gateCore := by
  rintro ⟨i, hi⟩
  fin_cases i <;>
    simp [literalLocal, PrefixSharedCore.gateCore,
      PrefixSharedCore.gateCoreCell,
      PrefixSharedCore.gateN, PrefixSharedCore.gateVertex,
      PrefixGateClean.savedCell, PrefixGateClean.outputCell,
      PrefixGateClean.countCell,
      SourceClauseRowGate.addressEmbedding,
      SourceClauseRowGate.gateEmbedding,
      gateSavedKey, gateCountKey] at hi

def gateIndexLocal : PrefixSharedCore.Gate :=
  SourceClauseRowGate.gateEmbedding
    (SourceClauseGateSlotAddress.gateEmbedding
      (SourceClauseGateAffineAddress.addressEmbedding (.inl 0)))

def tempLocal : PrefixSharedCore.Gate := SourceClauseRowGate.temp

theorem gateIndex_not_core : gateIndexLocal ∉
    Set.range PrefixSharedCore.gateCore := by
  rintro ⟨i, hi⟩
  fin_cases i <;>
    simp [gateIndexLocal, PrefixSharedCore.gateCore,
      PrefixSharedCore.gateCoreCell, PrefixSharedCore.gateN,
      PrefixSharedCore.gateVertex, PrefixGateClean.savedCell,
      PrefixGateClean.outputCell, PrefixGateClean.countCell,
      gateSavedKey, gateCountKey,
      SourceClauseRowGate.gateEmbedding,
      SourceClauseGateSlotAddress.gateEmbedding,
      SourceClauseGateAffineAddress.addressEmbedding,
      SourceClauseGateAffineAddress.gateEmbedding,
      SourceClauseGateTwoAddress.embedding,
      SourceClauseGateMachine.embedding] at hi

theorem temp_not_core : tempLocal ∉
    Set.range PrefixSharedCore.gateCore := by
  rintro ⟨i, hi⟩
  fin_cases i <;>
    simp [tempLocal, SourceClauseRowGate.temp,
      PrefixSharedCore.gateCore, PrefixSharedCore.gateCoreCell,
      PrefixSharedCore.gateN, PrefixSharedCore.gateVertex,
      PrefixGateClean.savedCell, PrefixGateClean.outputCell,
      PrefixGateClean.countCell, gateSavedKey, gateCountKey,
      SourceClauseRowGate.gateEmbedding] at hi

theorem source_ne (x : PrefixSharedCore.Gate)
    (hx : x ∉ Set.range PrefixSharedCore.gateCore) :
    vertex ≠ gateCell x := by
  rw [gateCell, PrefixSharedCore.gateEmbedding,
    SourceClauseSharedCore.left_outside PrefixSharedCore.gateCore
      PrefixSharedCore.unitCore x hx]
  simp [vertex]

theorem constant_not_core (i : Fin 5) :
    constantLocal i ∉ Set.range PrefixSharedCore.gateCore := by
  rintro ⟨c, hc⟩
  fin_cases i <;> fin_cases c <;>
    simp [constantLocal, PrefixSharedCore.gateCore,
      PrefixSharedCore.gateCoreCell,
      PrefixSharedCore.gateN, PrefixSharedCore.gateVertex,
      PrefixGateClean.savedCell, PrefixGateClean.outputCell,
      PrefixGateClean.countCell, gateSavedKey, gateCountKey,
      SourceClauseRowGate.addressEmbedding,
      SourceClauseRowGate.gateEmbedding,
      SourceClauseGateSlotAddress.gateEmbedding,
      SourceClauseGateAffineAddress.addressEmbedding,
      SourceClauseGateAffineAddress.gateEmbedding,
      SourceClauseGateTwoAddress.embedding,
      SourceClauseGateMachine.embedding] at hc

theorem fixed_vertex (s w : ℕ) (S : Stack → List Bool) :
    fixed s w S vertex = S vertex := by
  apply SourceClauseFixedBatch.result_outside
  intro i
  rw [constantTarget_eq]
  exact Ne.symm (source_ne _ (constant_not_core i))

theorem fixed_temp (s w : ℕ) (S : Stack → List Bool) :
    fixed s w S temp = S temp := by
  apply SourceClauseFixedBatch.result_outside
  intro i
  rw [constantTarget_eq]
  intro h
  have hh := PrefixSharedCore.gateEmbedding.injective h.symm
  fin_cases i <;>
    simp [constantLocal, SourceClauseRowGate.temp,
      SourceClauseRowGate.addressEmbedding,
      SourceClauseRowGate.gateEmbedding] at hh

theorem literal_ne_gate : literalIndex ≠ gateIndex := by
  intro h
  have hh := PrefixSharedCore.gateEmbedding.injective h
  simp [SourceClauseRowGate.addressEmbedding,
    SourceClauseRowGate.gateEmbedding] at hh

theorem temp_ne_literal : temp ≠ literalIndex := by
  intro h
  have hh := PrefixSharedCore.gateEmbedding.injective h
  simp [SourceClauseRowGate.temp,
    SourceClauseRowGate.addressEmbedding] at hh

theorem temp_ne_gate : temp ≠ gateIndex := by
  intro h
  have hh := PrefixSharedCore.gateEmbedding.injective h
  simp [SourceClauseRowGate.temp,
    SourceClauseRowGate.gateEmbedding] at hh

noncomputable def copied (bits : List Bool) (S : Stack → List Bool) :
    Stack → List Bool :=
  SourceClausePreservingBroadcast.result vertex temp vertexTargets bits S

theorem vertex_copy_run (bits : List Bool) (S : Stack → List Bool)
    (hvertex : S vertex = bits) (htemp : S temp = []) :
    ((advance (SourceClausePreservingBroadcast.program
      vertex temp vertexTargets))^[2 * bits.length + 3])
      (⟨some SourceClausePreservingBroadcast.Label.scan, ((), none), S⟩) =
      ⟨none, ((), none), copied bits S⟩ := by
  apply SourceClausePreservingBroadcast.run_halt vertex temp vertexTargets
  · exact source_ne tempLocal temp_not_core
  · simpa [vertexTargets] using literal_ne_gate
  · simpa [vertexTargets] using
      (show vertex ≠ literalIndex ∧ vertex ≠ gateIndex from
        ⟨source_ne literalLocal literalIndex_not_core,
          source_ne gateIndexLocal gateIndex_not_core⟩)
  · simpa [vertexTargets] using
      (show temp ≠ literalIndex ∧ temp ≠ gateIndex from
        ⟨temp_ne_literal, temp_ne_gate⟩)
  · exact hvertex
  · exact htemp

def preparationProgram (s w : ℕ) :=
  BitMachineRawSequence.program
    (SourceClauseFixedBatch.program constantTarget (constantSize s w))
    (SourceClausePreservingBroadcast.program vertex temp vertexTargets)
    SourceClausePreservingBroadcast.Label.scan () ((), none)

def preparationCost (s w : ℕ) (bits : List Bool) : ℕ :=
  SourceClauseFixedBatch.costPrefix (constantSize s w) 5 + 1 +
    (2 * bits.length + 3) + 1

theorem preparation_run (s w : ℕ) (bits : List Bool)
    (S : Stack → List Bool) (hvertex : S vertex = bits)
    (htemp : S temp = []) :
    ∃ T ≤ preparationCost s w bits,
      ((advance (preparationProgram s w))^[T])
        (⟨some (BitMachineRawSequence.leftLabel
          (SourceClauseFixedBatch.labelAt (constantSize s w) 0)),
          ((), ((), none)), S⟩) =
        ⟨none, ((), ((), none)), copied bits (fixed s w S)⟩ := by
  have hf := fixed_run s w S
  have hc := vertex_copy_run bits (fixed s w S)
    (by rw [fixed_vertex, hvertex])
    (by rw [fixed_temp, htemp])
  obtain ⟨T, hT, hr⟩ := BitMachineRawSequence.runs
    (SourceClauseFixedBatch.program constantTarget (constantSize s w))
    (SourceClausePreservingBroadcast.program vertex temp vertexTargets)
    (SourceClauseFixedBatch.labelAt (constantSize s w) 0)
    SourceClausePreservingBroadcast.Label.scan
    () () ((), none) ((), none)
    S (fixed s w S) (copied bits (fixed s w S))
    (SourceClauseFixedBatch.costPrefix (constantSize s w) 5 + 1)
    (2 * bits.length + 3) hf hc
  exact ⟨T, by dsimp [preparationCost]; omega,
    by simpa only [preparationProgram] using hr⟩

end
end EthInapproximability.CurrentPaper.SourceBooleanPrefix.PrefixGateOperands
