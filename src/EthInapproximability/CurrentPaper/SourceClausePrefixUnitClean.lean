import EthInapproximability.CurrentPaper.SourceClausePrefixUnitRun
import EthInapproximability.CurrentPaper.SourceClauseClearExcept
import EthInapproximability.CurrentPaper.SourceClauseFixedBatch

/-!
Physically clear the prefix-unit writer scratch while retaining its varying
unary inputs and the three persistent output cells. Fixed constants still
require a charged restaging step before the next unit call.
-/

namespace EthInapproximability.CurrentPaper.SourceBooleanPrefix.PrefixUnitClean

open Turing BitMachineEncoding BitMachineStackEmbedding
open scoped Classical

abbrev Stack := PrefixUnitRun.Stack
noncomputable instance : Fintype Stack := Fintype.ofFinite _

def vertexCount : Stack := .inl (.inl 0)
def ordinal : Stack :=
  .inl (SourceClauseGateSlotAddress.gateEmbedding
    (SourceClauseGateAffineAddress.addressEmbedding (.inl 0)))
def saved : Stack := PrefixUnitRun.savedKey
def output : Stack := PrefixUnitRun.outputKey
def count : Stack := PrefixUnitRun.countKey

noncomputable def keep : Finset Stack :=
  {vertexCount, ordinal, saved, output, count}

noncomputable def clean (S : Stack → List Bool) : Stack → List Bool :=
  SourceClauseClearExcept.result keep S

theorem saved_mem : saved ∈ keep := by simp [keep]
theorem output_mem : output ∈ keep := by simp [keep]
theorem count_mem : count ∈ keep := by simp [keep]
theorem vertexCount_mem : vertexCount ∈ keep := by simp [keep]
theorem ordinal_mem : ordinal ∈ keep := by simp [keep]

noncomputable def cost (S : Stack → List Bool) : ℕ :=
  (∑ i : Fin (SourceClauseClearExcept.workCount keep),
    (S (SourceClauseClearExcept.workBank keep i)).length) +
    SourceClauseClearExcept.workCount keep + 2

theorem run (S : Stack → List Bool) :
    ((advance (SourceClauseClearExcept.program keep))^[cost S])
      (⟨some (.clear 0), ((), none), S⟩) =
      ⟨none, ((), none), clean S⟩ := by
  exact SourceClauseClearExcept.run keep S

theorem final_saved (n ordinalValue w ell : ℕ) (sign : Bool)
    (savedBits outputBits countBits : List Bool) :
    clean (PrefixUnitRun.finished n ordinalValue w ell sign
      savedBits outputBits countBits) saved =
      (EncodedCNF.encodeClause (SourceClauseUnitMachine.unitClause
        (ordinalValue * w + (2 * n + ell)) sign)).reverse ++ savedBits := by
  simpa only [clean, SourceClauseClearExcept.result, saved_mem,
    ite_true, saved] using
    PrefixUnitRun.final_saved n ordinalValue w ell sign
      savedBits outputBits countBits

theorem final_count (n ordinalValue w ell : ℕ) (sign : Bool)
    (savedBits outputBits countBits : List Bool) :
    clean (PrefixUnitRun.finished n ordinalValue w ell sign
      savedBits outputBits countBits) count = true :: countBits := by
  simpa only [clean, SourceClauseClearExcept.result, count_mem,
    ite_true, count] using
    PrefixUnitRun.final_count n ordinalValue w ell sign
      savedBits outputBits countBits

theorem initial_vertexCount (n ordinalValue w ell : ℕ)
    (savedBits outputBits countBits : List Bool) :
    PrefixUnitRun.initial n ordinalValue w ell
      savedBits outputBits countBits vertexCount =
      List.replicate n true := by
  rfl

theorem initial_ordinal (n ordinalValue w ell : ℕ)
    (savedBits outputBits countBits : List Bool) :
    PrefixUnitRun.initial n ordinalValue w ell
      savedBits outputBits countBits ordinal =
      List.replicate ordinalValue true := by
  rfl

theorem final_vertexCount (n ordinalValue w ell : ℕ) (sign : Bool)
    (savedBits outputBits countBits : List Bool) :
    PrefixUnitRun.finished n ordinalValue w ell sign
      savedBits outputBits countBits vertexCount =
      List.replicate n true := by
  rw [PrefixUnitRun.finished, bank_outside]
  · simp [PrefixUnitRun.copied, BitMachineBroadcast.copied,
      PrefixUnitRun.source, PrefixUnitRun.temp,
      PrefixUnitRun.targets, PrefixUnitRun.target,
      PrefixUnitRun.addressed, PrefixUnitAddress.finalBank,
      PrefixUnitAddress.transferred,
      SourceClauseGateSlotAddress.transferred,
      SourceClauseGateSlotAddress.offsetDone,
      PrefixUnitAddress.binarySource,
      SourceClauseGateSlotAddress.gateEmbedding,
      SourceClauseGateSlotAddress.temp,
      vertexCount]
    rw [bank_outside]
    · simp [BitMachineBroadcast.copied,
        SourceClauseGateSlotAddress.offsetSource,
        SourceClauseGateSlotAddress.affineOffset,
        SourceClauseGateSlotAddress.targets,
        SourceClauseGateSlotAddress.offsetOutput,
        MatrixAddressMachine.cfg]
    · intro ⟨x, h⟩; cases h
  · intro ⟨x, h⟩; cases h

theorem final_ordinal (n ordinalValue w ell : ℕ) (sign : Bool)
    (savedBits outputBits countBits : List Bool) :
    PrefixUnitRun.finished n ordinalValue w ell sign
      savedBits outputBits countBits ordinal =
      List.replicate ordinalValue true := by
  rw [PrefixUnitRun.finished, bank_outside]
  · simp [PrefixUnitRun.copied, BitMachineBroadcast.copied,
      PrefixUnitRun.source, PrefixUnitRun.temp,
      PrefixUnitRun.targets, PrefixUnitRun.target,
      PrefixUnitRun.addressed, PrefixUnitAddress.finalBank,
      PrefixUnitAddress.transferred,
      SourceClauseGateSlotAddress.transferred,
      SourceClauseGateSlotAddress.offsetDone,
      SourceClauseGateAffineAddress.addressed,
      SourceLabelAddressMachine.outputs,
      SourceLabelAddressMachine.ambient,
      PrefixUnitAddress.binarySource,
      SourceClauseGateSlotAddress.gateEmbedding,
      SourceClauseGateAffineAddress.addressEmbedding,
      SourceClauseGateSlotAddress.temp,
      ordinal]
    simp only [SourceClauseGateAffineAddress.addressSource]
    simp only [Sum.inl.injEq, reduceCtorEq,
      ↓reduceIte]
    rw [show (Sum.inr (Sum.inl (Sum.inl (0 : Fin 5))) :
        SourceClauseGateSlotAddress.Stack) =
        (Function.Embedding.inr : SourceClauseGateAffineAddress.Stack ↪
          SourceClauseGateSlotAddress.Stack) (.inl (.inl 0)) by rfl,
      bank_at]
    rfl
  · intro ⟨x, h⟩
    simp [ordinal, PrefixUnitRun.unitEmbedding] at h

noncomputable def blank (n ordinalValue : ℕ)
    (savedBits outputBits countBits : List Bool) : Stack → List Bool :=
  clean (PrefixUnitRun.initial n ordinalValue 0 0
    savedBits outputBits countBits)

theorem blank_vertexCount (n ordinalValue : ℕ)
    (savedBits outputBits countBits : List Bool) :
    blank n ordinalValue savedBits outputBits countBits vertexCount =
      List.replicate n true := by
  simpa [blank, clean, SourceClauseClearExcept.result, vertexCount_mem] using
    initial_vertexCount n ordinalValue 0 0 savedBits outputBits countBits

theorem blank_ordinal (n ordinalValue : ℕ)
    (savedBits outputBits countBits : List Bool) :
    blank n ordinalValue savedBits outputBits countBits ordinal =
      List.replicate ordinalValue true := by
  simpa [blank, clean, SourceClauseClearExcept.result, ordinal_mem] using
    initial_ordinal n ordinalValue 0 0 savedBits outputBits countBits

theorem blank_saved (n ordinalValue : ℕ)
    (savedBits outputBits countBits : List Bool) :
    blank n ordinalValue savedBits outputBits countBits saved = savedBits := by
  rw [blank, clean, SourceClauseClearExcept.result,
    if_pos saved_mem]
  rfl

theorem blank_output (n ordinalValue : ℕ)
    (savedBits outputBits countBits : List Bool) :
    blank n ordinalValue savedBits outputBits countBits output = outputBits := by
  rw [blank, clean, SourceClauseClearExcept.result,
    if_pos output_mem]
  rfl

theorem blank_count (n ordinalValue : ℕ)
    (savedBits outputBits countBits : List Bool) :
    blank n ordinalValue savedBits outputBits countBits count = countBits := by
  rw [blank, clean, SourceClauseClearExcept.result,
    if_pos count_mem]
  rfl

theorem clean_finished_eq_blank (n ordinalValue w ell : ℕ) (sign : Bool)
    (savedBits outputBits countBits : List Bool) :
    clean (PrefixUnitRun.finished n ordinalValue w ell sign
      savedBits outputBits countBits) =
      blank n ordinalValue
        ((EncodedCNF.encodeClause (SourceClauseUnitMachine.unitClause
          (ordinalValue * w + (2 * n + ell)) sign)).reverse ++ savedBits)
        outputBits (true :: countBits) := by
  funext x
  by_cases hx : x ∈ keep
  · have hcases : x = vertexCount ∨ x = ordinal ∨ x = saved ∨
        x = output ∨ x = count := by
      simpa only [keep, Finset.mem_insert, Finset.mem_singleton] using hx
    rcases hcases with rfl | rfl | rfl | rfl | rfl
    · rw [clean, SourceClauseClearExcept.result, if_pos vertexCount_mem,
        final_vertexCount, blank_vertexCount]
    · rw [clean, SourceClauseClearExcept.result, if_pos ordinal_mem,
        final_ordinal, blank_ordinal]
    · rw [final_saved, blank_saved]
    · rw [clean, SourceClauseClearExcept.result, if_pos output_mem]
      change PrefixUnitRun.finished n ordinalValue w ell sign
        savedBits outputBits countBits PrefixUnitRun.outputKey = _
      rw [PrefixUnitRun.final_output, blank_output]
    · rw [final_count, blank_count]
  · simp only [clean, blank, SourceClauseClearExcept.result,
      hx, ↓reduceIte]

def constantTarget : Fin 3 → Stack
  | 0 => .inl (.inl 1)
  | 1 => .inl (.inl 2)
  | 2 => .inl (SourceClauseGateSlotAddress.gateEmbedding
      (SourceClauseGateAffineAddress.addressEmbedding (.inl 1)))

def constantSize (w ell : ℕ) : Fin 3 → ℕ
  | 0 => 2
  | 1 => ell
  | 2 => w

noncomputable def stage (w ell : ℕ) (S : Stack → List Bool) :
    Stack → List Bool :=
  SourceClauseFixedBatch.bankPrefix constantTarget
    (constantSize w ell) S 3

theorem constantTarget_injective : Function.Injective constantTarget := by
  intro i j h
  fin_cases i <;> fin_cases j <;>
    simp [constantTarget, SourceClauseGateSlotAddress.gateEmbedding] at h ⊢

theorem stage_run (w ell : ℕ) (S : Stack → List Bool) :
    ((advance (SourceClauseFixedBatch.program constantTarget
      (constantSize w ell)))^[SourceClauseFixedBatch.costPrefix
        (constantSize w ell) 3 + 1])
      (⟨some (SourceClauseFixedBatch.labelAt (constantSize w ell) 0), (), S⟩) =
      ⟨none, (), stage w ell S⟩ := by
  exact SourceClauseFixedBatch.run constantTarget (constantSize w ell) S

theorem stage_constant (w ell : ℕ) (S : Stack → List Bool)
    (i : Fin 3) :
    stage w ell S (constantTarget i) =
      List.replicate (constantSize w ell i) true ++
        S (constantTarget i) := by
  exact SourceClauseFixedBatch.result_target constantTarget
    (constantSize w ell) S constantTarget_injective i

theorem stage_blank_eq_initial (n ordinalValue w ell : ℕ)
    (savedBits outputBits countBits : List Bool) :
    stage w ell (blank n ordinalValue savedBits outputBits countBits) =
      PrefixUnitRun.initial n ordinalValue w ell
        savedBits outputBits countBits := by
  funext x
  by_cases h0 : x = constantTarget 0
  · subst x
    rw [stage_constant]
    simp [constantTarget, constantSize, blank, clean, keep,
      SourceClauseClearExcept.result, PrefixUnitRun.initial,
      PrefixUnitAddress.initial, SourceClauseGateSlotAddress.initial,
      SourceClauseGateSlotAddress.offsetInput, MatrixAddressMachine.cfg,
      vertexCount, ordinal, saved, output, count,
      SourceClauseGateSlotAddress.gateEmbedding,
      SourceClauseGateAffineAddress.addressEmbedding,
      PrefixUnitRun.savedKey, PrefixUnitRun.outputKey,
      PrefixUnitRun.countKey]
  by_cases h1 : x = constantTarget 1
  · subst x
    rw [stage_constant]
    simp [constantTarget, constantSize, blank, clean, keep,
      SourceClauseClearExcept.result, PrefixUnitRun.initial,
      PrefixUnitAddress.initial, SourceClauseGateSlotAddress.initial,
      SourceClauseGateSlotAddress.offsetInput, MatrixAddressMachine.cfg,
      vertexCount, ordinal, saved, output, count]
  by_cases h2 : x = constantTarget 2
  · subst x
    rw [stage_constant]
    simp [constantTarget, constantSize, blank, clean, keep,
      SourceClauseClearExcept.result, PrefixUnitRun.initial,
      PrefixUnitAddress.initial, SourceClauseGateSlotAddress.initial,
      SourceClauseGateAffineAddress.initial,
      SourceLabelAddressMachine.inputs, SourceLabelAddressMachine.ambient,
      SourceClauseGateSlotAddress.gateEmbedding,
      SourceClauseGateAffineAddress.addressEmbedding,
      vertexCount, ordinal, saved, output, count]
  have hout : ∀ i : Fin 3, constantTarget i ≠ x := by
    intro i; fin_cases i
    · exact Ne.symm h0
    · exact Ne.symm h1
    · exact Ne.symm h2
  change SourceClauseFixedBatch.bankPrefix constantTarget
    (constantSize w ell) (blank n ordinalValue savedBits outputBits countBits) 3 x = _
  rw [SourceClauseFixedBatch.result_outside constantTarget
    (constantSize w ell) _ x hout]
  rcases x with x | x
  · rcases x with x | x
    · fin_cases x <;>
        simp [blank, clean, keep, SourceClauseClearExcept.result,
          PrefixUnitRun.initial, PrefixUnitAddress.initial,
          SourceClauseGateSlotAddress.initial,
          SourceClauseGateSlotAddress.offsetInput, MatrixAddressMachine.cfg,
          constantTarget, vertexCount, ordinal, saved, output, count,
          PrefixUnitRun.savedKey, PrefixUnitRun.outputKey,
          PrefixUnitRun.countKey,
          SourceClauseGateSlotAddress.gateEmbedding,
          SourceClauseGateAffineAddress.addressEmbedding] at *
    · fin_cases x <;>
        simp [blank, clean, keep, SourceClauseClearExcept.result,
        PrefixUnitRun.initial, PrefixUnitAddress.initial,
        SourceClauseGateSlotAddress.initial, constantTarget,
        SourceClauseGateAffineAddress.initial,
        SourceLabelAddressMachine.inputs, SourceLabelAddressMachine.ambient,
        vertexCount, ordinal, saved, output, count,
        PrefixUnitRun.savedKey, PrefixUnitRun.outputKey,
        PrefixUnitRun.countKey,
        SourceClauseGateSlotAddress.gateEmbedding,
        SourceClauseGateAffineAddress.addressEmbedding,
        SourceClauseGateSuccessor.initial,
        SourceClauseGateBroadcast.initial,
        SourceClauseGateSchedule.contents] at *
  · fin_cases x <;>
      simp [blank, clean, keep, SourceClauseClearExcept.result,
      PrefixUnitRun.initial, PrefixUnitAddress.initial,
      SourceClauseGateSlotAddress.initial, constantTarget,
      SourceClauseUnitMachine.initial,
      vertexCount, ordinal, saved, output, count,
      PrefixUnitRun.savedKey, PrefixUnitRun.outputKey,
      PrefixUnitRun.countKey,
      SourceClauseCountedStream.contents,
      SourceLiteralWriter.cfg, SourceLiteralWriter.contents] at *

end EthInapproximability.CurrentPaper.SourceBooleanPrefix.PrefixUnitClean
