import EthInapproximability.CurrentPaper.GenericPrefixUnitRun
import EthInapproximability.CurrentPaper.SourceClausePrefixUnitClean

namespace EthInapproximability.CurrentPaper.SourceGenericPrefixMachine.UnitStage

open Turing BitMachineEncoding
open SourceBooleanPrefix
open scoped Classical

abbrev Stack := PrefixUnitRun.Stack

def constantSize (a w ell : Nat) : Fin 3 → Nat
  | 0 => a
  | 1 => ell
  | 2 => w

noncomputable def stage (a w ell : Nat) (S : Stack → List Bool) :
    Stack → List Bool :=
  SourceClauseFixedBatch.bankPrefix PrefixUnitClean.constantTarget
    (constantSize a w ell) S 3

theorem stage_run (a w ell : Nat) (S : Stack → List Bool) :
    ((advance (SourceClauseFixedBatch.program
      PrefixUnitClean.constantTarget (constantSize a w ell)))^[
        SourceClauseFixedBatch.costPrefix (constantSize a w ell) 3 + 1])
      (⟨some (SourceClauseFixedBatch.labelAt
        (constantSize a w ell) 0),(),S⟩) =
      ⟨none,(),stage a w ell S⟩ := by
  exact SourceClauseFixedBatch.run PrefixUnitClean.constantTarget
    (constantSize a w ell) S

theorem stage_constant (a w ell : Nat) (S : Stack → List Bool)
    (i : Fin 3) :
    stage a w ell S (PrefixUnitClean.constantTarget i) =
      List.replicate (constantSize a w ell i) true ++
        S (PrefixUnitClean.constantTarget i) := by
  exact SourceClauseFixedBatch.result_target
    PrefixUnitClean.constantTarget (constantSize a w ell) S
    PrefixUnitClean.constantTarget_injective i

theorem stage_blank_eq_initial (n a ordinal w ell : Nat)
    (saved output count : List Bool) :
    stage a w ell (PrefixUnitClean.blank n ordinal saved output count) =
      UnitRun.initial n a ordinal w ell saved output count := by
  funext x
  by_cases h0 : x = PrefixUnitClean.constantTarget 0
  · subst x
    rw [stage_constant]
    simp [PrefixUnitClean.constantTarget,constantSize,PrefixUnitClean.blank,
      PrefixUnitClean.clean,PrefixUnitClean.keep,
      SourceClauseClearExcept.result,UnitRun.initial,
      PrefixUnitRun.initial,PrefixUnitAddress.initial,
      SourceGenericUnitAddress.initial,SourceClauseGateSlotAddress.initial,
      SourceClauseGateSlotAddress.offsetInput,MatrixAddressMachine.cfg,
      PrefixUnitClean.vertexCount,PrefixUnitClean.ordinal,
      PrefixUnitClean.saved,PrefixUnitClean.output,PrefixUnitClean.count,
      SourceClauseGateSlotAddress.gateEmbedding,
      SourceClauseGateAffineAddress.addressEmbedding,
      PrefixUnitRun.savedKey,PrefixUnitRun.outputKey,
      PrefixUnitRun.countKey]
  by_cases h1 : x = PrefixUnitClean.constantTarget 1
  · subst x
    rw [stage_constant]
    simp [PrefixUnitClean.constantTarget,constantSize,PrefixUnitClean.blank,
      PrefixUnitClean.clean,PrefixUnitClean.keep,
      SourceClauseClearExcept.result,UnitRun.initial,
      PrefixUnitRun.initial,PrefixUnitAddress.initial,
      SourceGenericUnitAddress.initial,SourceClauseGateSlotAddress.initial,
      SourceClauseGateSlotAddress.offsetInput,MatrixAddressMachine.cfg,
      PrefixUnitClean.vertexCount,PrefixUnitClean.ordinal,
      PrefixUnitClean.saved,PrefixUnitClean.output,PrefixUnitClean.count]
  by_cases h2 : x = PrefixUnitClean.constantTarget 2
  · subst x
    rw [stage_constant]
    simp [PrefixUnitClean.constantTarget,constantSize,PrefixUnitClean.blank,
      PrefixUnitClean.clean,PrefixUnitClean.keep,
      SourceClauseClearExcept.result,UnitRun.initial,
      SourceGenericUnitAddress.initial,SourceClauseGateSlotAddress.initial,
      SourceClauseGateAffineAddress.initial,
      SourceLabelAddressMachine.inputs,SourceLabelAddressMachine.ambient,
      SourceClauseGateSlotAddress.gateEmbedding,
      SourceClauseGateAffineAddress.addressEmbedding,
      PrefixUnitClean.vertexCount,PrefixUnitClean.ordinal,
      PrefixUnitClean.saved,PrefixUnitClean.output,PrefixUnitClean.count]
    all_goals simp [PrefixUnitRun.savedKey,PrefixUnitRun.outputKey,
      PrefixUnitRun.countKey] at *
  have hout : ∀ i : Fin 3, PrefixUnitClean.constantTarget i ≠ x := by
    intro i; fin_cases i
    · exact Ne.symm h0
    · exact Ne.symm h1
    · exact Ne.symm h2
  change SourceClauseFixedBatch.bankPrefix PrefixUnitClean.constantTarget
    (constantSize a w ell)
    (PrefixUnitClean.blank n ordinal saved output count) 3 x = _
  rw [SourceClauseFixedBatch.result_outside
    PrefixUnitClean.constantTarget (constantSize a w ell) _ x hout]
  rcases x with x | x
  · rcases x with x | x
    · fin_cases x <;>
        simp [PrefixUnitClean.blank,PrefixUnitClean.clean,
          PrefixUnitClean.keep,SourceClauseClearExcept.result,
          PrefixUnitRun.initial,PrefixUnitAddress.initial,
          UnitRun.initial,SourceGenericUnitAddress.initial,
          SourceClauseGateSlotAddress.initial,
          SourceClauseGateSlotAddress.offsetInput,MatrixAddressMachine.cfg,
          PrefixUnitClean.constantTarget,PrefixUnitClean.vertexCount,
          PrefixUnitClean.ordinal,PrefixUnitClean.saved,
          PrefixUnitClean.output,PrefixUnitClean.count,
          PrefixUnitRun.savedKey,PrefixUnitRun.outputKey,
          PrefixUnitRun.countKey,
          SourceClauseGateSlotAddress.gateEmbedding,
          SourceClauseGateAffineAddress.addressEmbedding] at *
    · fin_cases x <;>
        simp [PrefixUnitClean.blank,PrefixUnitClean.clean,
          PrefixUnitClean.keep,SourceClauseClearExcept.result,
          PrefixUnitRun.initial,PrefixUnitAddress.initial,
          UnitRun.initial,SourceGenericUnitAddress.initial,
          SourceClauseGateSlotAddress.initial,
          PrefixUnitClean.constantTarget,
          SourceClauseGateAffineAddress.initial,
          SourceLabelAddressMachine.inputs,SourceLabelAddressMachine.ambient,
          PrefixUnitClean.vertexCount,PrefixUnitClean.ordinal,
          PrefixUnitClean.saved,PrefixUnitClean.output,
          PrefixUnitClean.count,PrefixUnitRun.savedKey,
          PrefixUnitRun.outputKey,PrefixUnitRun.countKey,
          SourceClauseGateSlotAddress.gateEmbedding,
          SourceClauseGateAffineAddress.addressEmbedding,
          SourceClauseGateSuccessor.initial,
          SourceClauseGateBroadcast.initial,
          SourceClauseGateSchedule.contents] at *
  · fin_cases x <;>
      simp [PrefixUnitClean.blank,PrefixUnitClean.clean,
        PrefixUnitClean.keep,SourceClauseClearExcept.result,
        PrefixUnitRun.initial,PrefixUnitAddress.initial,
        UnitRun.initial,SourceGenericUnitAddress.initial,
        SourceClauseGateSlotAddress.initial,
        PrefixUnitClean.constantTarget,
        SourceClauseUnitMachine.initial,
        PrefixUnitClean.vertexCount,PrefixUnitClean.ordinal,
        PrefixUnitClean.saved,PrefixUnitClean.output,
        PrefixUnitClean.count,PrefixUnitRun.savedKey,
        PrefixUnitRun.outputKey,PrefixUnitRun.countKey,
        SourceClauseCountedStream.contents,
        SourceLiteralWriter.cfg,SourceLiteralWriter.contents] at *

#print axioms stage_blank_eq_initial

end EthInapproximability.CurrentPaper.SourceGenericPrefixMachine.UnitStage
