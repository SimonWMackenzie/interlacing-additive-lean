import EthInapproximability.CurrentPaper.GenericPrefixUnitStage

namespace EthInapproximability.CurrentPaper.SourceGenericPrefixMachine.UnitClean

open Turing BitMachineEncoding BitMachineStackEmbedding
open SourceBooleanPrefix
open scoped Classical

abbrev Stack := PrefixUnitRun.Stack

theorem final_vertexCount (n a ordinal w ell : Nat) (sign : Bool)
    (saved output count : List Bool) :
    UnitRun.finished n a ordinal w ell sign saved output count
      PrefixUnitClean.vertexCount = List.replicate n true := by
  rw [UnitRun.finished,bank_outside]
  · simp [UnitRun.copied,BitMachineBroadcast.copied,
      PrefixUnitRun.source,PrefixUnitRun.temp,PrefixUnitRun.targets,
      PrefixUnitRun.target,UnitRun.addressed,
      SourceGenericUnitAddress.finalBank,
      SourceGenericUnitAddress.transferred,
      SourceClauseGateSlotAddress.transferred,
      SourceClauseGateSlotAddress.offsetDone,
      PrefixUnitAddress.binarySource,
      SourceClauseGateSlotAddress.gateEmbedding,
      SourceClauseGateSlotAddress.temp,PrefixUnitClean.vertexCount]
    rw [bank_outside]
    · simp [BitMachineBroadcast.copied,
        SourceClauseGateSlotAddress.offsetSource,
        SourceClauseGateSlotAddress.affineOffset,
        SourceClauseGateSlotAddress.targets,
        SourceClauseGateSlotAddress.offsetOutput,
        MatrixAddressMachine.cfg]
    · intro ⟨x,h⟩; cases h
  · intro ⟨x,h⟩; cases h

theorem final_ordinal (n a ordinalValue w ell : Nat) (sign : Bool)
    (saved output count : List Bool) :
    UnitRun.finished n a ordinalValue w ell sign saved output count
      PrefixUnitClean.ordinal = List.replicate ordinalValue true := by
  rw [UnitRun.finished,bank_outside]
  · simp [UnitRun.copied,BitMachineBroadcast.copied,
      PrefixUnitRun.source,PrefixUnitRun.temp,PrefixUnitRun.targets,
      PrefixUnitRun.target,UnitRun.addressed,
      SourceGenericUnitAddress.finalBank,
      SourceGenericUnitAddress.transferred,
      SourceClauseGateSlotAddress.transferred,
      SourceClauseGateSlotAddress.offsetDone,
      SourceClauseGateAffineAddress.addressed,
      SourceLabelAddressMachine.outputs,
      SourceLabelAddressMachine.ambient,
      PrefixUnitAddress.binarySource,
      SourceClauseGateSlotAddress.gateEmbedding,
      SourceClauseGateAffineAddress.addressEmbedding,
      SourceClauseGateSlotAddress.temp,PrefixUnitClean.ordinal]
    simp only [SourceClauseGateAffineAddress.addressSource]
    simp only [Sum.inl.injEq,reduceCtorEq,↓reduceIte]
    rw [show (Sum.inr (Sum.inl (Sum.inl (0 : Fin 5))) :
        SourceClauseGateSlotAddress.Stack) =
        (Function.Embedding.inr : SourceClauseGateAffineAddress.Stack ↪
          SourceClauseGateSlotAddress.Stack) (.inl (.inl 0)) by rfl,
      bank_at]
    rfl
  · intro ⟨x,h⟩
    simp [PrefixUnitClean.ordinal,PrefixUnitRun.unitEmbedding] at h

theorem clean_finished_eq_blank (n a ordinal w ell : Nat)
    (sign : Bool) (saved output count : List Bool) :
    PrefixUnitClean.clean
      (UnitRun.finished n a ordinal w ell sign saved output count) =
      PrefixUnitClean.blank n ordinal
        ((EncodedCNF.encodeClause (SourceClauseUnitMachine.unitClause
          (ordinal*w+(n*a+ell)) sign)).reverse ++ saved)
        output (true :: count) := by
  funext x
  by_cases hx : x ∈ PrefixUnitClean.keep
  · have hcases : x = PrefixUnitClean.vertexCount ∨
        x = PrefixUnitClean.ordinal ∨ x = PrefixUnitClean.saved ∨
        x = PrefixUnitClean.output ∨ x = PrefixUnitClean.count := by
      simpa only [PrefixUnitClean.keep,Finset.mem_insert,
        Finset.mem_singleton] using hx
    rcases hcases with rfl | rfl | rfl | rfl | rfl
    · rw [PrefixUnitClean.clean,SourceClauseClearExcept.result,
        if_pos PrefixUnitClean.vertexCount_mem,
        final_vertexCount,PrefixUnitClean.blank_vertexCount]
    · rw [PrefixUnitClean.clean,SourceClauseClearExcept.result,
        if_pos PrefixUnitClean.ordinal_mem,
        final_ordinal,PrefixUnitClean.blank_ordinal]
    · rw [PrefixUnitClean.clean,SourceClauseClearExcept.result,
        if_pos PrefixUnitClean.saved_mem]
      change UnitRun.finished n a ordinal w ell sign saved output count
        PrefixUnitRun.savedKey = _
      rw [UnitRun.final_saved,PrefixUnitClean.blank_saved]
    · rw [PrefixUnitClean.clean,SourceClauseClearExcept.result,
        if_pos PrefixUnitClean.output_mem]
      change UnitRun.finished n a ordinal w ell sign saved output count
        PrefixUnitRun.outputKey = _
      rw [UnitRun.final_output,PrefixUnitClean.blank_output]
    · rw [PrefixUnitClean.clean,SourceClauseClearExcept.result,
        if_pos PrefixUnitClean.count_mem]
      change UnitRun.finished n a ordinal w ell sign saved output count
        PrefixUnitRun.countKey = _
      rw [UnitRun.final_count,PrefixUnitClean.blank_count]
  · simp only [PrefixUnitClean.clean,PrefixUnitClean.blank,
      SourceClauseClearExcept.result,hx,↓reduceIte]

#print axioms clean_finished_eq_blank

end EthInapproximability.CurrentPaper.SourceGenericPrefixMachine.UnitClean
