import EthInapproximability.CurrentPaper.SourceClausePairGateBase
import EthInapproximability.CurrentPaper.BitMachineClearBank
import EthInapproximability.CurrentPaper.BitMachineCopy

namespace EthInapproximability.CurrentPaper.SourceBooleanPrefix.PairGatePatch

open Turing TM2.Stmt BitMachineEncoding BitMachineStackEmbedding
open SourceBooleanEncoding
open scoped Classical

abbrev Stack := PairGateBase.Stack

noncomputable def gateIndex : Stack := .inl PrefixGateOperands.gateIndex
noncomputable def gateOffset : Stack := .inl PrefixGateOperands.gateOffset
def ordinal : Stack := PairUnitLift.pairOrdinalCell
noncomputable def scratch : Stack := .inl PrefixGateOperands.temp

theorem index_ne_offset : gateIndex ≠ gateOffset := by
  simp [gateIndex, gateOffset,
    PrefixGateOperands.gateIndex,
    PrefixGateOperands.gateOffset,
    PrefixGateOperands.gateCell,
    SourceClauseRowGate.gateEmbedding,
    SourceClauseGateSlotAddress.gateEmbedding,
    SourceClauseGateAffineAddress.addressEmbedding]

theorem ordinal_ne_index : ordinal ≠ gateIndex := by
  simp [ordinal, gateIndex, PairUnitLift.pairOrdinalCell]

theorem ordinal_ne_offset : ordinal ≠ gateOffset := by
  simp [ordinal, gateOffset, PairUnitLift.pairOrdinalCell]

theorem scratch_ne_index : scratch ≠ gateIndex := by
  exact fun h => PrefixGateOperands.temp_ne_gate (Sum.inl.inj h)

theorem scratch_ne_offset : scratch ≠ gateOffset := by
  simp [scratch, gateOffset,
    PrefixGateOperands.temp, PrefixGateOperands.gateOffset,
    PrefixGateOperands.gateCell,
    SourceClauseRowGate.temp,
    SourceClauseRowGate.gateEmbedding]

theorem ordinal_ne_scratch : ordinal ≠ scratch := by
  simp [ordinal, scratch, PairUnitLift.pairOrdinalCell]

noncomputable def target : Fin 2 → Stack
  | 0 => gateIndex
  | 1 => gateOffset

noncomputable def targetEmbedding : Fin 2 ↪ Stack where
  toFun := target
  inj' := by
    intro i j h
    fin_cases i <;> fin_cases j <;>
      simp_all [target, index_ne_offset, Ne.symm index_ne_offset]

noncomputable def clearProgram : Fin 4 →
    TM2.Stmt (fun _ : Stack => Bool) (Fin 4) (Unit × Option Bool)
  | 0 => BitMachineClearBank.clearStep gateIndex 0 1
  | 1 => BitMachineClearBank.clearStep gateOffset 1 2
  | 2 => BitMachineClearBank.finishStep id 3
  | 3 => halt

noncomputable def clearTime (B : Stack → List Bool) : Nat :=
  (B gateIndex).length + (B gateOffset).length + 4

theorem clear_run (B : Stack → List Bool) :
    ((advance clearProgram)^[clearTime B])
      (⟨some 0, ((), none), B⟩ :
        TM2.Cfg (fun _ : Stack => Bool) _ _) =
      ⟨none, ((), none), BitMachineClearBank.cleared target B⟩ := by
  have hr := BitMachineClearBank.clear_bank_run
    clearProgram id 3 2 target targetEmbedding.injective
    (fun i : Fin 3 => i.castSucc)
    (by intro i; fin_cases i <;> rfl)
    (by rfl) () B
  change ((advance clearProgram)^[(∑ i : Fin 2, (B (target i)).length) + 2 + 1])
      (⟨some 0, ((), none), B⟩ :
        TM2.Cfg (fun _ : Stack => Bool) _ _) =
      ⟨some 3, ((), none), BitMachineClearBank.cleared target B⟩ at hr
  change ((advance clearProgram)^[
      (B gateIndex).length + (B gateOffset).length + 4])
      (⟨some 0, ((), none), B⟩ :
        TM2.Cfg (fun _ : Stack => Bool) _ _) =
      ⟨none, ((), none), BitMachineClearBank.cleared target B⟩
  rw [show (B gateIndex).length + (B gateOffset).length + 4 =
    ((∑ i : Fin 2, (B (target i)).length) + 2 + 1) + 1 by
      simp [Fin.sum_univ_succ, target],
    Function.iterate_succ_apply', hr]
  rfl

noncomputable def copySlots : Fin 3 ↪ Stack where
  toFun
    | 0 => ordinal
    | 1 => gateIndex
    | 2 => scratch
  inj' := by
    intro i j h
    fin_cases i <;> fin_cases j <;>
      simp_all [ordinal_ne_index, ordinal_ne_scratch,
        scratch_ne_index, Ne.symm ordinal_ne_index,
        Ne.symm ordinal_ne_scratch, Ne.symm scratch_ne_index]

noncomputable def copyProgram :=
  fun l => stackStmt copySlots (BitMachineCopy.program l)

theorem copy_run (B : Stack → List Bool)
    (hindex : B gateIndex = []) (hscratch : B scratch = []) :
    ((advance copyProgram)^[2 * (B ordinal).length + 2])
      (⟨some .scan, none, B⟩ :
        TM2.Cfg (fun _ : Stack => Bool) _ _) =
      ⟨none, none, Function.update B gateIndex (B ordinal)⟩ := by
  let word := B ordinal
  let C := BitMachineCopy.cfg (some .scan) none word [] []
  have hbank : bank copySlots B C.stk = B := by
    apply bank_eq_self
    intro k
    fin_cases k
    · rfl
    · exact hindex.symm
    · exact hscratch.symm
  have hc : ((advance BitMachineCopy.program)^[2 * word.length + 2]) C =
      BitMachineCopy.cfg none none word word [] := by
    simpa [C, BitMachineCopy.run] using
      BitMachineCopy.run_correct none word []
  have he := BitMachineStackRun.run copySlots B
    BitMachineCopy.program C (2 * word.length + 2)
  rw [hc] at he
  have hf : (BitMachineCopy.cfg none none word word []).stk =
      Function.update C.stk 1 word := by
    funext k
    fin_cases k <;> rfl
  simp only [stackCfg, hf, bank_update, hbank] at he
  simpa only [copyProgram, word, copySlots] using he

noncomputable def offsetTarget : Fin 1 → Stack := fun _ => gateOffset
def offsetSize (ell : Fin 2) : Fin 1 → Nat := fun _ => ell.val

noncomputable def offsetProgram (ell : Fin 2) :=
  SourceClauseFixedBatch.program offsetTarget (offsetSize ell)

theorem offset_run (ell : Fin 2) (B : Stack → List Bool)
    (hoffset : B gateOffset = []) :
    ((advance (offsetProgram ell))^[
      SourceClauseFixedBatch.costPrefix (offsetSize ell) 1 + 1])
      (⟨some (SourceClauseFixedBatch.labelAt (offsetSize ell) 0), (), B⟩ :
        TM2.Cfg (fun _ : Stack => Bool) _ _) =
      ⟨none, (), Function.update B gateOffset
        (List.replicate ell.val true)⟩ := by
  have h := SourceClauseFixedBatch.run offsetTarget (offsetSize ell) B
  simpa [offsetProgram, SourceClauseFixedBatch.bankPrefix,
    SourceClauseFixedBatch.prepend, offsetTarget, offsetSize,
    hoffset] using h

end EthInapproximability.CurrentPaper.SourceBooleanPrefix.PairGatePatch
