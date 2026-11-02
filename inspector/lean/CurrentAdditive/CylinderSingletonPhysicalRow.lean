import CurrentAdditive.CylinderSourceContract
import CurrentAdditive.CylinderSingletonSemantic

/-! Literal Fin32 execution of one singleton cylinder row on the projected
production V2 tuple list, with the scheduler's exact charged finite budget. -/

noncomputable section

namespace CurrentAdditive.CylinderSingletonPhysicalRow

open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open CurrentAdditive.GaussListContext
open CurrentAdditive.CylinderSourceTupleProjection
open CurrentAdditive.CylinderSourceContractPrep
open CurrentAdditive.LargeContextListScheduler
open CurrentAdditive.SourceContextScheduler
open CurrentAdditive.CylinderCoordinateEqualityCallback

theorem singleton_row_run {q : Nat}
    (source : Array ((Fin q → Nat) × ℚ)) (i : Fin q) (y : Nat) :
    let original := tupleWords source
    let C := CurrentAdditive.CylinderSourceContract.singletonContract
      source i y [] []
    let sourceBytes := SourceListEncoding.encode original
    let row := source.toList.map (fun entry =>
      decide (SequentialCode.generatedFeatureValue entry.1
        [(i.val, y)] ≠ 0))
    ∃ t ≤ SourceContextScheduler.remainingBudget
        CylinderCoordinateEqualityCallback.program
        CylinderSourceContractPrep.callbackStart
        CylinderSourceContractPrep.callbackInit
        (piece i.val y.bits) [] [] original C [] original,
      ∃ vFinal : LargeContextListScheduler.Control Control,
      LargeContextListScheduler.run
        CylinderCoordinateEqualityCallback.program
        CylinderSourceContractPrep.callbackStart
        CylinderSourceContractPrep.callbackInit t
        ⟨some (.inr (.inr .check)),
         LargeContextListScheduler.getterControl
           CylinderSourceContractPrep.callbackInit
           (CylinderContextScanStep.copyControl ((), none)),
         (LargeContextPreservingScan.frame
           (foreignBank [] [] original.length C.extra)
           (CylinderContextScanStep.initial sourceBytes 0)).stk⟩ =
        ⟨none, vFinal,
         (LargeContextPreservingScan.frame
           (foreignBank row [] 0 C.extra)
           (CylinderContextScanStep.initial sourceBytes
             original.length)).stk⟩ := by
  classical
  dsimp only
  let original := tupleWords source
  let C := CurrentAdditive.CylinderSourceContract.singletonContract
    source i y [] []
  have hrun := SourceContextScheduler.run_remaining
    CylinderCoordinateEqualityCallback.program
    CylinderSourceContractPrep.callbackStart
    CylinderSourceContractPrep.callbackInit
    (piece i.val y.bits) [] [] original C [] original
    (by simp) (LargeContextListScheduler.getterControl
      CylinderSourceContractPrep.callbackInit
      (CylinderContextScanStep.copyControl ((), none)))
  have hrow : joined (piece i.val y.bits) original =
      source.toList.map (fun entry =>
        decide (SequentialCode.generatedFeatureValue entry.1
          [(i.val, y)] ≠ 0)) := by
    simpa [original, piece, joined] using
      CurrentAdditive.CylinderSingletonSemantic.singleton_row_exact
        source i y
  obtain ⟨t, ht, v, hr⟩ := hrun
  refine ⟨t, ht, v, ?_⟩
  simpa only [List.nil_append, List.length_nil, Nat.zero_add,
    List.append_nil, hrow, original, C] using hr

#print axioms singleton_row_run

end CurrentAdditive.CylinderSingletonPhysicalRow
