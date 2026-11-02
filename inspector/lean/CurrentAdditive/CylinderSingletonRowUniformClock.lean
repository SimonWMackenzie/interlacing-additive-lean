import CurrentAdditive.CylinderSourceUniformCap
import CurrentAdditive.CylinderSingletonSemantic

/-! A literal full-list TM2 run for the singleton cylinder row, with one
fixed-input clock computed from all actual source splits. -/

noncomputable section

namespace CurrentAdditive.CylinderSingletonRowUniformClock

open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open CurrentAdditive.GaussListContext
open CurrentAdditive.CylinderSourceTupleProjection
open CurrentAdditive.CylinderSourceContractPrep
open CurrentAdditive.CylinderSourceClockContract
open CurrentAdditive.CylinderSourceUniformCap
open CurrentAdditive.LargeContextListScheduler
open CurrentAdditive.SourceContextScheduler
open CurrentAdditive.CylinderCoordinateEqualityCallback

theorem singleton_row_run_uniform {q : Nat}
    (source : Array ((Fin q → Nat) × ℚ)) (i : Fin q) (y : Nat) :
    let original := tupleWords source
    let C := clockContract source i y [] []
    let sourceBytes := SourceListEncoding.encode original
    let row := source.toList.map (fun entry =>
      decide (SequentialCode.generatedFeatureValue entry.1
        [(i.val, y)] ≠ 0))
    ∃ t ≤ (source.size + 1) * (uniformCap source i y [] [] + 1),
      ∃ vFinal : LargeContextListScheduler.Control Control,
      LargeContextListScheduler.run
        CylinderCoordinateEqualityCallback.program
        callbackStart callbackInit t
        ⟨some (.inr (.inr .check)),
         LargeContextListScheduler.getterControl callbackInit
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
  let C := clockContract source i y [] []
  let P := uniformCap source i y [] []
  have hP : ∀ a word b, a ++ word :: b = original →
      SourceContextScheduler.cycleBudget
        CylinderCoordinateEqualityCallback.program
        callbackStart callbackInit (piece i.val y.bits)
        [] [] original C a word b ≤ P := by
    intro a word b hSplit
    exact cycleBudget_le_uniformCap source i y [] [] a word b hSplit
  have hrun := SourceContextScheduler.run_full_fixed_input
    CylinderCoordinateEqualityCallback.program
    callbackStart callbackInit (piece i.val y.bits)
    [] [] original C P hP
    (LargeContextListScheduler.getterControl callbackInit
      (CylinderContextScanStep.copyControl ((), none)))
  have hrow : joined (piece i.val y.bits) original =
      source.toList.map (fun entry =>
        decide (SequentialCode.generatedFeatureValue entry.1
          [(i.val, y)] ≠ 0)) := by
    simpa [original, piece, joined] using
      CurrentAdditive.CylinderSingletonSemantic.singleton_row_exact
        source i y
  obtain ⟨t, ht, v, hr⟩ := hrun
  refine ⟨t, ?_, v, ?_⟩
  · simpa [original, tupleWords, P] using ht
  · simpa only [List.nil_append, hrow, original, C] using hr

#print axioms singleton_row_run_uniform

end CurrentAdditive.CylinderSingletonRowUniformClock
