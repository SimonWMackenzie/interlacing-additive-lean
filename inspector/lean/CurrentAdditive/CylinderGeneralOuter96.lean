import CurrentAdditive.SourceContextScheduler96
import CurrentAdditive.CylinderGeneralSourceRowBare

/-! The exact outer Fin96 integration interface for one arbitrary feature.
Its hypothesis is a physical callback contract for the descriptor; the
theorem then runs the literal repeated tuple getter over the actual source. -/

noncomputable section

namespace CurrentAdditive.CylinderGeneralOuter96

open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open CurrentAdditive.CylinderSourceTupleProjection
open CurrentAdditive.CylinderFeatureCodec
open CurrentAdditive.CylinderGeneralSourceRowBare
open CurrentAdditive.Wide96ContextListScheduler
open CurrentAdditive.SourceContextScheduler96

variable {L V : Type} [DecidableEq L] [Fintype L]
    [DecidableEq V] [Fintype V]

theorem feature_row_run
    {q : Nat} (source : Array ((Fin q → Nat) × ℚ))
    (feature : List (Nat × Nat))
    (callback : L → TM2.Stmt (fun _ : Fin 96 => Bool) L V)
    (callbackStart : L) (callbackInit : V)
    (C : SourceCallbackContract callback callbackStart callbackInit
      (featurePiece q feature) [] (encodeFeature feature)
      (tupleWords source)) :
    let original := tupleWords source
    let sourceBytes := SourceListEncoding.encode original
    let row := source.toList.map (fun entry =>
      decide (SequentialCode.generatedFeatureValue entry.1 feature ≠ 0))
    ∃ t ≤ SourceContextScheduler96.remainingBudget callback
        callbackStart callbackInit (featurePiece q feature) []
        (encodeFeature feature) original C [] original,
      ∃ vFinal : Wide96ContextListScheduler.Control V,
      Wide96ContextListScheduler.run callback callbackStart callbackInit t
        ⟨some (.inr (.inr .check)),
         Wide96ContextListScheduler.getterControl callbackInit
           (CylinderContextScanStep.copyControl ((), none)),
         (Wide96ContextPreservingScan.frame
           (foreignBank [] (encodeFeature feature) original.length C.extra)
           (CylinderContextScanStep.initial sourceBytes 0)).stk⟩ =
        ⟨none, vFinal,
         (Wide96ContextPreservingScan.frame
           (foreignBank row (encodeFeature feature) 0 C.extra)
           (CylinderContextScanStep.initial sourceBytes
             original.length)).stk⟩ := by
  dsimp only
  let original := tupleWords source
  have hrun := SourceContextScheduler96.run_remaining callback
    callbackStart callbackInit (featurePiece q feature) []
    (encodeFeature feature) original C [] original (by simp)
    (Wide96ContextListScheduler.getterControl callbackInit
      (CylinderContextScanStep.copyControl ((), none)))
  have hrow : joined (featurePiece q feature) original =
      source.toList.map (fun entry =>
        decide (SequentialCode.generatedFeatureValue entry.1 feature ≠ 0)) := by
    simpa [original, joined] using feature_row_exact source feature
  obtain ⟨t, ht, v, hr⟩ := hrun
  refine ⟨t, ht, v, ?_⟩
  simpa only [List.nil_append, List.length_nil, Nat.zero_add,
    List.append_nil, hrow, original] using hr

theorem feature_row_run_fixed_input
    {q : Nat} (source : Array ((Fin q → Nat) × ℚ))
    (feature : List (Nat × Nat))
    (callback : L → TM2.Stmt (fun _ : Fin 96 => Bool) L V)
    (callbackStart : L) (callbackInit : V)
    (C : SourceCallbackContract callback callbackStart callbackInit
      (featurePiece q feature) [] (encodeFeature feature)
      (tupleWords source)) (P : Nat)
    (hP : ∀ pre word suffix,
      pre ++ word :: suffix = tupleWords source →
      SourceContextScheduler96.cycleBudget callback callbackStart
        callbackInit (featurePiece q feature) []
        (encodeFeature feature) (tupleWords source) C
        pre word suffix ≤ P) :
    let original := tupleWords source
    let sourceBytes := SourceListEncoding.encode original
    let row := source.toList.map (fun entry =>
      decide (SequentialCode.generatedFeatureValue entry.1 feature ≠ 0))
    ∃ t ≤ (source.size + 1) * (P + 1),
      ∃ vFinal : Wide96ContextListScheduler.Control V,
      Wide96ContextListScheduler.run callback callbackStart callbackInit t
        ⟨some (.inr (.inr .check)),
         Wide96ContextListScheduler.getterControl callbackInit
           (CylinderContextScanStep.copyControl ((), none)),
         (Wide96ContextPreservingScan.frame
           (foreignBank [] (encodeFeature feature) original.length C.extra)
           (CylinderContextScanStep.initial sourceBytes 0)).stk⟩ =
        ⟨none, vFinal,
         (Wide96ContextPreservingScan.frame
           (foreignBank row (encodeFeature feature) 0 C.extra)
           (CylinderContextScanStep.initial sourceBytes
             original.length)).stk⟩ := by
  dsimp only
  let original := tupleWords source
  have hrun := SourceContextScheduler96.run_full_fixed_input callback
    callbackStart callbackInit (featurePiece q feature) []
    (encodeFeature feature) original C P hP
    (Wide96ContextListScheduler.getterControl callbackInit
      (CylinderContextScanStep.copyControl ((), none)))
  have hrow : joined (featurePiece q feature) original =
      source.toList.map (fun entry =>
        decide (SequentialCode.generatedFeatureValue entry.1 feature ≠ 0)) := by
    simpa [original, joined] using feature_row_exact source feature
  obtain ⟨t, ht, v, hr⟩ := hrun
  refine ⟨t, ?_, v, ?_⟩
  · simpa [original, tupleWords] using ht
  · simpa only [List.nil_append, hrow, original] using hr

#print axioms feature_row_run
#print axioms feature_row_run_fixed_input

end CurrentAdditive.CylinderGeneralOuter96
