import CurrentAdditive.CylinderGeneralOuter96
import CurrentAdditive.CylinderGeneralSelectedFrame96

/-! The source-row statement with the actual bank-33 parameter register and
empty high-bank baseline shown explicitly. -/

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
open CurrentAdditive.CylinderGeneralSelectedFrame96

variable {L V : Type} [DecidableEq L] [Fintype L]
    [DecidableEq V] [Fintype V]

theorem feature_row_run_fixed_extra
    {q : Nat} (source : Array ((Fin q → Nat) × ℚ))
    (feature : List (Nat × Nat))
    (callback : L → TM2.Stmt (fun _ : Fin 96 => Bool) L V)
    (callbackStart : L) (callbackInit : V)
    (C : SourceCallbackContract callback callbackStart callbackInit
      (featurePiece q feature) [] (encodeFeature feature)
      (tupleWords source))
    (hExtra : C.extra = evaluationExtra q) :
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
           (foreignBank [] (encodeFeature feature) original.length
             (evaluationExtra q))
           (CylinderContextScanStep.initial sourceBytes 0)).stk⟩ =
        ⟨none, vFinal,
         (Wide96ContextPreservingScan.frame
           (foreignBank row (encodeFeature feature) 0 (evaluationExtra q))
           (CylinderContextScanStep.initial sourceBytes
             original.length)).stk⟩ := by
  dsimp only
  obtain ⟨t, ht, vFinal, hr⟩ :=
    feature_row_run source feature callback callbackStart callbackInit C
  refine ⟨t, ht, vFinal, ?_⟩
  simpa only [hExtra] using hr

theorem feature_row_run_fixed_input_extra
    {q : Nat} (source : Array ((Fin q → Nat) × ℚ))
    (feature : List (Nat × Nat))
    (callback : L → TM2.Stmt (fun _ : Fin 96 => Bool) L V)
    (callbackStart : L) (callbackInit : V)
    (C : SourceCallbackContract callback callbackStart callbackInit
      (featurePiece q feature) [] (encodeFeature feature)
      (tupleWords source)) (P : Nat)
    (hExtra : C.extra = evaluationExtra q)
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
           (foreignBank [] (encodeFeature feature) original.length
             (evaluationExtra q))
           (CylinderContextScanStep.initial sourceBytes 0)).stk⟩ =
        ⟨none, vFinal,
         (Wide96ContextPreservingScan.frame
           (foreignBank row (encodeFeature feature) 0 (evaluationExtra q))
           (CylinderContextScanStep.initial sourceBytes
             original.length)).stk⟩ := by
  dsimp only
  obtain ⟨t, ht, vFinal, hr⟩ :=
    feature_row_run_fixed_input source feature callback callbackStart
      callbackInit C P hP
  refine ⟨t, ht, vFinal, ?_⟩
  simpa only [hExtra] using hr

#print axioms feature_row_run_fixed_extra
#print axioms feature_row_run_fixed_input_extra

end CurrentAdditive.CylinderGeneralOuter96
