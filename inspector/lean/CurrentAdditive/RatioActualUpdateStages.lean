import CurrentAdditive.RatioPhysicalFold
import CurrentAdditive.RatioPositiveScaling
import CurrentAdditive.IndependentSupport
import CurrentAdditive.CodeDUpdateFullPipeline

set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 100

/-! Exact all-width dependent branch, with a concrete ratio scanner and a
concrete zero-removing updater. The ratio-pair-list and update-request-list
preparation remain explicit input boundaries; this is not a whole Code D run.
-/

namespace CurrentAdditive.RatioActualUpdateStages

open Turing EthInapproximability.CurrentPaper BitMachineEncoding
open SequentialCode SequentialArrayBridge SequentialTotality

theorem actual_free_positive_update {q : Nat}
    (source : Array ((Fin q → Nat) × ℚ)) (a : Array (Array ℚ))
    (hsize : (source.map Prod.snd).size = columnCount a)
    (hpositive : ∀ i < (source.map Prod.snd).size,
      0 < (source.map Prod.snd)[i]?.getD 0)
    (hrow : ∃ i < a.size, ∀ j < columnCount a, cell a i j = 1)
    (f : Fin (columnCount a))
    (hfree : typedFree (echelonTyped (matrixOfArray a) 0 0
      (columnCount a)).2 = some f) (context : List Bool) :
    ∃ cert : {coeff : Array ℚ // IsDependence a coeff},
      MaterializedGauss.certifiedMaterializedDependence a = some cert ∧
      ∃ lambda : ℚ,
        0 < lambda ∧ minimumRatio (source.map Prod.snd) cert.val = some lambda ∧
        let updated := CodeDUpdatedArithmeticABI.candidateWeights source cert.val lambda
        eliminateWeights (source.map Prod.snd) cert.val = some updated ∧
        updated.all (fun w => decide (0 ≤ w)) = true ∧
        sameMoments a (source.map Prod.snd) updated = true ∧
        (positiveIndices updated).length < source.size ∧
        let xs := RatioPhysicalFold.pairWords
          (MinimumRatioFoldSemanticJoin.pairs (source.map Prod.snd) cert.val)
        (∃ t ≤ RatioPhysicalFold.clock context xs,
          ∃ v,
          ((advance RatioPhysicalFold.program)^[t])
            (⟨some (.inr (.inr .check)),
              StatefulListScheduler.getterControl MinimumRatioCallbackPhysical.control
                (CurrentAdditive.CylinderContextScanStep.copyControl
                  ((), none)),
              RatioPhysicalFold.boundary (SourceListEncoding.encode xs) []
                context 0 xs.length⟩ :
              TM2.Cfg (fun _ : MinimumRatioCallbackLayout.Stack => Bool) _ _) =
            ⟨none, v,
              RatioPhysicalFold.boundary (SourceListEncoding.encode xs)
                (MinimumRatioStepSpec.bestPacket (some lambda))
                context xs.length 0⟩) ∧
        CodeDUpdateFullPipeline.machine.OutputsWithin
          (CodeDUpdateRequestABI.requestPacketList source cert.val lambda)
          (CodeDCanonicalSourceV2.encodedSource
            (CodeDCompactSequentialBridge.retainedSource source updated))
          (CodeDUpdateFullPipeline.clock source cert.val lambda) := by
  obtain ⟨cert, hcert⟩ :=
    IndependentSupport.certifiedMaterializedDependence_total_of_free a f hfree
  have hdep := cert.property
  obtain ⟨hcsize, hnonzero, _⟩ := (dependence_spec a cert.val).mp hdep
  have hsum : cert.val.toList.sum = 0 :=
    SequentialElimination.zero_sum_of_constant_row a cert.val hdep hrow
  obtain ⟨lambda, hmin, hlambda, _, _⟩ :=
    SequentialElimination.minimumRatio_total (source.map Prod.snd) cert.val
      (hsize.trans hcsize.symm) hpositive hsum hnonzero
  obtain ⟨out, helim, _, hnn, hmom, hshrink⟩ :=
    SequentialElimination.eliminateWeights_total a (source.map Prod.snd)
      cert.val hsize hpositive hdep hsum
  have heq := CodeDUpdatedArithmeticABI.eliminateWeights_eq_candidate
    source cert.val lambda out hmin helim
  subst out
  refine ⟨cert, hcert, lambda, hlambda, hmin, helim, hnn, hmom, ?_, ?_, ?_⟩
  · simpa only [Array.size_map] using hshrink
  · simpa only [hmin] using
      RatioPhysicalFold.exact_minimum_runs (source.map Prod.snd) cert.val context
  · exact CodeDUpdateFullPipeline.outputs source cert.val lambda hnn

#print axioms actual_free_positive_update

end CurrentAdditive.RatioActualUpdateStages
