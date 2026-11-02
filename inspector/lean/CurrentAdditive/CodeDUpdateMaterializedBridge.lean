import CurrentAdditive.CodeDUpdateFullPipeline
import CurrentAdditive.SequentialCompressionTotality

/-! A successful semantic elimination supplies exactly the arithmetic requests used physically. -/

namespace CurrentAdditive.CodeDUpdateMaterializedBridge

open SequentialCode SequentialSourceCode MaterializedGauss SequentialCompressionTotality
open CodeDUpdatedArithmeticABI CodeDCompactSequentialBridge

theorem certificate_size {q n : Nat}
    (φ : (Fin q → Nat) → Fin n → ℚ)
    (source : Array ((Fin q → Nat) × ℚ))
    (cert : {x : Array ℚ // IsDependence (featureRows n φ source) x}) :
    cert.val.size = source.size := by
  have hc := (dependence_spec _ _).mp cert.property
  by_cases hn : 0 < n
  · simpa [featureRows_columnCount n φ source hn] using hc.1
  · have hn0 : n = 0 := by omega
    have hzero : columnCount (featureRows n φ source) = 0 := by
      subst n
      simp [featureRows, columnCount]
    have hsize : cert.val.size = 0 := by simpa [hzero] using hc.1
    obtain ⟨j, hj, _⟩ := hc.2.1
    simp [hsize] at hj

theorem successful_step_has_requests {q n : Nat}
    (φ : (Fin q → Nat) → Fin n → ℚ)
    (source out : Array ((Fin q → Nat) × ℚ))
    (h : compressSourceOnceMaterialized n φ source = some out) :
    ∃ (coeff : Array ℚ) (lambda : ℚ),
      coeff.size = source.size ∧
      (candidateWeights source coeff lambda).all
        (fun w => decide (0 ≤ w)) = true ∧
      out = retainedSource source (candidateWeights source coeff lambda) := by
  let matrix := featureRows n φ source
  let weights := source.map Prod.snd
  cases hc : certifiedMaterializedDependence matrix with
  | none =>
      simp [compressSourceOnceMaterialized, matrix, weights, hc] at h
  | some cert =>
      cases he : eliminateWeights weights cert.val with
      | none =>
          simp [compressSourceOnceMaterialized, matrix, weights, hc, he] at h
      | some updated =>
          cases hr : minimumRatio weights cert.val with
          | none =>
              simp [eliminateWeights, hr] at he
          | some lambda =>
              have hu : updated = candidateWeights source cert.val lambda := by
                exact eliminateWeights_eq_candidate source cert.val lambda updated
                  (by simpa only [weights] using hr)
                  (by simpa only [weights] using he)
              have hh := h
              simp only [compressSourceOnceMaterialized, matrix, weights,
                hc, he] at hh
              split at hh
              · split at hh
                · split at hh
                  · cases hh
                    refine ⟨cert.val, lambda,
                      certificate_size φ source cert, ?_, ?_⟩
                    · have hguard :
                        (((weights.all (fun w => decide (0 < w))) &&
                            updated.all (fun w => decide (0 ≤ w))) &&
                            sameMoments matrix weights updated) = true := by
                        assumption
                      simp only [Bool.and_eq_true] at hguard
                      have hnn := hguard.1.2
                      simpa [← hu] using hnn
                    · simpa [← hu, retainedSource]
                  · cases hh
                · cases hh
              · cases hh

theorem physical_materialized_success {q n : Nat}
    (φ : (Fin q → Nat) → Fin n → ℚ)
    (source out : Array ((Fin q → Nat) × ℚ))
    (h : compressSourceOnceMaterialized n φ source = some out) :
    ∃ (coeff : Array ℚ) (lambda : ℚ),
      coeff.size = source.size ∧
      CodeDUpdateFullPipeline.machine.OutputsWithin
        (CodeDUpdateRequestABI.requestPacketList source coeff lambda)
        (CodeDCanonicalSourceV2.encodedSource out)
        (CodeDUpdateFullPipeline.clock source coeff lambda) := by
  obtain ⟨coeff, lambda, hsize, hnonneg, hout⟩ :=
    successful_step_has_requests φ source out h
  exact ⟨coeff, lambda, hsize,
    hout ▸ CodeDUpdateFullPipeline.outputs source coeff lambda hnonneg⟩

#print axioms successful_step_has_requests
#print axioms physical_materialized_success
#print axioms certificate_size

end CurrentAdditive.CodeDUpdateMaterializedBridge
