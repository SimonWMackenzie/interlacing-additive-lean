import CurrentAdditive.CodeDCompactSequentialBridge
import CurrentAdditive.CodeDUpdatedArithmeticABI

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace CurrentAdditive.CodeDMaterializedSuccessCertificate

open SequentialCode SequentialSourceCode MaterializedGauss
open CodeDUpdatedArithmeticABI CodeDCompactSequentialBridge

/-- Successful materialized compression exposes the actual selected Gauss
certificate and minimum ratio, together with its exact retained-source update.
The checked success guard already supplies nonnegative updated weights. -/
theorem successful_step_certificate {q n : Nat}
    (φ : (Fin q → Nat) → Fin n → ℚ)
    (source next : Array ((Fin q → Nat) × ℚ))
    (h : compressSourceOnceMaterialized n φ source = some next) :
    ∃ cert : {coeff : Array ℚ // IsDependence (featureRows n φ source) coeff},
      certifiedMaterializedDependence (featureRows n φ source) = some cert ∧
      ∃ lambda : ℚ,
        minimumRatio (source.map Prod.snd) cert.val = some lambda ∧
        (candidateWeights source cert.val lambda).all
          (fun w => decide (0 ≤ w)) = true ∧
        next = retainedSource source (candidateWeights source cert.val lambda) := by
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
              have hu : updated = candidateWeights source cert.val lambda :=
                eliminateWeights_eq_candidate source cert.val lambda updated
                  (by simpa only [weights] using hr)
                  (by simpa only [weights] using he)
              have hh := h
              simp only [compressSourceOnceMaterialized, matrix, weights,
                hc, he] at hh
              split at hh
              · split at hh
                · split at hh
                  · cases hh
                    refine ⟨cert, ?_, lambda, ?_, ?_, ?_⟩
                    · simpa only [matrix] using hc
                    · simpa only [weights] using hr
                    · have hguard :
                        (((weights.all (fun w => decide (0 < w))) &&
                            updated.all (fun w => decide (0 ≤ w))) &&
                            sameMoments matrix weights updated) = true := by
                        assumption
                      simp only [Bool.and_eq_true] at hguard
                      simpa [← hu] using hguard.1.2
                    · simpa [← hu, retainedSource]
                  · cases hh
                · cases hh
              · cases hh

#print axioms successful_step_certificate

end CurrentAdditive.CodeDMaterializedSuccessCertificate
