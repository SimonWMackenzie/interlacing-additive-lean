import CurrentV43.Randomized.Algorithm
import CurrentV43.Randomized.Probability
namespace CurrentV43.RandomizedRate
noncomputable section
open CurrentAdditive ParametricSource
open Paper2 EthInapproximability.CurrentPaper
open EncodedETHSource EncodedETHSourceComposition
open Unit4Shell.T10Finite Unit4Shell.Asymptotics
open V42RandomizedETHEndpoint V39PermittedNumericalExtraction
set_option maxHeartbeats 4000000
set_option maxRecDepth 32768
set_option synthInstance.maxSize 32768
variable (D : DinurReduction) (B : BOTReduction (booleanOccurrence D))
/-- The actual all-input algorithm has exactly the source and independent
estimator law; the physical router does not alter a random bit. -/
theorem routedAlgorithm_probability (E : V39ActualOutputMajority.ActualEstimator)
    (S : Schedule) (R : PhysicalConcat.Producer) (cs cutoff : ℕ) (hcutoff : 1 ≤ cutoff)
    (hsource : V42SourceGeometry.originalCutoff D B (cs+2) ≤ cutoff)
    (hfit : ∀ w, resources D B E.classifier S R (routedSource cs cutoff hcutoff w)
      (routedTests D B cs cutoff hcutoff hsource w)) (w : List Bool) :
    (routedAlgorithm D B E.classifier S R cs cutoff hcutoff hsource hfit).prob w (· = [true]) =
    let Φ := routedSource cs cutoff hcutoff w
    (sourceLaw D B (S.gap Φ.val.variables) E Φ).prob
      (fun z => sourceAccepts D B (S.gap Φ.val.variables) Φ
        (routedTests D B cs cutoff hcutoff hsource w) E z.1 z.2) := by
  let Φ := routedSource cs cutoff hcutoff w
  letI : NeZero (t10Graph D B Φ).vertices := ⟨(t10_vertices_pos D B Φ).ne'⟩
  let ht := routedTests D B cs cutoff hcutoff hsource w
  have hc := (hfit w).2 []
  have hcl := V42RawRequestSemantics.classifier_length (t10Graph D B Φ) (t10Graph_valid D B Φ)
    (S.gap Φ.val.variables) (sourceCoefficient D B Φ) (sourceDeltaV D B Φ) (sourceZeta D B) ht E
    (sampledBits D B S Φ [])
  change E.classifier.tapeLength (V42RawRequestPacket.request (t10Graph D B Φ) (t10Graph_valid D B Φ)
    (S.gap Φ.val.variables) (sourceCoefficient D B Φ) (sourceDeltaV D B Φ) (sourceZeta D B) ht
    (sampledBits D B S Φ [])) ≤ _ at hc
  rw [hcl] at hc
  exact physical_probability D B E S R Φ ht (hfit w).1 hc

#print axioms routedAlgorithm_probability
end
end CurrentV43.RandomizedRate
