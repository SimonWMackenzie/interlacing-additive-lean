import CurrentV43.Randomized.Parameters
import CurrentV43.Parametric.Probability
namespace CurrentV43.RandomizedRate
noncomputable section
open CurrentAdditive ParametricSource
open Paper2 EthInapproximability.CurrentPaper
open EncodedETHSource EncodedETHSourceComposition
open Unit4Shell.T10Finite Unit4Shell.Asymptotics
open V39ActualOutputMajority V39PermittedNumericalExtraction
open V42RandomizedETHEndpoint
variable (D : DinurReduction) (B : BOTReduction (booleanOccurrence D))
/-- Exact probability identity for the physical source and independent
classifier streams. Both streams are literal segments of the single fair
tape consumed by the fixed source-to-estimator program. -/
theorem physical_probability (E : ActualEstimator) (S : Schedule)
    (R : PhysicalConcat.Producer) (Φ : ValidFormula) (ht : SourceTests D B Φ)
    (hfirst : V42RawSamplerJoin.precision (t10Graph D B Φ).vertices (S.gap Φ.val.variables)*
      V42RawSamplerJoin.reservation (t10Graph D B Φ).vertices (S.gap Φ.val.variables) ≤
        blockLength R (EncodedCNF.encode Φ.val))
    (hclass : V42JointEstimatorLaw.classifierLength E
      (Nat.clog 2 (t10Graph D B Φ).vertices) (S.gap Φ.val.variables) ≤
        blockLength R (EncodedCNF.encode Φ.val)) :
    (Unit4Shell.Definitions.uniformTape (carrierLength R (EncodedCNF.encode Φ.val))).prob
      (fun t => randomOutput D B E.classifier S R Φ
        (sourceCoefficient D B Φ) (sourceDeltaV D B Φ) (sourceZeta D B) ht (List.ofFn t) = [true]) =
    (sourceLaw D B (S.gap Φ.val.variables) E Φ).prob
      (fun z => sourceAccepts D B (S.gap Φ.val.variables) Φ ht E z.1 z.2) := by
  exact output_probability D B E S R Φ (sourceCoefficient D B Φ)
    (sourceDeltaV D B Φ) (sourceZeta D B) ht hfirst hclass (· = [true])
#print axioms physical_probability
end
end CurrentV43.RandomizedRate
