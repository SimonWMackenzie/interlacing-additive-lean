import CurrentV43.Randomized.Algorithm
import CurrentV43.Randomized.Clock
import CurrentV43.PowerSchedulePaid
import CurrentV43.ResourceFit
import CurrentV43.Parametric.Resource

namespace CurrentV43.RandomizedRate
noncomputable section
open CurrentAdditive ParametricSource
open Paper2 EthInapproximability.CurrentPaper
open EncodedETHSource EncodedETHSourceComposition
open Unit4Shell.T10Finite Unit4Shell.Asymptotics
open V42RandomizedETHEndpoint V39PermittedNumericalExtraction V39ActualOutputMajority
open CurrentAdditive.V43RandomizedRate
set_option maxHeartbeats 4000000
set_option maxRecDepth 32768
set_option synthInstance.maxSize 32768

/-- The rational exponent is fixed in the finite program. All operations
that compute its dyadic iteration count are actual unary machine routines. -/
def rationalSchedule (a b : ℕ) : Schedule where
  gap := iterations a b
  producer := PhysicalProducer.localProducer (V43PowerSchedule.formula a b)
  correct Φ := V43PowerSchedule.formula_result a b Φ.val
  paid := V43PowerSchedule.formula_paid a b

variable (D : DinurReduction) (B : BOTReduction (booleanOccurrence D))

def resource (C : SelectedTape.Algorithm) (a b : ℕ) :=
  resourceProducer (rationalSchedule a b) (ResourceFit.resourceExponent D B C)

/-- Every physically requested sampler and classifier bit fits inside the
actual resource word printed by the finite program. -/
theorem concrete_resources (C : SelectedTape.Algorithm) (a b : ℕ)
    (Φ : ValidFormula) (ht : SourceTests D B Φ) :
    resources D B C (rationalSchedule a b) (resource D B C a b) Φ ht := by
  let S := rationalSchedule a b
  have hfit := ResourceFit.actual_tapes_fit D B C S Φ
    (sourceCoefficient D B Φ) (sourceDeltaV D B Φ) (sourceZeta D B) ht
  have hb := resource_le_block (resource D B C a b) (EncodedCNF.encode Φ.val)
  change ((resourceProducer S (ResourceFit.resourceExponent D B C)).result (EncodedCNF.encode Φ.val)).length ≤ _ at hb
  rw [resource_length] at hb
  refine ⟨hfit.1.trans hb,?_⟩
  intro tape
  exact (hfit.2 (sampledBits D B S Φ tape)).trans hb

/-- One fixed concrete algorithm, including the finite-exception router,
physical iteration printer, source graph, rounded table sampler, amplified
estimator and both paid fair-bit streams. -/
def algorithm (E : ActualEstimator) (a b cs cutoff : ℕ) (hcutoff : 1 ≤ cutoff)
    (hsource : V42SourceGeometry.originalCutoff D B (cs+2) ≤ cutoff) :
    FairBitAlgorithm.Algorithm :=
  routedAlgorithm D B E.classifier (rationalSchedule a b) (resource D B E.classifier a b)
    cs cutoff hcutoff hsource (fun w => concrete_resources D B E.classifier a b
      (routedSource cs cutoff hcutoff w) (routedTests D B cs cutoff hcutoff hsource w))

#print axioms rationalSchedule
#print axioms concrete_resources
#print axioms algorithm
end
end CurrentV43.RandomizedRate
