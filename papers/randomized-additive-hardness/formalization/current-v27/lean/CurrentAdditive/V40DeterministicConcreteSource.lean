import CurrentAdditive.V40DeterministicGraphConstructor
import CurrentAdditive.V40DeterministicPipelineClock
import CurrentAdditive.V40DeterministicEstimatorDomain

/-! Concrete instantiation of the source-run interface from the actual
whole graph constructor. This file has no supplied run or clock premise. -/
namespace CurrentAdditive.V40DeterministicETHEndpoint
noncomputable section
open Paper2 V38Schedule EthInapproximability.CurrentPaper
open EncodedETHSource EncodedETHSourceComposition Unit4Shell.T10Finite
open V39CurrentSourceJoin V39RuntimeETHNumerics V39FramedNumerical
open V39PermittedDeterministicExtraction V40DeterministicSourcePack
set_option maxHeartbeats 5000000
set_option maxRecDepth 32768

variable (D : DinurReduction) (B : BOTReduction (booleanOccurrence D))

def constructionAmplification := V40DeterministicGraphConstructor.amplification (parameters D B)
def constructionExponent := V40DeterministicGraphConstructor.requestExponent (parameters D B)

theorem constructionAmplification_ge : 2^64≤constructionAmplification D B :=
  V40DeterministicGraphConstructor.amplification_ge (parameters D B)

theorem constructionExponent_ge : 1040≤constructionExponent D B :=
  V40DeterministicGraphConstructor.requestExponent_ge (parameters D B)

theorem source_constructor_outputs (Φ : ValidFormula) (k : ℕ) :
    (V40DeterministicGraphConstructor.requestMachine (parameters D B)).OutputsWithin
      (graphInput (t10Graph D B Φ) Φ.val.variables k) (sourceRequest D B Φ k)
      (sourceRequestClock D B (constructionAmplification D B) (constructionExponent D B) Φ k) := by
  have h:=V40DeterministicGraphConstructor.request_outputs (parameters D B)
    (t10Graph D B Φ) (t10Graph_valid D B Φ) Φ.val.variables k
    (source_geometry D B Φ).1 (source_geometry D B Φ).2.1 (source_geometry D B Φ).2.2
  exact h

theorem source_request_fixed_outputs (k : ℕ) (Φ : ValidFormula) :
    (V40DeterministicGraphConstructor.requestMachine (parameters D B)).OutputsWithin
      (graphInput (t10Graph D B Φ) Φ.val.variables k) (sourceRequest D B Φ k)
      (((graphInput (t10Graph D B Φ) Φ.val.variables k).length+1)^
        V40DeterministicGraphConstructor.requestPolynomialDegree (parameters D B) k) := by
  exact V40DeterministicGraphConstructor.request_outputs_fixed_round (parameters D B) k
    (t10Graph D B Φ) (t10Graph_valid D B Φ) Φ.val.variables
    (source_geometry D B Φ).1 (source_geometry D B Φ).2.1 (source_geometry D B Φ).2.2

theorem source_rectangle_fixed_outputs (k : ℕ) (w : List Bool) :
    (V40DeterministicGraphConstructor.rectangleMachine (parameters D B)).OutputsWithin
      (graphInput (t10Graph D B (fixedFormula w)) (fixedFormula w).val.variables k)
      (EncodedCommunication.encodeInstance (V40DeterministicFixedGap.instanceWord D B k w))
      (((graphInput (t10Graph D B (fixedFormula w)) (fixedFormula w).val.variables k).length+1)^
        V40DeterministicGraphConstructor.rectanglePolynomialDegree (parameters D B) k) := by
  let Φ:=fixedFormula w
  exact V40DeterministicGraphConstructor.rectangle_outputs_fixed_round (parameters D B) k
    (t10Graph D B Φ) (t10Graph_valid D B Φ) Φ.val.variables
    (source_geometry D B Φ).1 (source_geometry D B Φ).2.1 (source_geometry D B Φ).2.2

#print axioms source_constructor_outputs
#print axioms source_request_fixed_outputs
#print axioms source_rectangle_fixed_outputs
end
end CurrentAdditive.V40DeterministicETHEndpoint
