import CurrentAdditive.V40DeterministicConcreteSource

/-! The actual unrestricted deterministic growing-error ETH endpoint.
The constructor, request, comparator and complete clock are concrete
instantiations; none is a premise of these final class theorems. -/
namespace CurrentAdditive.V40DeterministicETHEndpoint
noncomputable section
open Paper2 EthInapproximability.CurrentPaper
open EncodedETHSource EncodedETHSourceComposition Unit4Shell.T10Finite
open V39CurrentSourceJoin V39RuntimeETHNumerics V39PermittedDeterministicExtraction
set_option maxHeartbeats 4000000
set_option maxRecDepth 32768

variable (D : DinurReduction) (B : BOTReduction (booleanOccurrence D))

def constructionError : ℝ := errorCoefficient (constructionAmplification D B)

theorem constructionError_positive : 0<constructionError D B := by
  change 0<(errorCoefficient (constructionAmplification D B):ℝ)
  exact_mod_cast coefficient_positive (constructionAmplification D B) (constructionAmplification_ge D B)

def actualCutoff (A : PermittedDeterministicEstimator) (cs T₀ : ℕ)
    (hA : GrowingSquareAccuracy A (constructionError D B) T₀) :=
  semanticCutoff D B (constructionAmplification D B) (constructionExponent D B)
    (constructionAmplification_ge D B) (constructionExponent_ge D B) A cs T₀ hA

theorem actualCutoff_pos (A : PermittedDeterministicEstimator) (cs T₀ : ℕ)
    (hA : GrowingSquareAccuracy A (constructionError D B) T₀) : 1≤actualCutoff D B A cs T₀ hA :=
  le_max_left _ _

def actualAlgorithm (A : PermittedDeterministicEstimator) (cs T₀ : ℕ)
    (hA : GrowingSquareAccuracy A (constructionError D B) T₀) : DeterministicSparseETH.Algorithm :=
  sourcePipelineAlgorithm D B (V40DeterministicGraphConstructor.requestMachine (parameters D B))
    (constructionAmplification D B) (constructionExponent D B)
    (constructionAmplification_ge D B) (constructionExponent_ge D B) A cs T₀ hA
    (actualCutoff D B A cs T₀ hA) (actualCutoff_pos D B A cs T₀ hA) le_rfl
    (source_constructor_outputs D B)

theorem actualAlgorithm_runs (A : PermittedDeterministicEstimator) (cs T₀ : ℕ)
    (hA : GrowingSquareAccuracy A (constructionError D B) T₀) (w : List Bool) :
    (actualAlgorithm D B A cs T₀ hA).machine.OutputsWithin w
      [(actualAlgorithm D B A cs T₀ hA).answer w] ((actualAlgorithm D B A cs T₀ hA).time w) :=
  (actualAlgorithm D B A cs T₀ hA).run w

theorem actualAlgorithm_sparse (A : PermittedDeterministicEstimator) (cs T₀ : ℕ)
    (hA : GrowingSquareAccuracy A (constructionError D B) T₀) :
    DeterministicSparseETH.SparseDecider cs (actualAlgorithm D B A cs T₀ hA) :=
  sourcePipeline_sparse D B (V40DeterministicGraphConstructor.requestMachine (parameters D B))
    (constructionAmplification D B) (constructionExponent D B)
    (constructionAmplification_ge D B) (constructionExponent_ge D B) A cs T₀ hA
    (actualCutoff D B A cs T₀ hA) (actualCutoff_pos D B A cs T₀ hA) le_rfl
    (source_constructor_outputs D B)

theorem deterministic_growing_square_class (hETH : DeterministicSparseETH.Holds) :
    ¬ ∃ A : PermittedDeterministicEstimator, ∃ T₀ : ℕ,
      GrowingSquareAccuracy A (constructionError D B) T₀ := by
  rintro ⟨A,T₀,hA⟩
  apply DeterministicSparseETH.contradiction_of_decider hETH
  intro cs
  exact ⟨actualAlgorithm D B A cs T₀ hA,actualAlgorithm_sparse D B A cs T₀ hA⟩

theorem deterministic_growing_class (hETH : DeterministicSparseETH.Holds) :
    ¬ ∃ A : PermittedDeterministicEstimator, ∃ T₀ : ℕ,
      GrowingAccuracy A (constructionError D B) T₀ := by
  rintro ⟨A,T₀,hA⟩
  exact deterministic_growing_square_class D B hETH
    ⟨A,T₀,growingSquareAccuracy_of_growingAccuracy A _ T₀ hA⟩

include D B in
theorem deterministic_growing_hardness (hETH : DeterministicSparseETH.Holds) :
    ∃ c : ℝ, 0<c ∧ ¬ ∃ A : PermittedDeterministicEstimator, ∃ T₀ : ℕ,
      GrowingAccuracy A c T₀ :=
  ⟨constructionError D B,constructionError_positive D B,deterministic_growing_class D B hETH⟩

#print axioms actualAlgorithm_runs
#print axioms actualAlgorithm_sparse
#print axioms deterministic_growing_square_class
#print axioms deterministic_growing_class
#print axioms deterministic_growing_hardness
end
end CurrentAdditive.V40DeterministicETHEndpoint
