import CurrentAdditive.V40DeterministicFixedEstimator

/-! Ordinary unrestricted table estimation implies the dyadic-square
accuracy used by the actual deterministic source reduction. -/
namespace CurrentAdditive.V40DeterministicETHEndpoint
noncomputable section
open Paper2 EthInapproximability.CurrentPaper
open V39PermittedDeterministicExtraction

def GrowingAccuracy (A : PermittedDeterministicEstimator) (c : ℝ) (T₀ : ℕ) : Prop :=
  ∀ (r s : ℕ) (f : Fin r → Fin s → Bool), 0 < r → 0 < s → T₀ ≤ r*s →
    |A.value (A.output (AModel.matrixWord r s (MatrixMaterialization.rowMajor f)))-
      (Workspace.Types.CommComplexity.D f:ℝ)| ≤ c*Real.logb 2 (Real.logb 2 (r*s:ℕ))

def FixedAccuracy (A : PermittedDeterministicEstimator) (u : ℝ) : Prop :=
  ∀ (r s : ℕ) (f : Fin r → Fin s → Bool), 0 < r → 0 < s →
    |A.value (A.output (AModel.matrixWord r s (MatrixMaterialization.rowMajor f)))-
      (Workspace.Types.CommComplexity.D f:ℝ)| ≤ u

theorem growingSquareAccuracy_of_growingAccuracy (A : PermittedDeterministicEstimator)
    (c : ℝ) (T₀ : ℕ) (hA : GrowingAccuracy A c T₀) : GrowingSquareAccuracy A c T₀ := by
  intro m f hm hpower hT
  simpa only [pow_two] using hA m m f hm hm (by simpa only [pow_two] using hT)

theorem fixedSquareAccuracy_of_fixedAccuracy (A : PermittedDeterministicEstimator)
    (u : ℝ) (hA : FixedAccuracy A u) : FixedSquareAccuracy A u := by
  intro m f hm hpower
  exact hA m m f hm hm

#print axioms growingSquareAccuracy_of_growingAccuracy
#print axioms fixedSquareAccuracy_of_fixedAccuracy
end
end CurrentAdditive.V40DeterministicETHEndpoint
