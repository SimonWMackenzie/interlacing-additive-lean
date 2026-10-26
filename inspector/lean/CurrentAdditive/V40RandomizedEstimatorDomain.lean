import CurrentAdditive.V40RandomizedSourceLaw

namespace CurrentAdditive.V40RandomizedETHEndpoint
noncomputable section
open Paper2 EthInapproximability.CurrentPaper
open V39PermittedNumericalExtraction

/-- Ordinary growing-error estimation on arbitrary sufficiently large
explicit total Boolean tables, using the permitted matrix-only input. -/
def GrowingAccuracy (A : PermittedEstimator) (c : ℝ) (T₀ : ℕ) : Prop :=
  ∀ (r s : ℕ) (f : Fin r → Fin s → Bool), 0 < r → 0 < s → T₀ ≤ r*s →
    (2:ℝ)/3 ≤ A.raw.prob (AModel.matrixWord r s (MatrixMaterialization.rowMajor f))
      (fun out => |A.value out-(Workspace.Types.CommComplexity.D f:ℝ)| ≤ growingError c (r*s))

theorem growingSquareAccuracy_of_growingAccuracy (A : PermittedEstimator)
    (c : ℝ) (T₀ : ℕ) (hA : GrowingAccuracy A c T₀) :
    GrowingSquareAccuracy A c T₀ := by
  intro m f hm hpower hT
  simpa only [pow_two] using hA m m f hm hm (by simpa only [pow_two] using hT)

#print axioms growingSquareAccuracy_of_growingAccuracy
end
end CurrentAdditive.V40RandomizedETHEndpoint
