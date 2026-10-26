import CurrentAdditive.V39SourceProfiles

/-!
The recovered literal diagonal/template projection, now imported through
the actual two-threshold source packet rather than the obsolete-profile
recovery packet. This is a submatrix theorem, not the final collision bound.
-/

namespace CurrentAdditive.V39DiagonalProjection

open Workspace.Types.CommComplexity Paper2
open CurrentAdditive.EdgeSourceMatrix CurrentAdditive.V38Matrix

variable {V E X Y : Type*} [Fintype V] [Fintype E] [Fintype X] [Fintype Y]
variable {s q₁ q₂ : ℕ} [NeZero s]

theorem diagonal_template_restriction
    (order : Items s V ≃ Fin (Fintype.card (Items s V)))
    (edge : E → Bool → V) (hs : 3 ≤ s) (r : ℕ)
    (hq : q₂=EdgeSource.sourceQ0 (Fin (4*s)) E*r)
    (R : X → Y → Bool) (ξ₀ : SourceMatrix.Tail s Y)
    (p : Fin s) (α : Fin q₂)
    (A : Set (SourceMatrix.Template q₁ q₂ X))
    (K : Set (SourceMatrix.Word q₁ s Y))
    (W : Set (TaggedColumn q₁ q₂ s Y))
    (U : Set (SourceMatrix.RawRow q₁ q₂ s X (Items s V)))
    (hA : ∀ z ∈ A, Sum.inl (p,z) ∈ U)
    (hK : ∀ γ ∈ K, Sum.inr (α,γ) ∈ W) :
    Compression.restrictionD (SourceMatrix.M₁ R) ((fun z => z α) '' A) K ≤
      Compression.restrictionD (V38Matrix.matrix order edge hs r hq R ξ₀) W U := by
  let F : SourceMatrix.Word q₁ s Y → SourceMatrix.Template q₁ q₂ X → Bool :=
    fun γ z => V38Matrix.matrix order edge hs r hq R ξ₀ (.inr (α,γ)) (.inl (p,z))
  have hp := SourceProjection.restrictionD_projected_le F
    (fun γ j => SourceMatrix.M₁ R j γ) id (fun z => z α)
    K A K (fun _ h => h) (fun _ _ _ _ => rfl)
  rw [SourceProjection.restrictionD_transpose (SourceMatrix.M₁ R)] at hp
  exact hp.trans (SourceProjection.restrictionD_map_le
    (V38Matrix.matrix order edge hs r hq R ξ₀)
    (fun γ => Sum.inr (α,γ)) (fun z => Sum.inl (p,z))
    W U K A hK hA)

#print axioms diagonal_template_restriction

end CurrentAdditive.V39DiagonalProjection
