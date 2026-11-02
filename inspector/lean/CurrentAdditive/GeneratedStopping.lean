import CurrentAdditive.GeneratedAliceNode
import Paper2.ReferenceProjectionMass

/-!
One-coordinate Appendix I live-stop obstruction on the literal indexed
generated matrix. The retained inner source is a joint event of complete
labels; exact marginals are used only to lower-bound its image at the one
coordinate exposed by the selected diagonal.
-/

namespace CurrentAdditive.DeterministicIndexedMatrix.Sources

open Paper2 Paper2.SourceProjection Paper2.SourceMatrix
open Workspace.Types.CommComplexity Workspace.Types.Protocol

variable {X Y I : Type*} [Fintype X] [Fintype Y] [Fintype I]
  [DecidableEq X] [DecidableEq Y]
  {D q₁ q₂ s : ℕ} [NeZero s] [NeZero q₁] [NeZero q₂]
  {μX : PositiveRationalLaw X} {μY : PositiveRationalLaw Y}
  (src : Sources (D := D) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY)

theorem inner_coordinate_pushes (hD : 8 ≤ D) (α : Fin q₂) :
    src.inner.law.toFiniteLaw.PushesTo
      ((PositiveRationalLaw.uniform (Fin q₁)).prod μX).toFiniteLaw
      (fun z => src.inner.decode z α) := by
  intro E
  have h := CurrentAdditive.ArbitraryPrefix.exact_selected_of_eight
    src.inner.law.toFiniteLaw
    ((PositiveRationalLaw.uniform (Fin q₁)).prod μX).toFiniteLaw
    src.inner.decode (inner_eightwise src hD) (by omega)
    (fun _ : Fin 1 => α) (by intro i j _; fin_cases i; fin_cases j; rfl)
    (fun v => E (v 0))
  simpa only [Paper2.ReferenceProjectionMass.iid_one_coordinate_prob] using h

theorem indexed_coordinate_cost
    (hD : 8 ≤ D) (R : X → Y → Bool)
    (activity : I → Fin q₂ → Option (Fin s)) (ξ₀ : Tail s Y)
    (H : ℕ) (x : ℝ)
    (hprofile : RestrictionProfile (A src R)
      src.gamma.law.toFiniteLaw
      ((PositiveRationalLaw.uniform (Fin q₁)).prod μX).toFiniteLaw
      x (H : ℤ))
    (p : Fin s) (α : Fin q₂) (K : Set src.inner.Label)
    (W : Set src.gamma.Label)
    (U : Set (Column src)) (V : Set (Row (I := I) src))
    (hK : ∀ z ∈ K, Sum.inl (p, z) ∈ V)
    (hW : ∀ γ ∈ W, Column.diagonal (α, γ) ∈ U)
    (hKmass : (3/5 : ℝ) ≤ src.inner.law.toFiniteLaw.prob (· ∈ K))
    (hWmass : x ≤ src.gamma.law.toFiniteLaw.prob (· ∈ W)) :
    H ≤ Paper2.Compression.restrictionD (N src R activity ξ₀) U V := by
  classical
  let projection : src.inner.Label → Fin q₁ × X :=
    fun z => src.inner.decode z α
  let F : src.gamma.Label → src.inner.Label → Bool :=
    fun γ z => N src R activity ξ₀ (.diagonal (α, γ)) (.inl (p, z))
  have himage : (3/5 : ℝ) ≤
      ((PositiveRationalLaw.uniform (Fin q₁)).prod μX).toFiniteLaw.prob
        (· ∈ projection '' K) :=
    hKmass.trans (FiniteLaw.prob_le_image _ _ _
      (inner_coordinate_pushes src hD α) K)
  have hfirst := (restrictionProfile_three_levels _ _ _ _ _).mp hprofile |>.1
  have hprofileCost := hfirst W (projection '' K) hWmass himage
  have hnat : H ≤ Paper2.Compression.restrictionD (A src R) W
      (projection '' K) := by exact_mod_cast hprofileCost
  have hentry : ∀ γ ∈ W, ∀ z ∈ K,
      F γ z = A src R γ (projection z) := by
    intro γ _ z _
    rfl
  have hp := restrictionD_projected_le F (A src R) id projection
    W K W (fun _ h => h) hentry
  have hm := restrictionD_map_le (N src R activity ξ₀)
    (fun γ : src.gamma.Label => Column.diagonal (α, γ))
    (fun z : src.inner.Label => Sum.inl (p, z))
    U V W K hW hK
  exact hnat.trans (hp.trans hm)

end CurrentAdditive.DeterministicIndexedMatrix.Sources

#print axioms CurrentAdditive.DeterministicIndexedMatrix.Sources.inner_coordinate_pushes
#print axioms CurrentAdditive.DeterministicIndexedMatrix.Sources.indexed_coordinate_cost
