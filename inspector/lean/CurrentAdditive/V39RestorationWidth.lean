import CurrentAdditive.V39TwoThresholdRestoration

namespace CurrentAdditive.V39TwoThresholdRestoration

open Paper2 CurrentAdditive.DeterministicIndexedMatrix Workspace.Types.CommComplexity

/-- Keep the actual supplied width and source labels; power-of-two width is
an equality, not a replacement source or a separate chosen construction. -/
theorem restored_width
    {X Z : Type*} [Fintype X] [Fintype Z] [DecidableEq X] [DecidableEq Z]
    (μ : PositiveRationalLaw X) (ν : PositiveRationalLaw Z)
    (F : X → Z → Bool) (Q r C : ℕ) (θ φ δ : ℝ)
    [NeZero Q] (src : CodeSource 8192 Q Z ν) (hQr : Q=2^r)
    (hC : 3 ≤ C) (hD : D F=C) (hθ : 0 < θ) (hφ : 0 < φ) (hφ1 : φ ≤ 1)
    (hδ : 0 < δ)
    (hQ : 128*((V38Moments.exceptionCount φ (δ/2):ℝ)+1) ≤ Q)
    (hθQ : (Q:ℝ)*θ ≤ 1/20)
    (hnear : ∀ A : Set X, ∀ B : Set Z,
      θ ≤ μ.toFiniteLaw.prob (· ∈ A) → 1-δ ≤ ν.toFiniteLaw.prob (· ∈ B) →
      C ≤ Compression.restrictionD F A B)
    (hp : V38RestrictionProfiles.TwoThresholdProfile F μ.toFiniteLaw ν.toFiniteLaw
      θ ((C-1:ℕ):ℤ)) :
    D (fun (seed : src.Label) (a : Fin Q × X) => F a.2 (src.decode seed a.1)) = C+r ∧
    V38RestrictionProfiles.TwoThresholdProfile
      (fun (seed : src.Label) (a : Fin Q × X) => F a.2 (src.decode seed a.1))
      src.law.toFiniteLaw ((PositiveRationalLaw.uniform (Fin Q)).prod μ).toFiniteLaw
      φ ((C+r:ℕ):ℤ) := by
  subst Q
  exact restored μ ν F r C θ φ δ src hC hD hθ hφ hφ1 hδ hQ hθQ hnear hp

end CurrentAdditive.V39TwoThresholdRestoration
