import CurrentAdditive.DeterministicIndexedTemplates

/-! Appendix I `det:profiles` entry alignment. The reference matrix is the
ordinary indexed restriction of N. This does not assert a lower profile. -/

namespace CurrentAdditive.DeterministicIndexedMatrix

open Paper2 Paper2.SourceMatrix

variable {I X Y : Type*} [Fintype I] [Fintype X] [Fintype Y]
  [DecidableEq X] [DecidableEq Y]
  {D q₁ q₂ s : ℕ} [NeZero s] [NeZero q₁] [NeZero q₂]
  {μX : PositiveRationalLaw X} {μY : PositiveRationalLaw Y}
  (src : Sources (D := D) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY)

namespace Sources

/-- The manuscript's N_ref is the normalized ordinary-row restriction of N.
Its ordinary law is the already constructed `ordinaryLaw src`. -/
def Nref (R : X → Y → Bool)
    (activity : I → Fin q₂ → Option (Fin s)) (ξ₀ : Tail s Y) :
    (src.outer.Label × src.gamma.Label) → Row (I := I) src → Bool :=
  fun Z k => N src R activity ξ₀ (.ordinary Z) k

@[simp] theorem Nref_template (R : X → Y → Bool)
    (activity : I → Fin q₂ → Option (Fin s)) (ξ₀ : Tail s Y)
    (js : src.outer.Label) (γ : src.gamma.Label)
    (p : Fin s) (z : src.inner.Label) :
    Nref src R activity ξ₀ (js, γ) (.inl (p, z)) =
      T src R z (src.outer.decode js p) := rfl

@[simp] theorem Nref_source (R : X → Y → Bool)
    (activity : I → Fin q₂ → Option (Fin s)) (ξ₀ : Tail s Y)
    (js : src.outer.Label) (γ : src.gamma.Label)
    (i : I) (u : X) :
    Nref src R activity ξ₀ (js, γ) (.inr (i, u)) =
      R u (sourceColumn activity i
        (decodeColumn src ξ₀ (.ordinary (js, γ)))) := rfl

end Sources

end CurrentAdditive.DeterministicIndexedMatrix
