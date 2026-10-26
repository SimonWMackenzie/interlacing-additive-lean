import CurrentAdditive.GeneratedTwoStreamOrdinaryOriginal
import Paper2.TwoStreamPairedCapacity

/-! The attached paired family in the actual generated two-stream matrix. -/

namespace CurrentAdditive.DeterministicIndexedMatrix.Sources

open Paper2 Paper2.SourceProjection Paper2.PairedSelectorMatrix
open Paper2.PairedSelectorPopulation Workspace.Types.CommComplexity

variable {X Y Rw F E : Type*}
  [Fintype X] [Fintype Y] [Fintype Rw] [Nonempty Rw] [Fintype F] [Fintype E]
  [DecidableEq X] [DecidableEq Y]
  {D q₁ q₂ s : ℕ} [NeZero s] [NeZero q₁] [NeZero q₂]
  {μX : PositiveRationalLaw X} {μY : PositiveRationalLaw Y}
  (src : Sources (D := D) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY)

/-- The actual indexed pair matrix is a restriction of any original
two-stream matrix with the source's prescribed pointwise entries. The
retained pair event stays joint, and all column representatives are fixed
before a row is read. -/
theorem paired_original_D_le
    (R₀ : X → Y → Bool)
    (M : Rw → ((src.outer.Label × src.gamma.Label) ⊕ F) → Bool)
    (bin : Rw → Fin s) (selector : Rw → src.inner.Label)
    (ψ : F → J src) (star : Fin s)
    (ι : E → Rw) (ζ : E → src.inner.Label × src.inner.Label)
    (hordinary : ∀ r c, M r (.inl c) =
      T src R₀ (selector r) (src.outer.decode c.1 (bin r)))
    (P : Set E) (R : Set Rw)
    (O : Set (src.outer.Label × src.gamma.Label)) (G : Set F)
    (hstar : ∀ a ∈ P, bin (ι a) = star ∧ selector (ι a) = (ζ a).1)
    (hforeign : ∀ a ∈ P, ∀ f,
      M (ι a) (.inr f) = T src R₀ (ζ a).2 (ψ f))
    (hι : ∀ a ∈ P, ι a ∈ R) :
    Compression.restrictionD
        (fun z c => pairedIndexed src R₀ z (c.1.1, (c.1.2, c.2)))
        (ζ '' P)
        (columns ((fun c => src.outer.decode c.1 star) '' O) (ψ '' G)) ≤
      Compression.restrictionD M R
        ((Sum.inl '' O) ∪ (Sum.inr '' G)) := by
  classical
  let C : Set ((src.outer.Label × src.gamma.Label) ⊕ F) :=
    (Sum.inl '' O) ∪ (Sum.inr '' G)
  let φ : ((src.outer.Label × src.gamma.Label) ⊕ F) →
      Paper2.PairedSelectorMatrix.Column q₂ src.gamma.Label :=
    Paper2.TwoStreamPairedCapacity.columnProjection
      (fun c i => src.outer.decode c.1 i) ψ star
  have hC : φ '' C =
      columns ((fun c => src.outer.decode c.1 star) '' O) (ψ '' G) :=
    Paper2.TwoStreamPairedCapacity.columnProjection_image
      (fun c i => src.outer.decode c.1 i) ψ star O G
  -- Use a total row map with an arbitrary fallback away from the retained image.
  let f : (src.inner.Label × src.inner.Label) → Rw :=
    fun z => if hz : z ∈ ζ '' P then
      ι (representative ζ P ⟨z, hz⟩).val else Classical.choice inferInstance
  have hf : ∀ z ∈ ζ '' P, f z ∈ R := by
    intro z hz
    simpa only [f, dif_pos hz] using
      hι (representative ζ P ⟨z, hz⟩).val
        (representative ζ P ⟨z, hz⟩).property
  have hentry : ∀ z ∈ ζ '' P, ∀ c ∈ C,
      M (f z) c = pairedIndexed src R₀ z
        ((φ c).1.1, ((φ c).1.2, (φ c).2)) := by
    intro z hz c hc
    have hzmap := representative_maps ζ P ⟨z, hz⟩
    change ζ (representative ζ P ⟨z, hz⟩).val = z at hzmap
    rcases hc with ⟨o, ho, rfl⟩ | ⟨g, hg, rfl⟩
    · change M (f z) (.inl o) = _
      dsimp only [f]
      rw [dif_pos hz]
      rw [hordinary, (hstar _ (representative ζ P ⟨z, hz⟩).property).1,
        (hstar _ (representative ζ P ⟨z, hz⟩).property).2]
      exact (congrArg
        (fun zz : src.inner.Label × src.inner.Label =>
          T src R₀ zz.1 (src.outer.decode o.1 star)) hzmap).trans
        (by rfl)
    · change M (f z) (.inr g) = _
      dsimp only [f]
      rw [dif_pos hz]
      rw [hforeign _ (representative ζ P ⟨z, hz⟩).property]
      exact (congrArg
        (fun zz : src.inner.Label × src.inner.Label => T src R₀ zz.2 (ψ g)) hzmap).trans
        (by rfl)
  have h := restrictionD_projected_le M
    (fun z c => pairedIndexed src R₀ z (c.1.1, (c.1.2, c.2)))
    f φ R C (ζ '' P) hf hentry
  simpa only [hC] using h

/-- The generated paired obstruction is paid by a surviving attached
two-stream row family, on the original matrix and original source laws. -/
theorem paired_original_parent_lower
    (R₀ : X → Y → Bool)
    (M : Rw → ((src.outer.Label × src.gamma.Label) ⊕ F) → Bool)
    (bin : Rw → Fin s) (selector : Rw → src.inner.Label)
    (ψ : F → J src) (star : Fin s)
    (ι : E → Rw) (ζ : E → src.inner.Label × src.inner.Label)
    (hordinary : ∀ r c, M r (.inl c) =
      T src R₀ (selector r) (src.outer.decode c.1 (bin r)))
    (P : Set E) (R : Set Rw)
    (O : Set (src.outer.Label × src.gamma.Label)) (G : Set F)
    (hstar : ∀ a ∈ P, bin (ι a) = star ∧ selector (ι a) = (ζ a).1)
    (hforeign : ∀ a ∈ P, ∀ f,
      M (ι a) (.inr f) = T src R₀ (ζ a).2 (ψ f))
    (hι : ∀ a ∈ P, ι a ∈ R)
    (H ell : ℕ) (hH : 2 ≤ H) (hq : q₂ = 2^ell)
    (x : ℝ) (hx : 0 < x) (hD : 8 ≤ D)
    (hprofile : RestrictionProfile (A src R₀)
      src.gamma.law.toFiniteLaw
      ((PositiveRationalLaw.uniform (Fin q₁)).prod μX).toFiniteLaw
      x (H : ℤ))
    (ε δ : ℝ)
    (hK : (49/64 : ℝ) ≤
      (src.inner.law.toFiniteLaw.prod src.inner.law.toFiniteLaw).prob
        (· ∈ ζ '' P))
    (hO : 1-ε ≤
      (Paper2.PairedSelectorPopulation.columnLaw src.gamma.law).toFiniteLaw.prob
        (· ∈ (fun c => src.outer.decode c.1 star) '' O))
    (hF : δ ≤
      (Paper2.PairedSelectorPopulation.columnLaw src.gamma.law).toFiniteLaw.prob
        (· ∈ ψ '' G))
    (hδpos : 0 < δ) (hδ : δ ≤ 1)
    (hsmall : 2*q₂*x ≤ 1/8)
    (hslack : 2*q₂*x + 5*ε + 2/q₂ ≤ δ) :
    H+ell+1 ≤ Compression.restrictionD M R
      ((Sum.inl '' O) ∪ (Sum.inr '' G)) := by
  have hl := paired_restriction_lower src R₀ H ell hH hq x hx hD
    hprofile (ζ '' P)
    ((fun c => src.outer.decode c.1 star) '' O) (ψ '' G)
    ε δ hK hO hF hδpos hδ hsmall hslack
  exact hl.trans (paired_original_D_le src R₀ M bin selector ψ star ι ζ
    hordinary P R O G hstar hforeign hι)

#print axioms paired_original_D_le
#print axioms paired_original_parent_lower

end CurrentAdditive.DeterministicIndexedMatrix.Sources
