import Paper2.SourceProjection
import Paper2.RationalRowEstimates

/-!
# Several diagonal supports in the retained source matrix

Frozen v12 Section 4, `src:near-full`, the capacity argument after the first
Alice message in the remaining conversation. Retained full words map to
their actual diagonal tags. Retained templates are projected jointly, with
the same original representative used for every word. This module supplies
the concrete matrix maps and capacity calls; it does not construct the
stopping frontier or assume that its supports have already been found.
-/

namespace Paper2.SourceSupportProjection

open SourceMatrix SourceProjection Workspace.Types.CommComplexity

variable {X Y I : Type*} [Fintype X] [Fintype Y] [Fintype I]
variable {q₁ q₂ s k : ℕ} [NeZero s]

/-- A joint family of retained diagonal words and retained templates is
literally a restriction of `M₂`, inside the original retained source. -/
theorem diagonal_outer_D_le (R : X → Y → Bool)
    (activity : I → Fin q₂ → Option (Fin s)) (ξ₀ : Tail s Y)
    (p : Fin s) (A : Set (Template q₁ q₂ X))
    (J : Set (OuterColumn q₁ q₂ s Y))
    (U : Set (TaggedColumn q₁ q₂ s Y)) (V : Set (RawRow q₁ q₂ s X I))
    (hA : ∀ z ∈ A, Sum.inl (p, z) ∈ V)
    (hJ : ∀ a ∈ J, TaggedColumn.diagonal a ∈ U) :
    Compression.restrictionD (M₂ R) J A ≤
      Compression.restrictionD (N R activity ξ₀) U V :=
  restrictionD_map_le (N R activity ξ₀) TaggedColumn.diagonal
    (fun z => Sum.inl (p, z)) U V J A hJ hA

/-- Selected diagonal coordinates expose the actual interlace of `M₁ᵀ`.
The common column set is the image of whole surviving templates, not a
product assembled from separate coordinate images. -/
theorem selected_diagonal_D_le (R : X → Y → Bool)
    (activity : I → Fin q₂ → Option (Fin s)) (ξ₀ : Tail s Y)
    (p : Fin s) (e : Fin k → Fin q₂) (A : Set (Template q₁ q₂ X))
    (S : Set (Fin k × Word q₁ s Y))
    (U : Set (TaggedColumn q₁ q₂ s Y)) (V : Set (RawRow q₁ q₂ s X I))
    (hA : ∀ z ∈ A, Sum.inl (p, z) ∈ V)
    (hS : ∀ a ∈ S, TaggedColumn.diagonal (e a.1, a.2) ∈ U) :
    Compression.restrictionD (fullInterlace (fun γ j => M₁ R j γ) k)
      S (templateProjection e '' A) ≤
      Compression.restrictionD (N R activity ξ₀) U V :=
  (M₂_projection_D_le R e (TaggedColumn.diagonal ⁻¹' U) A S hS).trans
    (diagonal_outer_D_le R activity ξ₀ p A (TaggedColumn.diagonal ⁻¹' U)
      U V hA (fun _ h => h))

/-- The power-of-two capacity estimate on these same retained inputs.
The base profile is the word-versus-inner-row profile of `M₁ᵀ`; its
construction from the seed profile is proved separately in `SourceProfiles`.
No communication lower bound for this retained source is assumed. -/
theorem selected_capacity_power [NeZero q₁]
    (μ : PositiveRationalLaw X) (ν : PositiveRationalLaw Y)
    (R : X → Y → Bool) (activity : I → Fin q₂ → Option (Fin s)) (ξ₀ : Tail s Y)
    (H l : ℕ) {x : ℝ} (hH : 2 ≤ H) (hx : 0 < x) (hl : 2 ≤ l)
    (hscale : (2 : ℝ) ^ l * x ≤ 1)
    (hprofile : RestrictionProfile (fun (γ : Word q₁ s Y) j => M₁ R j γ)
      (ν.iid (q₁ + s + 1)).toFiniteLaw
      ((PositiveRationalLaw.uniform (Fin q₁)).prod μ).toFiniteLaw x (H : ℤ))
    (p : Fin s) (e : Fin k → Fin q₂) (he : Function.Injective e)
    (A : Set (Template q₁ q₂ X)) (S : Set (Fin k × Word q₁ s Y))
    (Q : Finset (Fin k)) (hQ : 2 ^ (l - 1) + 1 ≤ Q.card)
    (U : Set (TaggedColumn q₁ q₂ s Y)) (V : Set (RawRow q₁ q₂ s X I))
    (hA : ∀ z ∈ A, Sum.inl (p, z) ∈ V)
    (hS : ∀ a ∈ S, TaggedColumn.diagonal (e a.1, a.2) ∈ U)
    (hrow : ∀ i ∈ Q, (2 : ℝ) ^ l * x ≤
      (ν.iid (q₁ + s + 1)).toFiniteLaw.prob (fun γ => (i, γ) ∈ S))
    (hcol : (9 / 25 : ℝ) ≤ (SourceLaws.templateLaw μ q₁ q₂).toFiniteLaw.prob (· ∈ A)) :
    H + l ≤ Compression.restrictionD (N R activity ξ₀) U V := by
  classical
  have hc := hcol.trans (template_projection_mass μ e he A)
  have hh := RationalRowEstimates.small_capacity_power (ν.iid (q₁ + s + 1))
    ((PositiveRationalLaw.uniform (Fin q₁)).prod μ)
    (fun (γ : Word q₁ s Y) j => M₁ R j γ) H l k hH hx hl hscale hprofile
    Q hQ S.toFinset (templateProjection e '' A).toFinset
    (fun i hi => by simpa only [Set.mem_toFinset] using hrow i hi)
    (by simpa only [SourceLaws.templateLaw, PositiveRationalLaw.toFiniteLaw_iid,
      Set.mem_toFinset] using hc)
  change H + l ≤ Compression.restrictionD
    (fullInterlace (fun (γ : Word q₁ s Y) j => M₁ R j γ) k)
    (S.toFinset : Set _) ((templateProjection e '' A).toFinset : Set _) at hh
  simp only [Set.coe_toFinset] at hh
  exact hh.trans (selected_diagonal_D_le R activity ξ₀ p e A S U V hA hS)

/-- The two-coordinate capacity estimate, including the small dyadic
cases. Two actual supported coordinates are required; one does not suffice. -/
theorem selected_capacity_two [NeZero q₁]
    (μ : PositiveRationalLaw X) (ν : PositiveRationalLaw Y)
    (R : X → Y → Bool) (activity : I → Fin q₂ → Option (Fin s)) (ξ₀ : Tail s Y)
    (H : ℕ) {x : ℝ} (hH : 2 ≤ H) (hx : 0 < x) (hscale : 2 * x ≤ 1)
    (hprofile : RestrictionProfile (fun (γ : Word q₁ s Y) j => M₁ R j γ)
      (ν.iid (q₁ + s + 1)).toFiniteLaw
      ((PositiveRationalLaw.uniform (Fin q₁)).prod μ).toFiniteLaw x (H : ℤ))
    (p : Fin s) (e : Fin k → Fin q₂) (he : Function.Injective e)
    (A : Set (Template q₁ q₂ X)) (S : Set (Fin k × Word q₁ s Y))
    (Q : Finset (Fin k)) (hQ : 2 ≤ Q.card)
    (U : Set (TaggedColumn q₁ q₂ s Y)) (V : Set (RawRow q₁ q₂ s X I))
    (hA : ∀ z ∈ A, Sum.inl (p, z) ∈ V)
    (hS : ∀ a ∈ S, TaggedColumn.diagonal (e a.1, a.2) ∈ U)
    (hrow : ∀ i ∈ Q, 2 * x ≤
      (ν.iid (q₁ + s + 1)).toFiniteLaw.prob (fun γ => (i, γ) ∈ S))
    (hcol : (9 / 25 : ℝ) ≤ (SourceLaws.templateLaw μ q₁ q₂).toFiniteLaw.prob (· ∈ A)) :
    H + 1 ≤ Compression.restrictionD (N R activity ξ₀) U V := by
  classical
  have hc := hcol.trans (template_projection_mass μ e he A)
  have hh := RationalRowEstimates.small_capacity_two (ν.iid (q₁ + s + 1))
    ((PositiveRationalLaw.uniform (Fin q₁)).prod μ)
    (fun (γ : Word q₁ s Y) j => M₁ R j γ) H k hH hx hscale hprofile
    Q hQ S.toFinset (templateProjection e '' A).toFinset
    (fun i hi => by simpa only [Set.mem_toFinset] using hrow i hi)
    (by simpa only [SourceLaws.templateLaw, PositiveRationalLaw.toFiniteLaw_iid,
      Set.mem_toFinset] using hc)
  change H + 1 ≤ Compression.restrictionD
    (fullInterlace (fun (γ : Word q₁ s Y) j => M₁ R j γ) k)
    (S.toFinset : Set _) ((templateProjection e '' A).toFinset : Set _) at hh
  simp only [Set.coe_toFinset] at hh
  exact hh.trans (selected_diagonal_D_le R activity ξ₀ p e A S U V hA hS)

end Paper2.SourceSupportProjection

#print axioms Paper2.SourceSupportProjection.diagonal_outer_D_le
#print axioms Paper2.SourceSupportProjection.selected_diagonal_D_le
#print axioms Paper2.SourceSupportProjection.selected_capacity_power
#print axioms Paper2.SourceSupportProjection.selected_capacity_two
