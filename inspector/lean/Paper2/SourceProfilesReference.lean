import Paper2.SourceProfilesOuter
import Paper2.SourceProjectionRetention

/-!
# The reference source profile

Frozen v12 Section 4, `src:profiles`, third paragraph.  The source column
law is the actual protected mixture on graph-item labels.  Its template
mass is derived from that mixture, not introduced as an additional source
promise.  The activity map is arbitrary, since only template entries are
used by this lower bound.
-/

namespace Paper2.SourceProfilesReference

open Workspace.Types.CommComplexity
open SourceMatrix SourceProjection SourceProfilesInner SourceProfilesOuter
open SourceLawBinding SourceProjectionRetention

variable {X Y V : Type*} [Fintype X] [Fintype Y] [Fintype V] [Nonempty V]

/-- Conditional template mass forced by a retained source-column mass β. -/
noncomputable def templateThreshold (β : ℝ) : ℝ := (β - (1 - 255 / 256)) / (255 / 256)

theorem template_retained (μ : PositiveRationalLaw X) (q₁ q₂ s : ℕ)
    [NeZero q₁] [NeZero s] (hs : 4 ≤ s)
    (U : Set (RawRow q₁ q₂ s X (SourceConstruction.Items s V))) (β : ℝ)
    (hU : β ≤ (matrixColumnLaw μ q₁ q₂ s hs).toFiniteLaw.prob (· ∈ U)) :
    templateThreshold β ≤
      ((PositiveRationalLaw.uniform (Fin s)).prod
        (SourceLaws.templateLaw μ q₁ q₂)).toFiniteLaw.prob
        (fun r => Sum.inl r ∈ U) := by
  have h := (column_families_retained μ hs (· ∈ U) (1 - β) (by linarith)).1
  change 1 - (1 - β) / (255 / 256 : ℝ) ≤
    ((PositiveRationalLaw.uniform (Fin s)).prod
      (SourceLaws.templateLaw μ q₁ q₂)).toFiniteLaw.prob
      (fun r => Sum.inl r ∈ U) at h
  unfold templateThreshold
  linarith

theorem reference_rung
    (μ : PositiveRationalLaw X) (ν : PositiveRationalLaw Y)
    (R : X → Y → Bool) (q₁ q₂ s H a : ℕ)
    [NeZero q₁] [NeZero q₂] [NeZero s] (hs : 4 ≤ s)
    (activity : SourceConstruction.Items s V → Fin q₂ → Option (Fin s))
    (ξ₀ : Tail s Y) (hH : 3 ≤ H) (θ x β : ℝ)
    (hg : RungGuards s a θ x (templateThreshold β))
    (hp : RestrictionProfile (T (q₁ := q₁) (q₂ := q₂) (s := s) R)
      (SourceLaws.templateLaw μ q₁ q₂).toFiniteLaw
      (SourceLaws.outerLaw ν q₁ q₂ s).toFiniteLaw θ (H : ℤ)) :
    RestrictionLowerBound (fun Z r => N (q₁ := q₁) R activity ξ₀ (.unrestricted Z) r)
      (SourceLaws.rawLaw ν q₁ q₂ s).toFiniteLaw
      (matrixColumnLaw μ q₁ q₂ s hs).toFiniteLaw x β (H + a) := by
  intro W U hW hU
  have ht := template_retained μ q₁ q₂ s hs U β hU
  obtain ⟨e, he⟩ := select_blocks (SourceLaws.templateLaw μ q₁ q₂) s a θ x
    (templateThreshold β) hg {r | Sum.inl r ∈ U} ht
  let A : Set (Fin (StrongSeed.copies a) × Template q₁ q₂ X) :=
    {r | Sum.inl (e r.1, r.2) ∈ U}
  have hwords := hg.word_floor.trans (hW.trans (raw_projection_mass ν e e.injective W))
  rw [PositiveRationalLaw.toFiniteLaw_iid] at hwords
  have hlower := strong_member_sets (SourceLaws.templateLaw μ q₁ q₂)
    (SourceLaws.outerLaw ν q₁ q₂ s) (T R) H a hH hg.exponent θ
    hg.threshold_pos hg.scale_lt.le hp A (rawBinProjection e '' W) he hwords
  have hmap := reference_projection_D_le R activity ξ₀ e W U A (fun _ h => h)
  exact_mod_cast hlower.trans hmap

theorem reference_profile_of_outer
    (μ : PositiveRationalLaw X) (ν : PositiveRationalLaw Y)
    (R : X → Y → Bool) (q₁ q₂ s H a : ℕ)
    [NeZero q₁] [NeZero q₂] [NeZero s] (hs : 4 ≤ s)
    (activity : SourceConstruction.Items s V → Fin q₂ → Option (Fin s))
    (ξ₀ : Tail s Y) (hH : 3 ≤ H) (ha : 2 ≤ a) (θ x : ℝ)
    (hg : ∀ j : Fin 3, RungGuards s (a - j.val) θ x
      (templateThreshold ((3 / 5 : ℝ) * (1 / 2 : ℝ) ^ j.val)))
    (hp : RestrictionProfile (T (q₁ := q₁) (q₂ := q₂) (s := s) R)
      (SourceLaws.templateLaw μ q₁ q₂).toFiniteLaw
      (SourceLaws.outerLaw ν q₁ q₂ s).toFiniteLaw θ (H : ℤ)) :
    RestrictionProfile (fun Z r => N (q₁ := q₁) R activity ξ₀ (.unrestricted Z) r)
      (SourceLaws.rawLaw ν q₁ q₂ s).toFiniteLaw
      (matrixColumnLaw μ q₁ q₂ s hs).toFiniteLaw x ((H + a : ℕ) : ℤ) := by
  intro j
  have heq : (H : ℤ) + (a - j.val : ℕ) = ((H + a : ℕ) : ℤ) - j.val := by omega
  rw [← heq]
  exact reference_rung μ ν R q₁ q₂ s H (a - j.val) hs activity ξ₀ hH θ x _ (hg j) hp

/-- The whole reference profile is derived from the original base profile;
the preceding source profiles are not separate assumptions. -/
theorem reference_profile
    (μ : PositiveRationalLaw X) (ν : PositiveRationalLaw Y)
    (R : X → Y → Bool) (q₁ q₂ s d a b : ℕ)
    [NeZero q₁] [NeZero q₂] [NeZero s] (hs : 4 ≤ s)
    (activity : SourceConstruction.Items s V → Fin q₂ → Option (Fin s))
    (ξ₀ : Tail s Y) (hd : 3 ≤ d) (ha : 2 ≤ a) (hb : 2 ≤ b) (ρ x : ℝ)
    (hinner : ∀ j : Fin 3, RungGuards q₁ (a - j.val) ρ x
      ((3 / 5 : ℝ) * (1 / 2 : ℝ) ^ j.val))
    (houter : ∀ j : Fin 3, RungGuards q₂ (b - j.val) x x
      ((3 / 5 : ℝ) * (1 / 2 : ℝ) ^ j.val))
    (hreference : ∀ j : Fin 3, RungGuards s (a - j.val) x x
      (templateThreshold ((3 / 5 : ℝ) * (1 / 2 : ℝ) ^ j.val)))
    (hp : RestrictionProfile R μ.toFiniteLaw ν.toFiniteLaw ρ (d : ℤ)) :
    RestrictionProfile (fun Z r => N (q₁ := q₁) R activity ξ₀ (.unrestricted Z) r)
      (SourceLaws.rawLaw ν q₁ q₂ s).toFiniteLaw
      (matrixColumnLaw μ q₁ q₂ s hs).toFiniteLaw x ((d + a + b + a : ℕ) : ℤ) :=
  reference_profile_of_outer μ ν R q₁ q₂ s (d + a + b) a hs activity ξ₀
    (by omega) ha x x hreference
    (outer_profile μ ν R q₁ q₂ s d a b hd ha hb ρ x hinner houter hp)

end Paper2.SourceProfilesReference

#print axioms Paper2.SourceProfilesReference.template_retained
#print axioms Paper2.SourceProfilesReference.reference_profile
