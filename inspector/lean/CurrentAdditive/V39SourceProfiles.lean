import CurrentAdditive.V39ActualSourceProfiles
import CurrentAdditive.V38StrongSeed

/-!
Direct two-threshold source profiles on the actual v39 matrix. The general
product-block premise of the transfer packet is discharged by the newly
proved current-source rational theorem. The only remaining premises here
are the base profile and public scalar guards; no later profile, source
hardness, protocol bound, or small-block theorem is assumed.
-/

namespace CurrentAdditive.V39SourceProfiles

open Workspace.Types.CommComplexity Paper2
open Paper2.SourceMatrix Paper2.SourceProjection Paper2.SourceProfilesInner
open CurrentAdditive.EdgeSourceMatrix CurrentAdditive.V38Matrix
open CurrentAdditive.V39ActualSourceProfiles

variable {X Y V E : Type*} [Fintype X] [Fintype Y] [Fintype V] [Fintype E]
variable {q₁ q₂ s : ℕ}

theorem many_product_blocks
    (μ : PositiveRationalLaw X) (ν : PositiveRationalLaw Y) (F : X → Y → Bool) :
    ManyProductBlocks μ ν F := by
  intro H a hH ha θ hθ hscale hp U W hU hW
  exact V38StrongSeed.rational_restriction μ ν F H a hH ha θ hθ hscale hp U W hU hW

/-- Selected `src:profiles`, its exact-cost and three two-threshold-profile
clauses. The three-tail clause is separate. All retained labels and laws
are those of the actual construction, with precisely two column tags. -/
theorem costs_and_profiles [Nonempty V] [NeZero q₁] [NeZero q₂] [NeZero s]
    (μ : PositiveRationalLaw X) (ν : PositiveRationalLaw Y)
    (R : X → Y → Bool)
    (order : Items s V ≃ Fin (Fintype.card (Items s V)))
    (edge : E → Bool → V) (hs : 4 ≤ s) (r : ℕ)
    (hq : q₂ = EdgeSource.sourceQ0 (Fin (4*s)) E*r)
    (ξ₀ : Tail s Y) (d a b : ℕ) (hd : 3 ≤ d) (ρ x : ℝ) (hx : x ≤ 1)
    (hsa : s = 2^a) (hq₁ : q₁+2=s) (hq₂ : q₂=2^b)
    (hinner : ∀ j : Fin 2, RungGuards q₁ (a-j.val) ρ x
      ((3/5 : ℝ)*(1/2 : ℝ)^j.val))
    (houter : ∀ j : Fin 2, RungGuards q₂ (b-j.val) x x
      ((3/5 : ℝ)*(1/2 : ℝ)^j.val))
    (hreference : ∀ j : Fin 2, RungGuards s (a-j.val) x x
      (SourceProfilesReference.templateThreshold ((3/5 : ℝ)*(1/2 : ℝ)^j.val)))
    (hp : V38RestrictionProfiles.TwoThresholdProfile R
      μ.toFiniteLaw ν.toFiniteLaw ρ (d : ℤ)) (hD : D R = d) :
    D (M₁ (q₁ := q₁) (s := s) R)=d+a ∧
    D (T (q₁ := q₁) (q₂ := q₂) (s := s) R)=d+a+b ∧
    V38RestrictionProfiles.TwoThresholdProfile
      (fun γ r => M₁ (q₁ := q₁) (s := s) R r γ)
      (ν.iid (q₁+s+1)).toFiniteLaw
      ((PositiveRationalLaw.uniform (Fin q₁)).prod μ).toFiniteLaw x ((d+a : ℕ) : ℤ) ∧
    V38RestrictionProfiles.TwoThresholdProfile (T (q₁ := q₁) (q₂ := q₂) (s := s) R)
      (SourceLaws.templateLaw μ q₁ q₂).toFiniteLaw
      (SourceLaws.outerLaw ν q₁ q₂ s).toFiniteLaw x ((d+a+b : ℕ) : ℤ) ∧
    V38RestrictionProfiles.TwoThresholdProfile
      (fun Z k => V38Matrix.matrix order edge (by omega : 3 ≤ s) r hq R ξ₀ (.inl Z) k)
      (SourceLaws.rawLaw ν q₁ q₂ s).toFiniteLaw
      (columnLaw (q₁ := q₁) (q₂ := q₂) (s := s) (V := V) μ hs).toFiniteLaw
      x ((d+a+b+a : ℕ) : ℤ) := by
  exact scheduled_source_profiles μ ν R (many_product_blocks μ ν R)
    (many_product_blocks (ν.iid (q₁+s+1))
      ((PositiveRationalLaw.uniform (Fin q₁)).prod μ)
      (fun γ r => M₁ (q₁ := q₁) (s := s) R r γ))
    (many_product_blocks (SourceLaws.templateLaw μ q₁ q₂)
      (SourceLaws.outerLaw ν q₁ q₂ s) (T R))
    order edge hs r hq ξ₀ d a b hd ρ x hx hsa hq₁ hq₂
    hinner houter hreference hp hD

/-- Exact conditional retention of the ordinary branch under the actual
two-tag law, with ordinary mass 255/256 and diagonal mass 1/256. -/
theorem ordinary_retained [NeZero q₂] [NeZero s]
    (ν : PositiveRationalLaw Y) (W : Set (V38Matrix.TaggedColumn q₁ q₂ s Y))
    (η : ℝ)
    (hW : 1-η ≤ (V38Matrix.taggedLaw (q₁:=q₁) (q₂:=q₂) (s:=s) ν).toFiniteLaw.prob (· ∈ W)) :
    1-η/(255/256 : ℝ) ≤ (SourceLaws.rawLaw ν q₁ q₂ s).toFiniteLaw.prob
      (fun Z => Sum.inl Z ∈ W) := by
  have hd := (SourceLaws.outerLaw ν q₁ q₂ s).toFiniteLaw.prob_le_one
    (fun j => Sum.inr j ∈ W)
  rw [V38Matrix.tagged_prob] at hW
  have hscaled : (255/256 : ℝ) *
      (1-(SourceLaws.rawLaw ν q₁ q₂ s).toFiniteLaw.prob (fun Z => Sum.inl Z ∈ W)) ≤ η := by
    linarith
  exact SourceProjectionRetention.retained_of_scaled_defect (by norm_num) hscaled

/-- Any actual near-full source rectangle costs at least the ordinary
reference value. This is the `C-1` bound, before the separate collision
argument forces the final bit. No ordinary-reference profile is assumed:
it is constructed here from the original exact two-threshold base profile. -/
theorem near_full_reference [Nonempty V] [NeZero q₁] [NeZero q₂] [NeZero s]
    (μ : PositiveRationalLaw X) (ν : PositiveRationalLaw Y)
    (R : X → Y → Bool)
    (order : Items s V ≃ Fin (Fintype.card (Items s V)))
    (edge : E → Bool → V) (hs : 4 ≤ s) (r : ℕ)
    (hq : q₂ = EdgeSource.sourceQ0 (Fin (4*s)) E*r)
    (ξ₀ : Tail s Y) (d a b : ℕ) (hd : 3 ≤ d) (ρ x η : ℝ) (hx : x ≤ 1)
    (hsa : s = 2^a) (hq₁ : q₁+2=s) (hq₂ : q₂=2^b)
    (hinner : ∀ j : Fin 2, RungGuards q₁ (a-j.val) ρ x
      ((3/5 : ℝ)*(1/2 : ℝ)^j.val))
    (houter : ∀ j : Fin 2, RungGuards q₂ (b-j.val) x x
      ((3/5 : ℝ)*(1/2 : ℝ)^j.val))
    (hreference : ∀ j : Fin 2, RungGuards s (a-j.val) x x
      (SourceProfilesReference.templateThreshold ((3/5 : ℝ)*(1/2 : ℝ)^j.val)))
    (hp : V38RestrictionProfiles.TwoThresholdProfile R
      μ.toFiniteLaw ν.toFiniteLaw ρ (d : ℤ)) (hD : D R = d)
    (hηΩ : x ≤ 1-η/(255/256 : ℝ)) (hηK : 3/5 ≤ 1-η)
    (W : Set (V38Matrix.TaggedColumn q₁ q₂ s Y))
    (U : Set (RawRow q₁ q₂ s X (Items s V)))
    (hW : 1-η ≤ (V38Matrix.taggedLaw (q₁:=q₁) (q₂:=q₂) (s:=s) ν).toFiniteLaw.prob (· ∈ W))
    (hU : 1-η ≤ (columnLaw (q₁:=q₁) (q₂:=q₂) (s:=s) (V:=V) μ hs).toFiniteLaw.prob (· ∈ U)) :
    d+a+b+a ≤ Compression.restrictionD
      (V38Matrix.matrix order edge (by omega : 3 ≤ s) r hq R ξ₀) W U := by
  have href := (costs_and_profiles μ ν R order edge hs r hq ξ₀ d a b hd ρ x hx
    hsa hq₁ hq₂ hinner houter hreference hp hD).2.2.2.2
  have hlower := href ⟨0,by decide⟩ (Sum.inl ⁻¹' W) U
    (hηΩ.trans (ordinary_retained ν W η hW)) (by simpa using hηK.trans hU)
  have hsub := SourceProjection.restrictionD_map_le
    (V38Matrix.matrix order edge (by omega : 3 ≤ s) r hq R ξ₀) Sum.inl id
    W U (Sum.inl ⁻¹' W) U (fun _ h => h) (fun _ h => h)
  have hlower' : ((d+a+b+a : ℕ) : ℤ) ≤
      (Compression.restrictionD
        (fun Z k => V38Matrix.matrix order edge (by omega : 3 ≤ s) r hq R ξ₀ (.inl Z) k)
        (Sum.inl ⁻¹' W) U : ℤ) := by simpa using hlower
  exact_mod_cast hlower'.trans (Int.ofNat_le.mpr hsub)

#print axioms many_product_blocks
#print axioms costs_and_profiles
#print axioms ordinary_retained
#print axioms near_full_reference

end CurrentAdditive.V39SourceProfiles
