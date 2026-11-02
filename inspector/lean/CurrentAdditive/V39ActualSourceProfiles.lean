import CurrentAdditive.V38Matrix
import Paper2.SourceProfilesReference
import CurrentAdditive.V38RestrictionProfiles

/-!
Selected v39 `src:profiles`, mathematically identical to v38.  These are
the literal first, second and ordinary-reference interlaces and their laws.
Every profile hypothesis and conclusion has exactly the source's Fin 2
thresholds 3/5 and 3/10.  The general many-product-block theorem is stated
as an explicit temporary dependency, not supplied by the old Fin 3 theorem.
-/

namespace CurrentAdditive.V39ActualSourceProfiles

open Workspace.Types.CommComplexity Paper2
open Paper2.SourceMatrix Paper2.SourceProjection Paper2.SourceProfilesInner
open CurrentAdditive.EdgeSourceMatrix CurrentAdditive.V38Matrix

variable {X Y V E : Type*} [Fintype X] [Fintype Y] [Fintype V] [Fintype E]
variable {q₁ q₂ s : ℕ}

/-- The general product-block theorem needed here. This is the outstanding
dependency from the lower-bounds team, on arbitrary positive rational laws.
It is not a source-profile or source-hardness premise. -/
def ManyProductBlocks (μ : PositiveRationalLaw X) (ν : PositiveRationalLaw Y)
    (F : X → Y → Bool) : Prop :=
  ∀ (H a : ℕ), 3 ≤ H → 4 ≤ a → ∀ (θ : ℝ), 0 < θ →
    (2 : ℝ)^a * θ ≤ 1 →
    V38RestrictionProfiles.TwoThresholdProfile F μ.toFiniteLaw ν.toFiniteLaw θ (H : ℤ) →
    ∀ (U : Set (Fin (StrongSeed.copies a) × X))
      (W : Set (Fin (StrongSeed.copies a) → Y)),
      (∀ i, (2 : ℝ)^a * θ ≤ μ.toFiniteLaw.prob (fun z => (i,z) ∈ U)) →
      (2 : ℝ)^(-((2 : ℝ)^a / 1024)) ≤
        (ν.toFiniteLaw.iid (StrongSeed.copies a)).prob (· ∈ W) →
      H+a ≤ Compression.restrictionD (fullInterlace F (StrongSeed.copies a)) U W

theorem inner_rung
    (μ : PositiveRationalLaw X) (ν : PositiveRationalLaw Y)
    (R : X → Y → Bool) (hproduct : ManyProductBlocks μ ν R)
    (q₁ s d a : ℕ) [NeZero q₁]
    (hd : 3 ≤ d) (ρ x β : ℝ) (hg : RungGuards q₁ a ρ x β)
    (hp : V38RestrictionProfiles.TwoThresholdProfile R
      μ.toFiniteLaw ν.toFiniteLaw ρ (d : ℤ)) :
    RestrictionLowerBound (fun γ r => M₁ (q₁ := q₁) (s := s) R r γ)
      (ν.iid (q₁+s+1)).toFiniteLaw
      ((PositiveRationalLaw.uniform (Fin q₁)).prod μ).toFiniteLaw x β (d+a) := by
  intro W U hW hU
  obtain ⟨e, he⟩ := select_blocks μ q₁ a ρ x β hg U hU
  let A : Set (Fin (StrongSeed.copies a) × X) := {r | (e r.1,r.2) ∈ U}
  have hwords := hg.word_floor.trans (hW.trans (head_projection_mass ν e e.injective W))
  rw [PositiveRationalLaw.toFiniteLaw_iid] at hwords
  have hlower := hproduct d a hd hg.exponent ρ hg.threshold_pos hg.scale_lt.le
    hp A (headProjection e '' W) he hwords
  have hnat := hlower.trans (M₁_projection_D_le R e U W A (fun _ h => h))
  rw [restrictionD_transpose (M₁ R)]
  exact_mod_cast hnat

theorem inner_profile
    (μ : PositiveRationalLaw X) (ν : PositiveRationalLaw Y)
    (R : X → Y → Bool) (hproduct : ManyProductBlocks μ ν R)
    (q₁ s d a : ℕ) [NeZero q₁] (hd : 3 ≤ d) (ρ x : ℝ)
    (hg : ∀ j : Fin 2, RungGuards q₁ (a-j.val) ρ x
      ((3/5 : ℝ)*(1/2 : ℝ)^j.val))
    (hp : V38RestrictionProfiles.TwoThresholdProfile R
      μ.toFiniteLaw ν.toFiniteLaw ρ (d : ℤ)) :
    V38RestrictionProfiles.TwoThresholdProfile
      (fun γ r => M₁ (q₁ := q₁) (s := s) R r γ)
      (ν.iid (q₁+s+1)).toFiniteLaw
      ((PositiveRationalLaw.uniform (Fin q₁)).prod μ).toFiniteLaw x ((d+a : ℕ) : ℤ) := by
  intro j
  have hj : j.val ≤ a := by have hh := (hg j).exponent; omega
  have heq : (d : ℤ)+(a-j.val : ℕ) = ((d+a : ℕ) : ℤ)-j.val := by omega
  rw [← heq]
  exact inner_rung μ ν R hproduct q₁ s d (a-j.val) hd ρ x _ (hg j) hp

theorem outer_rung
    (μ : PositiveRationalLaw X) (ν : PositiveRationalLaw Y)
    (R : X → Y → Bool)
    (q₁ q₂ s H b : ℕ) [NeZero q₁] [NeZero q₂]
    (hproduct : ManyProductBlocks (ν.iid (q₁+s+1))
      ((PositiveRationalLaw.uniform (Fin q₁)).prod μ)
      (fun γ r => M₁ (q₁ := q₁) (s := s) R r γ))
    (hH : 3 ≤ H) (θ x β : ℝ) (hg : RungGuards q₂ b θ x β)
    (hp : V38RestrictionProfiles.TwoThresholdProfile
      (fun γ r => M₁ (q₁ := q₁) (s := s) R r γ)
      (ν.iid (q₁+s+1)).toFiniteLaw
      ((PositiveRationalLaw.uniform (Fin q₁)).prod μ).toFiniteLaw θ (H : ℤ)) :
    RestrictionLowerBound (T (q₁ := q₁) (q₂ := q₂) (s := s) R)
      (SourceLaws.templateLaw μ q₁ q₂).toFiniteLaw
      (SourceLaws.outerLaw ν q₁ q₂ s).toFiniteLaw x β (H+b) := by
  intro W U hW hU
  obtain ⟨e, he⟩ := select_blocks (ν.iid (q₁+s+1)) q₂ b θ x β hg U hU
  let A : Set (Fin (StrongSeed.copies b) × Word q₁ s Y) := {r | (e r.1,r.2) ∈ U}
  have hwords := hg.word_floor.trans (hW.trans (template_projection_mass μ e e.injective W))
  change _ ≤ ((((PositiveRationalLaw.uniform (Fin q₁)).prod μ).iid
    (StrongSeed.copies b)).toFiniteLaw).prob _ at hwords
  rw [PositiveRationalLaw.toFiniteLaw_iid] at hwords
  have hlower := hproduct H b hH hg.exponent θ hg.threshold_pos hg.scale_lt.le
    hp A (templateProjection e '' W) he hwords
  have hnat := hlower.trans (M₂_projection_D_le R e U W A (fun _ h => h))
  have ht := restrictionD_transpose (M₂ R) U W
  change Compression.restrictionD (T R) W U = _ at ht
  rw [ht]
  exact_mod_cast hnat

theorem outer_profile_of_inner
    (μ : PositiveRationalLaw X) (ν : PositiveRationalLaw Y)
    (R : X → Y → Bool) (q₁ q₂ s H b : ℕ) [NeZero q₁] [NeZero q₂]
    (hproduct : ManyProductBlocks (ν.iid (q₁+s+1))
      ((PositiveRationalLaw.uniform (Fin q₁)).prod μ)
      (fun γ r => M₁ (q₁ := q₁) (s := s) R r γ))
    (hH : 3 ≤ H) (θ x : ℝ)
    (hg : ∀ j : Fin 2, RungGuards q₂ (b-j.val) θ x
      ((3/5 : ℝ)*(1/2 : ℝ)^j.val))
    (hp : V38RestrictionProfiles.TwoThresholdProfile
      (fun γ r => M₁ (q₁ := q₁) (s := s) R r γ)
      (ν.iid (q₁+s+1)).toFiniteLaw
      ((PositiveRationalLaw.uniform (Fin q₁)).prod μ).toFiniteLaw θ (H : ℤ)) :
    V38RestrictionProfiles.TwoThresholdProfile (T (q₁ := q₁) (q₂ := q₂) (s := s) R)
      (SourceLaws.templateLaw μ q₁ q₂).toFiniteLaw
      (SourceLaws.outerLaw ν q₁ q₂ s).toFiniteLaw x ((H+b : ℕ) : ℤ) := by
  intro j
  have hj : j.val ≤ b := by have hh := (hg j).exponent; omega
  have heq : (H : ℤ)+(b-j.val : ℕ) = ((H+b : ℕ) : ℤ)-j.val := by omega
  rw [← heq]
  exact outer_rung μ ν R q₁ q₂ s H (b-j.val) hproduct hH θ x _ (hg j) hp

theorem reference_rung [Nonempty V] [NeZero q₁] [NeZero q₂] [NeZero s]
    (μ : PositiveRationalLaw X) (ν : PositiveRationalLaw Y)
    (R : X → Y → Bool)
    (hproduct : ManyProductBlocks (SourceLaws.templateLaw μ q₁ q₂)
      (SourceLaws.outerLaw ν q₁ q₂ s) (T R))
    (order : Items s V ≃ Fin (Fintype.card (Items s V)))
    (edge : E → Bool → V) (hs : 4 ≤ s) (r : ℕ)
    (hq : q₂ = EdgeSource.sourceQ0 (Fin (4*s)) E*r)
    (ξ₀ : Tail s Y) (H a : ℕ) (hH : 3 ≤ H) (θ x β : ℝ)
    (hg : RungGuards s a θ x (SourceProfilesReference.templateThreshold β))
    (hp : V38RestrictionProfiles.TwoThresholdProfile (T (q₁ := q₁) (q₂ := q₂) (s := s) R)
      (SourceLaws.templateLaw μ q₁ q₂).toFiniteLaw
      (SourceLaws.outerLaw ν q₁ q₂ s).toFiniteLaw θ (H : ℤ)) :
    RestrictionLowerBound
      (fun Z k => V38Matrix.matrix order edge (by omega : 3 ≤ s) r hq R ξ₀ (.inl Z) k)
      (SourceLaws.rawLaw ν q₁ q₂ s).toFiniteLaw
      (columnLaw (q₁ := q₁) (q₂ := q₂) (s := s) (V := V) μ hs).toFiniteLaw
      x β (H+a) := by
  intro W U hW hU
  have ht := SourceProfilesReference.template_retained μ q₁ q₂ s hs U β hU
  obtain ⟨e, he⟩ := select_blocks (SourceLaws.templateLaw μ q₁ q₂) s a θ x
    (SourceProfilesReference.templateThreshold β) hg {r | Sum.inl r ∈ U} ht
  let A : Set (Fin (StrongSeed.copies a) × Template q₁ q₂ X) :=
    {r | Sum.inl (e r.1,r.2) ∈ U}
  have hwords := hg.word_floor.trans (hW.trans (raw_projection_mass ν e e.injective W))
  rw [PositiveRationalLaw.toFiniteLaw_iid] at hwords
  have hlower := hproduct H a hH hg.exponent θ hg.threshold_pos hg.scale_lt.le
    hp A (rawBinProjection e '' W) he hwords
  have hm := reference_projection_D_le R (activity order edge (by omega : 3 ≤ s) r hq)
    ξ₀ e W U A (fun _ h => h)
  exact_mod_cast hlower.trans hm

theorem reference_profile_of_outer [Nonempty V] [NeZero q₁] [NeZero q₂] [NeZero s]
    (μ : PositiveRationalLaw X) (ν : PositiveRationalLaw Y)
    (R : X → Y → Bool)
    (hproduct : ManyProductBlocks (SourceLaws.templateLaw μ q₁ q₂)
      (SourceLaws.outerLaw ν q₁ q₂ s) (T R))
    (order : Items s V ≃ Fin (Fintype.card (Items s V)))
    (edge : E → Bool → V) (hs : 4 ≤ s) (r : ℕ)
    (hq : q₂ = EdgeSource.sourceQ0 (Fin (4*s)) E*r)
    (ξ₀ : Tail s Y) (H a : ℕ) (hH : 3 ≤ H) (θ x : ℝ)
    (hg : ∀ j : Fin 2, RungGuards s (a-j.val) θ x
      (SourceProfilesReference.templateThreshold ((3/5 : ℝ)*(1/2 : ℝ)^j.val)))
    (hp : V38RestrictionProfiles.TwoThresholdProfile (T (q₁ := q₁) (q₂ := q₂) (s := s) R)
      (SourceLaws.templateLaw μ q₁ q₂).toFiniteLaw
      (SourceLaws.outerLaw ν q₁ q₂ s).toFiniteLaw θ (H : ℤ)) :
    V38RestrictionProfiles.TwoThresholdProfile
      (fun Z k => V38Matrix.matrix order edge (by omega : 3 ≤ s) r hq R ξ₀ (.inl Z) k)
      (SourceLaws.rawLaw ν q₁ q₂ s).toFiniteLaw
      (columnLaw (q₁ := q₁) (q₂ := q₂) (s := s) (V := V) μ hs).toFiniteLaw
      x ((H+a : ℕ) : ℤ) := by
  intro j
  have hj : j.val ≤ a := by have hh := (hg j).exponent; omega
  have heq : (H : ℤ)+(a-j.val : ℕ) = ((H+a : ℕ) : ℤ)-j.val := by omega
  rw [← heq]
  exact reference_rung μ ν R hproduct order edge hs r hq ξ₀ H (a-j.val) hH
    θ x _ (hg j) hp

/-- All three literal source profiles are constructed successively from
the original base profile; no later source profile is an input. The only
pending general lower-bound dependencies are the three instances of the
many-product-block theorem. The public scalar guards are kept explicit. -/
theorem source_profiles [Nonempty V] [NeZero q₁] [NeZero q₂] [NeZero s]
    (μ : PositiveRationalLaw X) (ν : PositiveRationalLaw Y)
    (R : X → Y → Bool)
    (hproduct₀ : ManyProductBlocks μ ν R)
    (hproduct₁ : ManyProductBlocks (ν.iid (q₁+s+1))
      ((PositiveRationalLaw.uniform (Fin q₁)).prod μ)
      (fun γ r => M₁ (q₁ := q₁) (s := s) R r γ))
    (hproduct₂ : ManyProductBlocks (SourceLaws.templateLaw μ q₁ q₂)
      (SourceLaws.outerLaw ν q₁ q₂ s) (T R))
    (order : Items s V ≃ Fin (Fintype.card (Items s V)))
    (edge : E → Bool → V) (hs : 4 ≤ s) (r : ℕ)
    (hq : q₂ = EdgeSource.sourceQ0 (Fin (4*s)) E*r)
    (ξ₀ : Tail s Y) (d a b : ℕ) (hd : 3 ≤ d) (ρ x : ℝ)
    (hinner : ∀ j : Fin 2, RungGuards q₁ (a-j.val) ρ x
      ((3/5 : ℝ)*(1/2 : ℝ)^j.val))
    (houter : ∀ j : Fin 2, RungGuards q₂ (b-j.val) x x
      ((3/5 : ℝ)*(1/2 : ℝ)^j.val))
    (hreference : ∀ j : Fin 2, RungGuards s (a-j.val) x x
      (SourceProfilesReference.templateThreshold ((3/5 : ℝ)*(1/2 : ℝ)^j.val)))
    (hp : V38RestrictionProfiles.TwoThresholdProfile R
      μ.toFiniteLaw ν.toFiniteLaw ρ (d : ℤ)) :
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
  have hp₁ := inner_profile μ ν R hproduct₀ q₁ s d a hd ρ x hinner hp
  have hp₂ := outer_profile_of_inner μ ν R q₁ q₂ s (d+a) b hproduct₁
    (by omega) x x houter hp₁
  exact ⟨hp₁, hp₂, reference_profile_of_outer μ ν R hproduct₂ order edge hs r hq
    ξ₀ (d+a+b) a (by omega) x x hreference hp₂⟩

theorem inner_exact
    (μ : PositiveRationalLaw X) (ν : PositiveRationalLaw Y)
    (R : X → Y → Bool) (hproduct : ManyProductBlocks μ ν R)
    (q₁ s d a : ℕ) [NeZero q₁] (hd : 3 ≤ d) (ρ x : ℝ) (hx : x ≤ 1)
    (hg : ∀ j : Fin 2, RungGuards q₁ (a-j.val) ρ x
      ((3/5 : ℝ)*(1/2 : ℝ)^j.val))
    (hp : V38RestrictionProfiles.TwoThresholdProfile R
      μ.toFiniteLaw ν.toFiniteLaw ρ (d : ℤ))
    (hD : D R = d) (hwidth : q₁ ≤ 2^a) :
    D (M₁ (q₁ := q₁) (s := s) R) = d+a := by
  apply Nat.le_antisymm
  · simpa only [hD] using SourceProfilesInner.inner_upper R q₁ s a (NeZero.pos q₁) hwidth
  · have hp' := inner_profile μ ν R hproduct q₁ s d a hd ρ x hg hp
    have hl := hp' ⟨0, by decide⟩ Set.univ Set.univ (by simpa using hx) (by norm_num)
    have hm := SourceProfilesInner.restrictionD_le
      (fun γ r => M₁ (q₁ := q₁) (s := s) R r γ) Set.univ Set.univ
    rw [transpose_D] at hm
    have hl' : ((d+a : ℕ) : ℤ) ≤
        (Compression.restrictionD (fun γ r => M₁ (q₁ := q₁) (s := s) R r γ)
          Set.univ Set.univ : ℤ) := by simpa using hl
    exact_mod_cast hl'.trans (Int.ofNat_le.mpr hm)

theorem outer_exact
    (μ : PositiveRationalLaw X) (ν : PositiveRationalLaw Y)
    (R : X → Y → Bool) (q₁ q₂ s d a b : ℕ) [NeZero q₁] [NeZero q₂]
    (hproduct₀ : ManyProductBlocks μ ν R)
    (hproduct₁ : ManyProductBlocks (ν.iid (q₁+s+1))
      ((PositiveRationalLaw.uniform (Fin q₁)).prod μ)
      (fun γ r => M₁ (q₁ := q₁) (s := s) R r γ))
    (hd : 3 ≤ d) (ρ x : ℝ) (hx : x ≤ 1)
    (hinner : ∀ j : Fin 2, RungGuards q₁ (a-j.val) ρ x
      ((3/5 : ℝ)*(1/2 : ℝ)^j.val))
    (houter : ∀ j : Fin 2, RungGuards q₂ (b-j.val) x x
      ((3/5 : ℝ)*(1/2 : ℝ)^j.val))
    (hp : V38RestrictionProfiles.TwoThresholdProfile R
      μ.toFiniteLaw ν.toFiniteLaw ρ (d : ℤ))
    (hD : D R = d) (hwidth₁ : q₁ ≤ 2^a) (hwidth₂ : q₂ ≤ 2^b) :
    D (T (q₁ := q₁) (q₂ := q₂) (s := s) R) = d+a+b := by
  apply Nat.le_antisymm
  · have hu := SourceProfilesOuter.outer_upper R q₁ q₂ s b (NeZero.pos q₂) hwidth₂
    rw [inner_exact μ ν R hproduct₀ q₁ s d a hd ρ x hx hinner hp hD hwidth₁] at hu
    exact hu
  · have hp₁ := inner_profile μ ν R hproduct₀ q₁ s d a hd ρ x hinner hp
    have hp₂ := outer_profile_of_inner μ ν R q₁ q₂ s (d+a) b hproduct₁
      (by omega) x x houter hp₁
    have hl := hp₂ ⟨0, by decide⟩ Set.univ Set.univ (by simpa using hx) (by norm_num)
    have hm := SourceProfilesInner.restrictionD_le (T (q₁ := q₁) (q₂ := q₂) (s := s) R)
      Set.univ Set.univ
    have hl' : ((d+a+b : ℕ) : ℤ) ≤
        (Compression.restrictionD (T (q₁ := q₁) (q₂ := q₂) (s := s) R)
          Set.univ Set.univ : ℤ) := by simpa using hl
    exact_mod_cast hl'.trans (Int.ofNat_le.mpr hm)

/-- The scheduled source specialization: `s=2^a`, `q₁=s-2`, and
`q₂=2^b`. The returned exact costs and three profiles concern the same
actual source objects. Numeric schedule guards and the temporary general
product-block dependencies remain visible in this first transfer packet. -/
theorem scheduled_source_profiles [Nonempty V] [NeZero q₁] [NeZero q₂] [NeZero s]
    (μ : PositiveRationalLaw X) (ν : PositiveRationalLaw Y)
    (R : X → Y → Bool)
    (hproduct₀ : ManyProductBlocks μ ν R)
    (hproduct₁ : ManyProductBlocks (ν.iid (q₁+s+1))
      ((PositiveRationalLaw.uniform (Fin q₁)).prod μ)
      (fun γ r => M₁ (q₁ := q₁) (s := s) R r γ))
    (hproduct₂ : ManyProductBlocks (SourceLaws.templateLaw μ q₁ q₂)
      (SourceLaws.outerLaw ν q₁ q₂ s) (T R))
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
  have hw₁ : q₁ ≤ 2^a := by omega
  have hw₂ : q₂ ≤ 2^b := hq₂.le
  refine ⟨inner_exact μ ν R hproduct₀ q₁ s d a hd ρ x hx hinner hp hD hw₁,
    outer_exact μ ν R q₁ q₂ s d a b hproduct₀ hproduct₁ hd ρ x hx
      hinner houter hp hD hw₁ hw₂, ?_⟩
  exact source_profiles μ ν R hproduct₀ hproduct₁ hproduct₂ order edge hs r hq
    ξ₀ d a b hd ρ x hinner houter hreference hp

#print axioms inner_rung
#print axioms inner_profile
#print axioms outer_rung
#print axioms outer_profile_of_inner
#print axioms reference_rung
#print axioms reference_profile_of_outer
#print axioms source_profiles
#print axioms inner_exact
#print axioms outer_exact
#print axioms scheduled_source_profiles

end CurrentAdditive.V39ActualSourceProfiles
