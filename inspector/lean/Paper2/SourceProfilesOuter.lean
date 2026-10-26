import Paper2.SourceProfilesInner

/-!
# The restriction profile of the second source interlace

Frozen v12 Section 4, `src:profiles`, second paragraph.  The first source
profile is used as the proved base profile, and the actual retained
templates project to a joint set of surviving selected coordinates.
-/

namespace Paper2.SourceProfilesOuter

open Workspace.Types.CommComplexity
open SourceMatrix SourceProjection SourceProfilesInner

variable {X Y : Type*} [Fintype X] [Fintype Y]

theorem outer_upper (R : X → Y → Bool) (q₁ q₂ s b : ℕ)
    (hq : 0 < q₂) (hwidth : q₂ ≤ 2 ^ b) :
    D (T (q₁ := q₁) (q₂ := q₂) (s := s) R) ≤
      D (M₁ (q₁ := q₁) (s := s) R) + b := by
  have h := fullInterlace_transpose_D_le
    (fun (γ : Word q₁ s Y) (r : InnerRow q₁ X) => M₁ R r γ) q₂ hq
  have ht : D (fun (γ : Word q₁ s Y) (r : InnerRow q₁ X) => M₁ R r γ) =
      D (M₁ (q₁ := q₁) (s := s) R) := transpose_D (M₁ R)
  rw [ht] at h
  have hlog : Nat.clog 2 q₂ ≤ b := (Nat.clog_le_iff_le_pow (by decide)).2 hwidth
  change D (T (q₁ := q₁) (q₂ := q₂) (s := s) R) ≤ _ at h
  exact h.trans (by omega)

theorem outer_rung (μ : PositiveRationalLaw X) (ν : PositiveRationalLaw Y)
    (R : X → Y → Bool) (q₁ q₂ s H b : ℕ) [NeZero q₁] [NeZero q₂]
    (hH : 3 ≤ H) (θ x β : ℝ) (hg : RungGuards q₂ b θ x β)
    (hp : RestrictionProfile (fun γ r => M₁ (q₁ := q₁) (s := s) R r γ)
      (ν.iid (q₁ + s + 1)).toFiniteLaw
      ((PositiveRationalLaw.uniform (Fin q₁)).prod μ).toFiniteLaw θ (H : ℤ)) :
    RestrictionLowerBound (T (q₁ := q₁) (q₂ := q₂) (s := s) R)
      (SourceLaws.templateLaw μ q₁ q₂).toFiniteLaw
      (SourceLaws.outerLaw ν q₁ q₂ s).toFiniteLaw x β (H + b) := by
  intro W U hW hU
  obtain ⟨e, he⟩ := select_blocks (ν.iid (q₁ + s + 1)) q₂ b θ x β hg U hU
  let A : Set (Fin (StrongSeed.copies b) × Word q₁ s Y) :=
    {r | (e r.1, r.2) ∈ U}
  have hwords := hg.word_floor.trans
    (hW.trans (template_projection_mass μ e e.injective W))
  change _ ≤ ((((PositiveRationalLaw.uniform (Fin q₁)).prod μ).iid
    (StrongSeed.copies b)).toFiniteLaw).prob _ at hwords
  rw [PositiveRationalLaw.toFiniteLaw_iid] at hwords
  have hlower := strong_member_sets (ν.iid (q₁ + s + 1))
    ((PositiveRationalLaw.uniform (Fin q₁)).prod μ)
    (fun (γ : Word q₁ s Y) (r : InnerRow q₁ X) => M₁ R r γ)
    H b hH hg.exponent θ hg.threshold_pos hg.scale_lt.le hp
    A (templateProjection e '' W) he hwords
  have hmap := M₂_projection_D_le R e U W A (fun _ h => h)
  have hnat := hlower.trans hmap
  have htrans := restrictionD_transpose (M₂ R) U W
  change Compression.restrictionD (T R) W U = _ at htrans
  rw [htrans]
  exact_mod_cast hnat

theorem outer_profile_of_inner
    (μ : PositiveRationalLaw X) (ν : PositiveRationalLaw Y)
    (R : X → Y → Bool) (q₁ q₂ s H b : ℕ) [NeZero q₁] [NeZero q₂]
    (hH : 3 ≤ H) (hb : 2 ≤ b) (θ x : ℝ)
    (hg : ∀ j : Fin 3, RungGuards q₂ (b - j.val) θ x
      ((3 / 5 : ℝ) * (1 / 2 : ℝ) ^ j.val))
    (hp : RestrictionProfile (fun γ r => M₁ (q₁ := q₁) (s := s) R r γ)
      (ν.iid (q₁ + s + 1)).toFiniteLaw
      ((PositiveRationalLaw.uniform (Fin q₁)).prod μ).toFiniteLaw θ (H : ℤ)) :
    RestrictionProfile (T (q₁ := q₁) (q₂ := q₂) (s := s) R)
      (SourceLaws.templateLaw μ q₁ q₂).toFiniteLaw
      (SourceLaws.outerLaw ν q₁ q₂ s).toFiniteLaw x ((H + b : ℕ) : ℤ) := by
  intro j
  have heq : (H : ℤ) + (b - j.val : ℕ) = ((H + b : ℕ) : ℤ) - j.val := by omega
  rw [← heq]
  exact outer_rung μ ν R q₁ q₂ s H (b - j.val) hH θ x _ (hg j) hp

/-- Both source profiles are derived from the original base profile. -/
theorem outer_profile
    (μ : PositiveRationalLaw X) (ν : PositiveRationalLaw Y)
    (R : X → Y → Bool) (q₁ q₂ s d a b : ℕ) [NeZero q₁] [NeZero q₂]
    (hd : 3 ≤ d) (ha : 2 ≤ a) (hb : 2 ≤ b) (ρ x : ℝ)
    (hinner : ∀ j : Fin 3, RungGuards q₁ (a - j.val) ρ x
      ((3 / 5 : ℝ) * (1 / 2 : ℝ) ^ j.val))
    (houter : ∀ j : Fin 3, RungGuards q₂ (b - j.val) x x
      ((3 / 5 : ℝ) * (1 / 2 : ℝ) ^ j.val))
    (hp : RestrictionProfile R μ.toFiniteLaw ν.toFiniteLaw ρ (d : ℤ)) :
    RestrictionProfile (T (q₁ := q₁) (q₂ := q₂) (s := s) R)
      (SourceLaws.templateLaw μ q₁ q₂).toFiniteLaw
      (SourceLaws.outerLaw ν q₁ q₂ s).toFiniteLaw x ((d + a + b : ℕ) : ℤ) :=
  outer_profile_of_inner μ ν R q₁ q₂ s (d + a) b (by omega) hb x x houter
    (inner_profile μ ν R q₁ s d a hd ha ρ x hinner hp)

theorem outer_exact
    (μ : PositiveRationalLaw X) (ν : PositiveRationalLaw Y)
    (R : X → Y → Bool) (q₁ q₂ s d a b : ℕ) [NeZero q₁] [NeZero q₂]
    (hd : 3 ≤ d) (ha : 2 ≤ a) (hb : 2 ≤ b) (ρ x : ℝ) (hx : x ≤ 1)
    (hinner : ∀ j : Fin 3, RungGuards q₁ (a - j.val) ρ x
      ((3 / 5 : ℝ) * (1 / 2 : ℝ) ^ j.val))
    (houter : ∀ j : Fin 3, RungGuards q₂ (b - j.val) x x
      ((3 / 5 : ℝ) * (1 / 2 : ℝ) ^ j.val))
    (hp : RestrictionProfile R μ.toFiniteLaw ν.toFiniteLaw ρ (d : ℤ))
    (hD : D R = d) (hwidth₁ : q₁ ≤ 2 ^ a) (hwidth₂ : q₂ ≤ 2 ^ b) :
    D (T (q₁ := q₁) (q₂ := q₂) (s := s) R) = d + a + b := by
  apply Nat.le_antisymm
  · have h := outer_upper R q₁ q₂ s b (NeZero.pos q₂) hwidth₂
    rw [inner_exact μ ν R q₁ s d a hd ha ρ x hx hinner hp hD hwidth₁] at h
    exact h
  · have hp' := outer_profile μ ν R q₁ q₂ s d a b hd ha hb ρ x hinner houter hp
    have hl := hp' ⟨0, by decide⟩ Set.univ Set.univ
      (by simpa using hx) (by norm_num)
    have hm := restrictionD_le (T (q₁ := q₁) (q₂ := q₂) (s := s) R)
      Set.univ Set.univ
    have hl' : ((d + a + b : ℕ) : ℤ) ≤
        (Compression.restrictionD (T (q₁ := q₁) (q₂ := q₂) (s := s) R)
          Set.univ Set.univ : ℤ) := by simpa using hl
    exact_mod_cast hl'.trans (Int.ofNat_le.mpr hm)

end Paper2.SourceProfilesOuter

#print axioms Paper2.SourceProfilesOuter.outer_profile
#print axioms Paper2.SourceProfilesOuter.outer_exact
