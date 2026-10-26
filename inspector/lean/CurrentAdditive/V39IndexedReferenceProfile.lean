import CurrentAdditive.V39IndexedProfiles
import CurrentAdditive.V38IndexedTwoTag
import Paper2.AModelTape

/-! The current indexed ordinary-reference profile.  Ordinary source
indices and actual two-family entries are retained throughout. -/

namespace CurrentAdditive.V39IndexedReferenceProfile

open Paper2 Workspace.Types.CommComplexity
open CurrentAdditive.DeterministicIndexedMatrix

variable {X Y I : Type*} [Fintype X] [Fintype Y] [Fintype I]
  [DecidableEq X] [DecidableEq Y]
  {q₁ q₂ s : ℕ} [NeZero q₁] [NeZero q₂] [NeZero s]
  {μX : PositiveRationalLaw X} {μY : PositiveRationalLaw Y}
  (src : Sources (D := 8192) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY)

/-- The actual current row mixture, for any indexed item law. -/
noncomputable def rowLaw (μI : PositiveRationalLaw I) : PositiveRationalLaw (Sources.Row (I := I) src) where
  weight
    | .inl pz => (255/256)*((PositiveRationalLaw.uniform (Fin s)).prod src.inner.law).weight pz
    | .inr iu => (1/256)*(μI.prod μX).weight iu
  positive a := by
    cases a with
    | inl a => exact mul_pos (by norm_num) (((PositiveRationalLaw.uniform (Fin s)).prod src.inner.law).positive a)
    | inr a => exact mul_pos (by norm_num) ((μI.prod μX).positive a)
  total := by
    rw [Fintype.sum_sum_type]
    simp only [← Finset.mul_sum,PositiveRationalLaw.total,mul_one]
    norm_num

theorem row_prob_split (μI : PositiveRationalLaw I) (U : Set (Sources.Row (I := I) src)) :
    (rowLaw src μI).toFiniteLaw.prob (· ∈ U) =
      (255/256 : ℝ)*((PositiveRationalLaw.uniform (Fin s)).prod src.inner.law).toFiniteLaw.prob
        (fun pz => Sum.inl pz ∈ U) +
      (1/256 : ℝ)*(μI.prod μX).toFiniteLaw.prob (fun iu => Sum.inr iu ∈ U) := by
  classical
  unfold FiniteLaw.prob
  rw [Fintype.sum_sum_type]
  simp only [PositiveRationalLaw.toFiniteLaw,rowLaw,Rat.cast_mul,
    Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,Finset.mul_sum,mul_ite,mul_zero]

theorem template_retained (μI : PositiveRationalLaw I)
    (U : Set (Sources.Row (I := I) src)) (β : ℝ)
    (hU : β ≤ (rowLaw src μI).toFiniteLaw.prob (· ∈ U)) :
    (β-(1-255/256))/(255/256 : ℝ) ≤
      ((PositiveRationalLaw.uniform (Fin s)).prod src.inner.law).toFiniteLaw.prob
        (fun pz => Sum.inl pz ∈ U) := by
  rw [row_prob_split] at hU
  have hsource := (μI.prod μX).toFiniteLaw.prob_le_one (fun iu => Sum.inr iu ∈ U)
  linarith

/-- The normalised ordinary restriction of the actual selected matrix. -/
def reference (R : X → Y → Bool)
    (activity : I → Fin q₂ → Option (Fin s)) (ξ₀ : SourceMatrix.Tail s Y) :
    (src.outer.Label × src.gamma.Label) → Sources.Row (I := I) src → Bool :=
  fun Z k => V38IndexedTwoTag.matrix src R activity ξ₀ (Sum.inl Z) k

theorem outer_image_mass (W : Set (src.outer.Label × src.gamma.Label)) :
    (src.outer.law.prod src.gamma.law).toFiniteLaw.prob (· ∈ W) ≤
      src.outer.law.toFiniteLaw.prob (· ∈ Prod.fst '' W) := by
  have hpush : (src.outer.law.prod src.gamma.law).toFiniteLaw.PushesTo
      src.outer.law.toFiniteLaw Prod.fst := by
    intro E
    rw [PositiveRationalLaw.toFiniteLaw_prod]
    exact AModel.prod_prob_fst _ _ E
  exact FiniteLaw.prob_le_image _ _ _ hpush W

theorem reference_profile (μI : PositiveRationalLaw I)
    (R : X → Y → Bool) (activity : I → Fin q₂ → Option (Fin s))
    (ξ₀ : SourceMatrix.Tail s Y) (H a : ℕ) (x τ : ℝ)
    (hH : 2 ≤ H) (ha : 2 ≤ a) (hx : 0 < x) (hx1 : x ≤ 1) (hτ : 0 < τ)
    (hp : V38RestrictionProfiles.TwoThresholdProfile (Sources.T src R)
      src.inner.law.toFiniteLaw
      ((PositiveRationalLaw.uniform (Fin q₂)).prod src.gamma.law).toFiniteLaw x (H : ℤ))
    (hscale : ∀ j : Fin 2, (2 : ℝ)^(a-j.val)*x < 1)
    (hbudget : ∀ j : Fin 2,
      (((2^((a-j.val)-1)+1)+V38Moments.exceptionCount x τ : ℕ) : ℝ)*
        (1-(2 : ℝ)^(a-j.val)*x) ≤
        (s : ℝ)*((((3/5 : ℝ)*(1/2 : ℝ)^j.val-(1-255/256))/(255/256))-
          (2 : ℝ)^(a-j.val)*x)) :
    V38RestrictionProfiles.TwoThresholdProfile (reference src R activity ξ₀)
      (src.outer.law.prod src.gamma.law).toFiniteLaw (rowLaw src μI).toFiniteLaw
      x ((H+a : ℕ) : ℤ) := by
  intro j W U hW hU
  let β : ℝ := (3/5 : ℝ)*(1/2 : ℝ)^j.val
  let β' : ℝ := (β-(1-255/256))/(255/256)
  let Ut : Set (Fin s × src.inner.Label) := fun pz => Sum.inl pz ∈ U
  let Wout : Set src.outer.Label := Prod.fst '' W
  have hUt : β' ≤ ((PositiveRationalLaw.uniform (Fin s)).prod src.inner.law).toFiniteLaw.prob
      (· ∈ Ut) := by simpa only [β',β,Ut] using template_retained src μI U _ hU
  have hWout : x ≤ src.outer.law.toFiniteLaw.prob (· ∈ Wout) :=
    hW.trans (outer_image_mass src W)
  have hcost := V39IndexedProfiles.codeSource_rung src.inner.law
    ((PositiveRationalLaw.uniform (Fin q₂)).prod src.gamma.law) (Sources.T src R)
    src.outer Ut Wout H (a-j.val) x β' x τ
    (by have hj := j.isLt; omega) hH hx (hscale j) hp hUt (hbudget j)
    hx hx1 hWout hτ
  have htransfer : Compression.restrictionD
      (fun pz js => Sources.T src R pz.2 (src.outer.decode js pz.1)) Ut Wout ≤
      Compression.restrictionD (fun k Z => reference src R activity ξ₀ Z k) U W := by
    exact SourceProjection.restrictionD_projected_le
      (fun k Z => reference src R activity ξ₀ Z k)
      (fun pz js => Sources.T src R pz.2 (src.outer.decode js pz.1))
      Sum.inl Prod.fst U W Ut (by intro pz hpz; exact hpz)
      (by intro pz hpz Z hZ; rfl)
  have htrans : Compression.restrictionD
      (fun k Z => reference src R activity ξ₀ Z k) U W =
      Compression.restrictionD (reference src R activity ξ₀) W U :=
    (SourceProjection.restrictionD_transpose _ U W).symm
  have hcostN : H+(a-j.val) ≤ Compression.restrictionD (reference src R activity ξ₀) W U :=
    hcost.trans (htransfer.trans_eq htrans)
  exact_mod_cast (show (H : ℤ)+a-j.val ≤
    (Compression.restrictionD (reference src R activity ξ₀) W U : ℤ) by omega)

#print axioms rowLaw
#print axioms row_prob_split
#print axioms template_retained
#print axioms outer_image_mass
#print axioms reference_profile

end CurrentAdditive.V39IndexedReferenceProfile
