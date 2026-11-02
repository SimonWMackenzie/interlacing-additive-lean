import CurrentAdditive.V39RareBoost
import CurrentAdditive.IndexedProfileConditioning
import CurrentAdditive.DeterministicIndexedTemplates

/-! Selected v39 `det:profiles`: the finite indexed profile transfer from
the current two-threshold base profile.  The exceptional set is constructed
from the whole retained original-label event.  Remaining guards are scalar
population budgets involving the manuscript's current exception count. -/

namespace CurrentAdditive.V39IndexedProfiles

open Paper2 Workspace.Types.CommComplexity
open CurrentAdditive.DeterministicIndexedMatrix
open CurrentAdditive.ArbitraryPrefix

theorem codeSource_rung
    {X Z : Type*} [Fintype X] [Fintype Z]
    [DecidableEq X] [DecidableEq Z]
    {q : ℕ} [NeZero q]
    (μ : PositiveRationalLaw X) (ν : PositiveRationalLaw Z)
    (F : X → Z → Bool) (src : CodeSource 8192 q Z ν)
    (U : Set (Fin q × X)) (W : Set src.Label)
    (d a : ℕ) (x β v τ : ℝ)
    (ha : 1 ≤ a) (hd : 2 ≤ d) (hx : 0 < x)
    (hscale : (2 : ℝ)^a*x < 1)
    (hprofile : V38RestrictionProfiles.TwoThresholdProfile F
      μ.toFiniteLaw ν.toFiniteLaw x (d : ℤ))
    (hU : β ≤ ((PositiveRationalLaw.uniform (Fin q)).prod μ).toFiniteLaw.prob (· ∈ U))
    (hbudget : (((2^(a-1)+1) + V38Moments.exceptionCount v τ : ℕ) : ℝ) *
      (1-(2 : ℝ)^a*x) ≤ (q : ℝ)*(β-(2 : ℝ)^a*x))
    (hv : 0 < v) (hv1 : v ≤ 1)
    (hW : v ≤ src.law.toFiniteLaw.prob (· ∈ W)) (hτ : 0 < τ) :
    d+a ≤ Compression.restrictionD
      (fun row col => F row.2 (src.decode col row.1)) U W := by
  classical
  obtain ⟨E,hE,hboost⟩ := V38RareBoost.rareboost_after_conditioning
    μ.toFiniteLaw ν F src.law.toFiniteLaw src.decode src.exactLaw
    W v τ hv hv1 hτ hW
  have hbudgetE : (((2^(a-1)+1)+E.card : ℕ) : ℝ)*(1-(2 : ℝ)^a*x) ≤
      (q : ℝ)*(β-(2 : ℝ)^a*x) := by
    have hcount : 2^(a-1)+1+E.card ≤ 2^(a-1)+1+V38Moments.exceptionCount v τ := by omega
    have hcountR : (((2^(a-1)+1)+E.card : ℕ) : ℝ) ≤
        (((2^(a-1)+1)+V38Moments.exceptionCount v τ : ℕ) : ℝ) := by exact_mod_cast hcount
    exact (mul_le_mul_of_nonneg_right hcountR (by linarith)).trans hbudget
  obtain ⟨e,houtside,hmass⟩ := select_avoiding_exceptions μ q
    (2^(a-1)+1) U E β ((2 : ℝ)^a*x) hscale hU hbudgetE
  let Good : Finset (Fin q) := Finset.univ.image e
  let Rows : Fin q → Set X := fun i => {u | (i,u) ∈ U}
  have hcount : 2^(a-1)+1 ≤ Good.card := by
    simp [Good,Finset.card_image_of_injective _ e.injective]
  have hOutside : ∀ i ∈ Good, i ∉ E := by
    intro i hi
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hi
    exact houtside j
  have hrow : ∀ i ∈ Good, (2 : ℝ)^a*x ≤ μ.toFiniteLaw.prob (· ∈ Rows i) := by
    intro i hi
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hi
    exact hmass j
  have hcond : (1/2 : ℝ) ≤ src.law.toFiniteLaw.prob (· ∈ W)/
      src.law.toFiniteLaw.prob (· ∈ W) := by
    rw [div_self (ne_of_gt (hv.trans_le hW))]
    norm_num
  have hl := hboost Good Rows W d a x ha hd hx hscale.le hprofile hcount
    hOutside hrow (Set.Subset.rfl) hcond
  exact hl.trans (SourceProjection.restrictionD_map_le
    (fun row col => F row.2 (src.decode col row.1)) id id
    U W (rowRectangle Good Rows) W
    (by intro row hrow'; exact hrow'.2) (by intro col hcol; exact hcol))

/-- Current two-threshold profile of the actual indexed first template.
The gamma labels and their original rational weights are unchanged. -/
theorem A_profile
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    {q₁ q₂ s : ℕ} [NeZero q₁] [NeZero q₂] [NeZero s]
    {μX : PositiveRationalLaw X} {μY : PositiveRationalLaw Y}
    (src : Sources (D := 8192) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY)
    (R : X → Y → Bool) (d a : ℕ) (ρ x τ : ℝ)
    (hd : 2 ≤ d) (ha : 2 ≤ a) (hρ : 0 < ρ)
    (hx : 0 < x) (hx1 : x ≤ 1) (hτ : 0 < τ)
    (hp : V38RestrictionProfiles.TwoThresholdProfile R
      μX.toFiniteLaw μY.toFiniteLaw ρ (d : ℤ))
    (hscale : ∀ j : Fin 2, (2 : ℝ)^(a-j.val)*ρ < 1)
    (hbudget : ∀ j : Fin 2,
      (((2^((a-j.val)-1)+1)+V38Moments.exceptionCount x τ : ℕ) : ℝ) *
        (1-(2 : ℝ)^(a-j.val)*ρ) ≤
        (q₁ : ℝ)*((3/5 : ℝ)*(1/2 : ℝ)^j.val-(2 : ℝ)^(a-j.val)*ρ)) :
    V38RestrictionProfiles.TwoThresholdProfile (Sources.A src R)
      src.gamma.law.toFiniteLaw
      ((PositiveRationalLaw.uniform (Fin q₁)).prod μX).toFiniteLaw
      x ((d+a : ℕ) : ℤ) := by
  intro j W U hW hU
  have hcost := codeSource_rung μX μY R (Sources.headCodeSource src)
    U W d (a-j.val) ρ ((3/5 : ℝ)*(1/2 : ℝ)^j.val) x τ
    (by have hj := j.isLt; omega) hd hρ (hscale j) hp hU (hbudget j)
    hx hx1 hW hτ
  have hentry : (fun row col => R row.2 ((Sources.headCodeSource src).decode col row.1)) =
      Sources.M₁ src R := by funext row col; rfl
  rw [hentry] at hcost
  have htrans : Compression.restrictionD (Sources.A src R) W U =
      Compression.restrictionD (Sources.M₁ src R) U W :=
    SourceProjection.restrictionD_transpose _ U W
  have hcostA : d+(a-j.val) ≤ Compression.restrictionD (Sources.A src R) W U := by
    rw [htrans]
    exact hcost
  exact_mod_cast (show (d : ℤ)+a-j.val ≤
      (Compression.restrictionD (Sources.A src R) W U : ℤ) by omega)

/-- The same finite transfer gives the actual second template profile,
using the indexed first-template profile as its base. -/
theorem T_profile
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    {q₁ q₂ s : ℕ} [NeZero q₁] [NeZero q₂] [NeZero s]
    {μX : PositiveRationalLaw X} {μY : PositiveRationalLaw Y}
    (src : Sources (D := 8192) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY)
    (R : X → Y → Bool) (H a : ℕ) (x τ : ℝ)
    (hH : 2 ≤ H) (ha : 2 ≤ a) (hx : 0 < x) (hx1 : x ≤ 1) (hτ : 0 < τ)
    (hp : V38RestrictionProfiles.TwoThresholdProfile (Sources.A src R)
      src.gamma.law.toFiniteLaw
      ((PositiveRationalLaw.uniform (Fin q₁)).prod μX).toFiniteLaw x (H : ℤ))
    (hscale : ∀ j : Fin 2, (2 : ℝ)^(a-j.val)*x < 1)
    (hbudget : ∀ j : Fin 2,
      (((2^((a-j.val)-1)+1)+V38Moments.exceptionCount x τ : ℕ) : ℝ) *
        (1-(2 : ℝ)^(a-j.val)*x) ≤
        (q₂ : ℝ)*((3/5 : ℝ)*(1/2 : ℝ)^j.val-(2 : ℝ)^(a-j.val)*x)) :
    V38RestrictionProfiles.TwoThresholdProfile (Sources.T src R)
      src.inner.law.toFiniteLaw
      ((PositiveRationalLaw.uniform (Fin q₂)).prod src.gamma.law).toFiniteLaw
      x ((H+a : ℕ) : ℤ) := by
  intro j W U hW hU
  have hcost := codeSource_rung src.gamma.law
    ((PositiveRationalLaw.uniform (Fin q₁)).prod μX) (Sources.A src R)
    src.inner U W H (a-j.val) x ((3/5 : ℝ)*(1/2 : ℝ)^j.val) x τ
    (by have hj := j.isLt; omega) hH hx (hscale j) hp hU (hbudget j)
    hx hx1 hW hτ
  have hentry : (fun row col => Sources.A src R row.2 (src.inner.decode col row.1)) =
      fun row col => Sources.T src R col row := by funext row col; rfl
  rw [hentry] at hcost
  have htrans : Compression.restrictionD (Sources.T src R) W U =
      Compression.restrictionD (fun row col => Sources.T src R col row) U W :=
    SourceProjection.restrictionD_transpose _ U W
  rw [← htrans] at hcost
  exact_mod_cast (show (H : ℤ)+a-j.val ≤
      (Compression.restrictionD (Sources.T src R) W U : ℤ) by omega)

#print axioms codeSource_rung
#print axioms A_profile
#print axioms T_profile

end CurrentAdditive.V39IndexedProfiles
