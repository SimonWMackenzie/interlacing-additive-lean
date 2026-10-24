import CurrentAdditive.V39IndexedProfiles
import Paper2.SourceProfilesInner

/-! Exact whole-matrix template costs from the current two-rung profiles
and the unchanged actual indexed selector protocols. -/

namespace CurrentAdditive.V39IndexedProfiles

open Paper2 Workspace.Types.CommComplexity
open CurrentAdditive.DeterministicIndexedMatrix

theorem profile_full_cost
    {X Z : Type*} [Fintype X] [Fintype Z]
    (μ : FiniteLaw X) (ν : FiniteLaw Z) (F : X → Z → Bool)
    (x : ℝ) (d : ℕ) (hx : x ≤ 1)
    (hp : V38RestrictionProfiles.TwoThresholdProfile F μ ν x (d : ℤ)) : d ≤ D F := by
  have hrow : x ≤ μ.prob (· ∈ (Set.univ : Set X)) := by simpa using hx
  have hcol : (3/5 : ℝ)*(1/2 : ℝ)^(0 : ℕ) ≤ ν.prob (· ∈ (Set.univ : Set Z)) := by norm_num
  have hl := hp (0 : Fin 2) Set.univ Set.univ hrow hcol
  have hu := SourceProfilesInner.restrictionD_le F Set.univ Set.univ
  have hcast : (d : ℤ) ≤ (D F : ℤ) := by
    have hz : ((0 : Fin 2).val : ℤ) = 0 := rfl
    simp only [hz,sub_zero] at hl
    exact hl.trans (Int.ofNat_le.mpr hu)
  exact_mod_cast hcast

theorem A_exact
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    {D₀ q₁ q₂ s : ℕ} [NeZero q₁] [NeZero q₂] [NeZero s]
    {μX : PositiveRationalLaw X} {μY : PositiveRationalLaw Y}
    (src : Sources (D := D₀) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY)
    (R : X → Y → Bool) (d a : ℕ) (x : ℝ)
    (hD : D R = d) (hx : x ≤ 1) (hwidth : q₁ ≤ 2^a)
    (hp : V38RestrictionProfiles.TwoThresholdProfile (Sources.A src R)
      src.gamma.law.toFiniteLaw
      ((PositiveRationalLaw.uniform (Fin q₁)).prod μX).toFiniteLaw
      x ((d+a : ℕ) : ℤ)) : D (Sources.A src R) = d+a := by
  apply Nat.le_antisymm
  · have hclog : Nat.clog 2 q₁ ≤ a := (Nat.clog_le_iff_le_pow (by decide)).2 hwidth
    calc
      D (Sources.A src R) = D (Sources.M₁ src R) := Sources.A_D_eq_M₁ src R
      _ ≤ Nat.clog 2 q₁ + D R := Sources.M₁_D_le src R
      _ ≤ d+a := by omega
  · exact profile_full_cost src.gamma.law.toFiniteLaw
      ((PositiveRationalLaw.uniform (Fin q₁)).prod μX).toFiniteLaw
      (Sources.A src R) x (d+a) hx hp

theorem T_exact
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    {D₀ q₁ q₂ s : ℕ} [NeZero q₁] [NeZero q₂] [NeZero s]
    {μX : PositiveRationalLaw X} {μY : PositiveRationalLaw Y}
    (src : Sources (D := D₀) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY)
    (R : X → Y → Bool) (H a : ℕ) (x : ℝ)
    (hA : D (Sources.A src R) = H) (hx : x ≤ 1) (hwidth : q₂ ≤ 2^a)
    (hp : V38RestrictionProfiles.TwoThresholdProfile (Sources.T src R)
      src.inner.law.toFiniteLaw
      ((PositiveRationalLaw.uniform (Fin q₂)).prod src.gamma.law).toFiniteLaw
      x ((H+a : ℕ) : ℤ)) : D (Sources.T src R) = H+a := by
  apply Nat.le_antisymm
  · have hclog : Nat.clog 2 q₂ ≤ a := (Nat.clog_le_iff_le_pow (by decide)).2 hwidth
    calc
      D (Sources.T src R) ≤ Nat.clog 2 q₂ + D (Sources.A src R) := Sources.T_D_le src R
      _ ≤ H+a := by omega
  · exact profile_full_cost src.inner.law.toFiniteLaw
      ((PositiveRationalLaw.uniform (Fin q₂)).prod src.gamma.law).toFiniteLaw
      (Sources.T src R) x (H+a) hx hp

#print axioms profile_full_cost
#print axioms A_exact
#print axioms T_exact

end CurrentAdditive.V39IndexedProfiles
