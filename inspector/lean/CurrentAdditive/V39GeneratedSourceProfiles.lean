import CurrentAdditive.V39GeneratedGuardsAllLarge
import CurrentAdditive.V39IndexedProfileCosts
import CurrentAdditive.V39IndexedReferenceProfile

/-! Selected v39 `det:profiles`, generated indexed source.  The numerical
premises are proved from the public checker, and then from its accepted
cutoff.  All source labels and their original rational weights are retained.
-/

namespace CurrentAdditive.V39GeneratedSourceProfiles

open Paper2 Workspace.Types.CommComplexity V38Schedule
open CurrentAdditive.DeterministicIndexedMatrix

variable {X Y I : Type} [Fintype X] [Fintype Y] [Fintype I]
  [DecidableEq X] [DecidableEq Y]
  {L : ℕ} [NeZero (generatedQ₁ L)] [NeZero (generatedQ₂ L)] [NeZero (generatedS L)]
  {μX : PositiveRationalLaw X} {μY : PositiveRationalLaw Y}

/-- The two exact template costs and the three current indexed profiles.
The reference is the ordinary part of the actual two-family matrix. -/
def CostsAndProfiles
    (src : Sources (D := 8192) (q₁ := generatedQ₁ L) (q₂ := generatedQ₂ L)
      (s := generatedS L) μX μY)
    (μI : PositiveRationalLaw I) (R : X → Y → Bool)
    (activity : I → Fin (generatedQ₂ L) → Option (Fin (generatedS L)))
    (ξ₀ : SourceMatrix.Tail (generatedS L) Y) (d : ℕ) : Prop :=
  D (Sources.A src R) = d+quarterCeil L ∧
  D (Sources.T src R) = d+quarterCeil L+4*L ∧
  V38RestrictionProfiles.TwoThresholdProfile (Sources.A src R)
    src.gamma.law.toFiniteLaw
    ((PositiveRationalLaw.uniform (Fin (generatedQ₁ L))).prod μX).toFiniteLaw
    ((generatedX L : ℚ) : ℝ) ((d+quarterCeil L : ℕ) : ℤ) ∧
  V38RestrictionProfiles.TwoThresholdProfile (Sources.T src R)
    src.inner.law.toFiniteLaw
    ((PositiveRationalLaw.uniform (Fin (generatedQ₂ L))).prod src.gamma.law).toFiniteLaw
    ((generatedX L : ℚ) : ℝ) ((d+quarterCeil L+4*L : ℕ) : ℤ) ∧
  V38RestrictionProfiles.TwoThresholdProfile
    (V39IndexedReferenceProfile.reference src R activity ξ₀)
    (src.outer.law.prod src.gamma.law).toFiniteLaw
    (V39IndexedReferenceProfile.rowLaw src μI).toFiniteLaw
    ((generatedX L : ℚ) : ℝ) ((d+quarterCeil L+4*L+quarterCeil L : ℕ) : ℤ)

theorem costs_and_profiles_of_tests
    (src : Sources (D := 8192) (q₁ := generatedQ₁ L) (q₂ := generatedQ₂ L)
      (s := generatedS L) μX μY)
    (μI : PositiveRationalLaw I) (R : X → Y → Bool)
    (activity : I → Fin (generatedQ₂ L) → Option (Fin (generatedS L)))
    (ξ₀ : SourceMatrix.Tail (generatedS L) Y) (d : ℕ)
    (c δv ζ : ℚ) (m : ℕ) (htests : GeneratedTests c L m δv ζ)
    (hd : 2 ≤ d) (hD : D R = d)
    (hp : V38RestrictionProfiles.TwoThresholdProfile R μX.toFiniteLaw μY.toFiniteLaw
      ((generatedRho L : ℚ) : ℝ) (d : ℤ)) :
    CostsAndProfiles src μI R activity ξ₀ d := by
  obtain ⟨ha,hb,hρ,hx,hx1,_,_,_,_⟩ :=
    V39GeneratedProfileGuards.scalar_parameters c δv ζ L m htests
  obtain ⟨hsa,hst,hsn⟩ :=
    V39GeneratedProfileGuards.scale_guards c δv ζ L m htests
  obtain ⟨hba,hbt,hbn⟩ :=
    V39GeneratedProfileGuards.population_budgets c δv ζ L m htests
  have hpA := V39IndexedProfiles.A_profile src R d (quarterCeil L)
    ((generatedRho L : ℚ) : ℝ) ((generatedX L : ℚ) : ℝ) 1
    hd ha hρ hx hx1 (by norm_num) hp hsa hba
  have hpT := V39IndexedProfiles.T_profile src R (d+quarterCeil L) (4*L)
    ((generatedX L : ℚ) : ℝ) 1 (by omega) hb hx hx1 (by norm_num) hpA hst hbt
  have hpN := V39IndexedReferenceProfile.reference_profile src μI R activity ξ₀
    (d+quarterCeil L+4*L) (quarterCeil L) ((generatedX L : ℚ) : ℝ) 1
    (by omega) ha hx hx1 (by norm_num) hpT hsn
    (by simpa only [SourceProfilesReference.templateThreshold] using hbn)
  have hq₁ : generatedQ₁ L ≤ 2^quarterCeil L := by
    change 2^quarterCeil L-2 ≤ 2^quarterCeil L
    exact Nat.sub_le _ _
  have hq₂ : generatedQ₂ L ≤ 2^(4*L) := by
    unfold generatedQ₂ generatedN
    rw [← pow_mul]
    simp only [Nat.mul_comm L 4]
    exact le_rfl
  have hA := V39IndexedProfiles.A_exact src R d (quarterCeil L)
    ((generatedX L : ℚ) : ℝ) hD hx1 hq₁ hpA
  have hT := V39IndexedProfiles.T_exact src R (d+quarterCeil L) (4*L)
    ((generatedX L : ℚ) : ℝ) hA hx1 hq₂ hpT
  exact ⟨hA,hT,hpA,hpT,hpN⟩

/-- Above the explicit generated cutoff, the base profile is the only
profile hypothesis.  No eventual-test or later-profile premise is used. -/
theorem costs_and_profiles_all_large
    (src : Sources (D := 8192) (q₁ := generatedQ₁ L) (q₂ := generatedQ₂ L)
      (s := generatedS L) μX μY)
    (μI : PositiveRationalLaw I) (R : X → Y → Bool)
    (activity : I → Fin (generatedQ₂ L) → Option (Fin (generatedS L)))
    (ξ₀ : SourceMatrix.Tail (generatedS L) Y) (d : ℕ)
    (γ c : ℚ) (Δ n m : ℕ)
    (hγ : 0 < γ) (hΔ : 0 < Δ) (hc : 0 < c)
    (hcmax : c ≤ min 1 (min (γ/(4*Δ)) (sourceZeta γ/256))/2^16)
    (hL : GeneratedCutoff.cutoffLog Δ c ≤ L) (hn : 0 < n)
    (hnN : n ≤ generatedN L) (hlow : n ≤ 2*m) (hdegree : 2*m ≤ Δ*n)
    (hd : 2 ≤ d) (hD : D R = d)
    (hp : V38RestrictionProfiles.TwoThresholdProfile R μX.toFiniteLaw μY.toFiniteLaw
      ((generatedRho L : ℚ) : ℝ) (d : ℤ)) :
    CostsAndProfiles src μI R activity ξ₀ d := by
  exact costs_and_profiles_of_tests src μI R activity ξ₀ d
    c (sourceDeltaV γ Δ n m) (sourceZeta γ) m
    (GeneratedCutoff.all_large_sources γ c Δ hγ hΔ hc hcmax
      L n m hL hn hnN hlow hdegree) hd hD hp

#print axioms CostsAndProfiles
#print axioms costs_and_profiles_of_tests
#print axioms costs_and_profiles_all_large

end CurrentAdditive.V39GeneratedSourceProfiles
