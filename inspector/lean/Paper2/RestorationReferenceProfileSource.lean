import Paper2.RestorationReferenceProfile

/-!
# Source specialization of the three-rung restoration reference profile

Frozen v12 Section 5, lines 488--507. The source reference profile comes
from the base profile through the three actual source interlaces; the
restoration profile then uses the literal tagged/reference mixture.
-/

namespace Paper2.RestorationReferenceProfileSource

open Workspace.Types.CommComplexity
open SourceMatrix SourceLawBinding SourceProfileParameters

local instance (L : ℕ) : NeZero (width L) := ⟨by unfold width; positivity⟩
local instance (L : ℕ) : NeZero (outerWidth L) := ⟨by unfold outerWidth; positivity⟩
local instance (L : ℕ) : NeZero (width L - 2) := ⟨by
  have h := width_admissible L
  omega⟩

/-- The source-based one-bit-weaker profile of the transposed first
restoration interlace. Only the original base profile and literal finite
schedule checks are supplied; no coordinate count or final profile is. -/
theorem source_reference_profile
    {X Y V : Type*} [Fintype X] [Fintype Y] [Fintype V] [Nonempty V]
    (μ : PositiveRationalLaw X) (ν : PositiveRationalLaw Y)
    (base : X → Y → Bool) (L d w r Q C : ℕ)
    (hd : 3 ≤ d) (hD : D base = d)
    (hp : RestrictionProfile base μ.toFiniteLaw ν.toFiniteLaw (rho L) (d : ℤ))
    (hinner : (width L : ℝ) * rho L ≤ 1 / 1000)
    (houter : (outerWidth L : ℝ) * x L ≤ 1 / 10000)
    (hwide : (10 * L : ℝ) ≤ (outerWidth L : ℝ) / 4096)
    (href : (width L : ℝ) * x L ≤ 1 / 10000)
    (activity : SourceConstruction.Items (width L) V →
      Fin (outerWidth L) → Option (Fin (width L)))
    (ξ₀ : Tail (width L) Y)
    (hw : w = 2 ^ r) (hQ : 0 < Q)
    (hsmall : (w : ℝ) * x L ≤ 1 / 10000)
    (hstar : 4 * RestorationCoverParameters.tStar Q ≤ w)
    (hC : C = d + exponent L + outerExponent L + exponent L + 1) :
    RestrictionProfile
      (fun col row => fullInterlace
        (N (q₁ := width L - 2) base activity ξ₀) w row col)
      ((matrixColumnLaw μ (width L - 2) (outerWidth L) (width L)
        (SourceProfiles.width_ge_four L)).iid w).toFiniteLaw
      (ReferenceInitial.firstRowLaw ν (by rw [hw]; positivity))
      (RestorationCoverParameters.theta Q) ((C + r - 1 : ℕ) : ℤ) := by
  have hr : 8 ≤ r := by
    have ht := RestorationCoverParameters.tStar_ge Q
    by_contra hn
    have hle : r ≤ 7 := by omega
    have hpow : 2 ^ r ≤ 2 ^ 7 := Nat.pow_le_pow_right (by decide) hle
    rw [hw] at hstar
    omega
  have hsource := SourceProfiles.source_profiles μ ν base L d hd hD hp
    hinner houter hwide href activity ξ₀
  obtain ⟨_, _, _, _, hrefprof⟩ := hsource
  have hprof := RestorationReferenceProfile.reference_profile μ ν base activity ξ₀
    (SourceProfiles.width_ge_four L)
    (d + exponent L + outerExponent L + exponent L) r
    (by omega) hr hw (x L) (RestorationCoverParameters.theta Q)
    (x_pos L) hsmall
    (RestorationReferenceProfile.column_threshold Q w r hQ hr hw hstar)
    hrefprof
  convert hprof using 1
  congr 1
  omega

end Paper2.RestorationReferenceProfileSource

#print axioms Paper2.RestorationReferenceProfileSource.source_reference_profile
