import Paper2.SourceProfilesSchedule
import Paper2.SourceProfilesReference
import Paper2.SourceExtraPosition

/-!
# The source restriction profiles at the actual public parameters

Frozen v12 `src:profiles`. The only retained hypotheses are the base
matrix/profile and the displayed public admissibility checks. In particular,
the caller supplies neither a source profile nor a qualifying-block count.
The extra-position part of the same lemma is `SourceExtraPosition`.
-/

namespace Paper2.SourceProfiles

open Workspace.Types.CommComplexity
open SourceMatrix SourceLawBinding SourceProfileParameters SourceProfilesSchedule

local instance (L : ℕ) : NeZero (width L) := ⟨by unfold width; positivity⟩
local instance (L : ℕ) : NeZero (outerWidth L) := ⟨by unfold outerWidth; positivity⟩
local instance (L : ℕ) : NeZero (width L - 2) := ⟨by
  have h := width_admissible L
  omega⟩

theorem width_ge_four (L : ℕ) : 4 ≤ width L := by
  have h := width_admissible L
  omega

/-- All five source-profile conclusions, from the original base matrix and
literal finite checks in the stated schedule. The activity is arbitrary:
these source-independent conclusions hold before a graph promise is used. -/
theorem source_profiles
    {X Y V : Type*} [Fintype X] [Fintype Y] [Fintype V] [Nonempty V]
    (μ : PositiveRationalLaw X) (ν : PositiveRationalLaw Y)
    (R : X → Y → Bool) (L d : ℕ) (hd : 3 ≤ d)
    (hD : D R = d)
    (hp : RestrictionProfile R μ.toFiniteLaw ν.toFiniteLaw (rho L) (d : ℤ))
    (hinner : (width L : ℝ) * rho L ≤ 1 / 1000)
    (houter : (outerWidth L : ℝ) * x L ≤ 1 / 10000)
    (hwide : (10 * L : ℝ) ≤ (outerWidth L : ℝ) / 4096)
    (href : (width L : ℝ) * x L ≤ 1 / 10000)
    (activity : SourceConstruction.Items (width L) V →
      Fin (outerWidth L) → Option (Fin (width L))) (ξ₀ : Tail (width L) Y) :
    D (M₁ (q₁ := width L - 2) (s := width L) R) = d + exponent L ∧
    RestrictionProfile
      (fun γ r => M₁ (q₁ := width L - 2) (s := width L) R r γ)
      (ν.iid ((width L - 2) + width L + 1)).toFiniteLaw
      ((PositiveRationalLaw.uniform (Fin (width L - 2))).prod μ).toFiniteLaw
      (x L) ((d + exponent L : ℕ) : ℤ) ∧
    D (T (q₁ := width L - 2) (q₂ := outerWidth L) (s := width L) R) =
      d + exponent L + outerExponent L ∧
    RestrictionProfile
      (T (q₁ := width L - 2) (q₂ := outerWidth L) (s := width L) R)
      (SourceLaws.templateLaw μ (width L - 2) (outerWidth L)).toFiniteLaw
      (SourceLaws.outerLaw ν (width L - 2) (outerWidth L) (width L)).toFiniteLaw
      (x L) ((d + exponent L + outerExponent L : ℕ) : ℤ) ∧
    RestrictionProfile
      (fun Z r => N (q₁ := width L - 2) R activity ξ₀ (.unrestricted Z) r)
      (SourceLaws.rawLaw ν (width L - 2) (outerWidth L) (width L)).toFiniteLaw
      (matrixColumnLaw μ (width L - 2) (outerWidth L) (width L)
        (width_ge_four L)).toFiniteLaw
      (x L) ((d + exponent L + outerExponent L + exponent L : ℕ) : ℤ) := by
  have ha : 2 ≤ exponent L := le_trans (by decide) (exponent_ge L)
  have hb : 2 ≤ outerExponent L := by unfold outerExponent; omega
  have hx : x L ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hq1 : width L - 2 ≤ 2 ^ exponent L := Nat.sub_le _ _
  have hq2 : outerWidth L ≤ 2 ^ outerExponent L := le_rfl
  have hi := inner_guards L hinner
  have ho := outer_guards L houter hwide
  have hr := reference_guards L href
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact SourceProfilesInner.inner_exact μ ν R (width L - 2) (width L)
      d (exponent L) hd ha (rho L) (x L) hx hi hp hD hq1
  · exact SourceProfilesInner.inner_profile μ ν R (width L - 2) (width L)
      d (exponent L) hd ha (rho L) (x L) hi hp
  · exact SourceProfilesOuter.outer_exact μ ν R (width L - 2) (outerWidth L)
      (width L) d (exponent L) (outerExponent L) hd ha hb (rho L) (x L) hx
      hi ho hp hD hq1 hq2
  · exact SourceProfilesOuter.outer_profile μ ν R (width L - 2) (outerWidth L)
      (width L) d (exponent L) (outerExponent L) hd ha hb (rho L) (x L) hi ho hp
  · exact SourceProfilesReference.reference_profile μ ν R (width L - 2) (outerWidth L)
      (width L) d (exponent L) (outerExponent L) (width_ge_four L) activity ξ₀
      hd ha hb (rho L) (x L) hi ho hr hp

end Paper2.SourceProfiles
