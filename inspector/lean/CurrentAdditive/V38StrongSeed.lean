import CurrentAdditive.V38DefectRational
import Paper2.StrongSeed

/-!
Selected v39 `lem:many-product-blocks`, with its proof in Appendix A,
lines 323--350. The legacy module is used only for the exact arithmetic
`copies`, `copies_guard`, `defect_budget`, `theta_le_quarter`, and
`defect_of_density`; its three-threshold communication theorem is not used.
-/

namespace Paper2.V38StrongSeed

open Workspace.Types.CommComplexity

abbrev copies (a : ℕ) : ℕ := StrongSeed.copies a

variable {X Y : Type*} [Fintype X] [Fintype Y]

theorem weaker_profile (F : X → Y → Bool) (μ : FiniteLaw X) (ν : FiniteLaw Y)
    (θ : ℝ) (H : ℕ)
    (h : V38RestrictionProfiles.TwoThresholdProfile F μ ν θ (H : ℤ)) :
    V38RestrictionProfiles.TwoThresholdProfile F μ ν θ ((H : ℤ) - 1) := by
  intro j U V hU hV
  have hh := h j U V hU hV
  omega

theorem near_full_from_profile (F : X → Y → Bool)
    (μ : FiniteLaw X) (ν : FiniteLaw Y) (θ : ℝ) (H : ℕ)
    (h : V38RestrictionProfiles.TwoThresholdProfile F μ ν θ (H : ℤ)) :
    RestrictionLowerBound F μ ν θ (1 - 1 / 64) (H : ℤ) := by
  have h0 := (V38RestrictionProfiles.twoThresholdProfile_iff F μ ν θ (H : ℤ)).mp h
  intro U V hU hV
  exact h0.1 U V hU (by linarith)

/-- Original-law retained-input form of the current many-product-block
bound. All source hypotheses, including exactly two profile thresholds,
are explicit; no desired lower-bound callback is assumed. -/
theorem rational_member (μ : PositiveRationalLaw X) (ν : PositiveRationalLaw Y)
    (F : X → Y → Bool) (H a : ℕ) (hH : 3 ≤ H) (ha : 4 ≤ a)
    (θ : ℝ) (hθ : 0 < θ) (hscale : (2 : ℝ) ^ a * θ ≤ 1)
    (hprofile : V38RestrictionProfiles.TwoThresholdProfile F
      μ.toFiniteLaw ν.toFiniteLaw θ (H : ℤ))
    (R : Finset (Fin (copies a) × X)) (K : Finset (Fin (copies a) → Y))
    (hR : ∀ i, (2 : ℝ) ^ a * θ ≤ μ.toFiniteLaw.prob (fun x => (i, x) ∈ R))
    (hK : (2 : ℝ) ^ (-((2 : ℝ) ^ a / 1024)) ≤
      (ν.toFiniteLaw.iid (copies a)).prob (· ∈ K)) :
    H + a ≤ D (NPCC.subgame (fullInterlace F (copies a)) R K) := by
  classical
  have hKne : K.Nonempty := by
    by_contra hn
    have he : K = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
    have hp := Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2)
      (-((2 : ℝ) ^ a / 1024))
    simp only [he, Finset.notMem_empty, FiniteLaw.prob_false] at hK
    linarith
  exact V38DefectInduction.rational_defect_induction μ ν F H (copies a) a 0 θ
    (1 / 64) hH hθ (StrongSeed.theta_le_quarter a ha θ hθ hscale)
    (by norm_num) le_rfl (by omega) (by omega) (StrongSeed.copies_guard a ha)
    hscale (near_full_from_profile F _ _ θ H hprofile)
    (weaker_profile F _ _ θ H hprofile) R K hKne hR (by
      simpa only [Nat.cast_zero, zero_mul, add_zero, StrongSeed.defect_budget a ha]
        using StrongSeed.defect_of_density hK)

/-- The same actual-matrix bound through the set-based restriction API. -/
theorem rational_restriction
    (μ : PositiveRationalLaw X) (ν : PositiveRationalLaw Y)
    (F : X → Y → Bool) (H a : ℕ) (hH : 3 ≤ H) (ha : 4 ≤ a)
    (θ : ℝ) (hθ : 0 < θ) (hscale : (2 : ℝ) ^ a * θ ≤ 1)
    (hprofile : V38RestrictionProfiles.TwoThresholdProfile F
      μ.toFiniteLaw ν.toFiniteLaw θ (H : ℤ))
    (U : Set (Fin (copies a) × X)) (V : Set (Fin (copies a) → Y))
    (hU : ∀ i, (2 : ℝ) ^ a * θ ≤ μ.toFiniteLaw.prob (fun x => (i, x) ∈ U))
    (hV : (2 : ℝ) ^ (-((2 : ℝ) ^ a / 1024)) ≤
      (ν.toFiniteLaw.iid (copies a)).prob (· ∈ V)) :
    H + a ≤ Compression.restrictionD (fullInterlace F (copies a)) U V := by
  classical
  have hout := rational_member μ ν F H a hH ha θ hθ hscale hprofile
    U.toFinset V.toFinset (by simpa using hU) (by simpa using hV)
  change H + a ≤ Compression.restrictionD (fullInterlace F (copies a))
    (U.toFinset : Set _) (V.toFinset : Set _) at hout
  simpa using hout

#print axioms weaker_profile
#print axioms near_full_from_profile
#print axioms rational_member
#print axioms rational_restriction

end Paper2.V38StrongSeed
