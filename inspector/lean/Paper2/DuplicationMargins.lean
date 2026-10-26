import Mathlib

/-!
# Strict ceiling margins after uniform duplication

Frozen v12, Appendix A, `cl:rational-laws`, final paragraph. These are
numerical statements about the actual enlarged carrier size `h*m`. The
separate profile-transport module supplies preservation under h-fold input
duplication. This module does not assume a limiting equality or replace a
strict finite inequality by an asymptotic estimate.
-/

namespace Paper2.DuplicationMargins

/-- A concrete sufficient finite-size condition for the strict ceiling
inequality used by classical separation. Natural ceilings match the
positive real row counts in the manuscript. -/
theorem ceiling_margin_of_slack (u h m : ℕ) (ρ x : ℝ) (hρ : 0 ≤ ρ)
    (hslack : (u : ℝ) < h * m * (x - 2 * u * ρ)) :
    u * ⌈2 * ρ * h * m⌉₊ < ⌈x * h * m⌉₊ := by
  have hceil : (⌈2 * ρ * h * m⌉₊ : ℝ) ≤ 2 * ρ * h * m + 1 :=
    (Nat.ceil_lt_add_one (by positivity : 0 ≤ 2 * ρ * h * m)).le
  have hmul := mul_le_mul_of_nonneg_left hceil (Nat.cast_nonneg u : (0 : ℝ) ≤ u)
  have hright : x * h * m ≤ (⌈x * h * m⌉₊ : ℝ) := Nat.le_ceil _
  have hresult : (u : ℝ) * (⌈2 * ρ * h * m⌉₊ : ℝ) < (⌈x * h * m⌉₊ : ℝ) := by
    nlinarith
  exact_mod_cast hresult

/-- Positive carrier size and strict density separation give a positive
integer duplication factor satisfying the finite slack condition. -/
theorem exists_duplication_slack (u m : ℕ) (hm : 0 < m)
    (ρ x : ℝ) (hsep : 2 * (u : ℝ) * ρ < x) :
    ∃ h : ℕ, 0 < h ∧ (u : ℝ) < h * m * (x - 2 * u * ρ) := by
  have hden : 0 < (m : ℝ) * (x - 2 * u * ρ) := by
    exact mul_pos (Nat.cast_pos.mpr hm) (sub_pos.mpr hsep)
  obtain ⟨h, hh⟩ := exists_nat_gt (max 0 ((u : ℝ) / (m * (x - 2 * u * ρ))))
  have hpos : (0 : ℝ) < h := lt_of_le_of_lt (le_max_left _ _) hh
  have hquot : (u : ℝ) / (m * (x - 2 * u * ρ)) < h :=
    lt_of_le_of_lt (le_max_right _ _) hh
  refine ⟨h, Nat.cast_pos.mp hpos, ?_⟩
  have hmul := (div_lt_iff₀ hden).mp hquot
  nlinarith

/-- The displayed strict ceiling inequality in `cl:rational-laws`, for
all nonnegative densities, not only the dyadic specialization. -/
theorem exists_strict_ceiling_margin (u m : ℕ) (hm : 0 < m)
    (ρ x : ℝ) (hρ : 0 ≤ ρ) (hsep : 2 * (u : ℝ) * ρ < x) :
    ∃ h : ℕ, 0 < h ∧ u * ⌈2 * ρ * h * m⌉₊ < ⌈x * h * m⌉₊ := by
  obtain ⟨h, hh, hslack⟩ := exists_duplication_slack u m hm ρ x hsep
  exact ⟨h, hh, ceiling_margin_of_slack u h m ρ x hρ hslack⟩

/-- Once the finite slack is positive, increasing the duplication factor
preserves it. This allows several finite-carrier guards to hold together. -/
theorem duplication_slack_mono (u h k m : ℕ) (hhk : h ≤ k)
    (ρ x : ℝ) (hsep : 2 * (u : ℝ) * ρ < x)
    (hslack : (u : ℝ) < h * m * (x - 2 * u * ρ)) :
    (u : ℝ) < k * m * (x - 2 * u * ρ) := by
  apply lt_of_lt_of_le hslack
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hhk) (Nat.cast_nonneg m))
    (sub_nonneg.mpr hsep.le)

/-- An explicit finite bound on the dominant-block count, stronger than
asserting only convergence of its fraction. Here `k` is `u-1` in the paper. -/
theorem dominant_margin_of_slack (k h m : ℕ) (ρ x target : ℝ) (hρ : 0 ≤ ρ)
    (hslack : (k : ℝ) < h * m * ((x - target) - 2 * k * ρ)) :
    target * (h * m) < (⌈x * h * m⌉₊ : ℝ) -
      k * (⌈2 * ρ * h * m⌉₊ : ℝ) := by
  have hceil := (Nat.ceil_lt_add_one
    (by positivity : 0 ≤ 2 * ρ * h * m)).le
  have hmul := mul_le_mul_of_nonneg_left hceil (Nat.cast_nonneg k : (0 : ℝ) ≤ k)
  have hright : x * h * m ≤ (⌈x * h * m⌉₊ : ℝ) := Nat.le_ceil _
  nlinarith

/-- The same positive integer duplication factor satisfies both the strict
separation guard and any strictly smaller dominant-block fraction. -/
theorem exists_ceiling_and_dominant_margin (u m : ℕ) (hm : 0 < m)
    (ρ x target : ℝ) (hρ : 0 ≤ ρ)
    (hsep : 2 * (u : ℝ) * ρ < x)
    (hdom : 2 * ((u - 1 : ℕ) : ℝ) * ρ < x - target) :
    ∃ h : ℕ, 0 < h ∧
      u * ⌈2 * ρ * h * m⌉₊ < ⌈x * h * m⌉₊ ∧
      target < ((⌈x * h * m⌉₊ : ℝ) -
        (u - 1 : ℕ) * (⌈2 * ρ * h * m⌉₊ : ℝ)) / (h * m) := by
  obtain ⟨h₁, hh₁, hs₁⟩ := exists_duplication_slack u m hm ρ x hsep
  obtain ⟨h₂, hh₂, hs₂⟩ := exists_duplication_slack (u - 1) m hm ρ (x - target) hdom
  let h := max h₁ h₂
  have hh : 0 < h := lt_of_lt_of_le hh₁ (le_max_left _ _)
  have hs₁' := duplication_slack_mono u h₁ h m (le_max_left _ _) ρ x hsep hs₁
  have hs₂' := duplication_slack_mono (u - 1) h₂ h m
    (le_max_right _ _) ρ (x - target) hdom hs₂
  refine ⟨h, hh, ceiling_margin_of_slack u h m ρ x hρ hs₁', ?_⟩
  apply (lt_div_iff₀ (mul_pos (Nat.cast_pos.mpr hh) (Nat.cast_pos.mpr hm))).mpr
  exact dominant_margin_of_slack (u - 1) h m ρ x target hρ hs₂'

/-- The manuscript's numerical application: x=0.999 and u*rho≤0.0001
give a dominant-block fraction strictly greater than 0.998 after one common
finite duplication. No limiting argument remains in this conclusion. -/
theorem manuscript_margins (u m : ℕ) (hm : 0 < m)
    (ρ : ℝ) (hρ : 0 ≤ ρ) (hsmall : (u : ℝ) * ρ ≤ 1 / 10000) :
    ∃ h : ℕ, 0 < h ∧
      u * ⌈2 * ρ * h * m⌉₊ < ⌈(999 / 1000 : ℝ) * h * m⌉₊ ∧
      (998 / 1000 : ℝ) < ((⌈(999 / 1000 : ℝ) * h * m⌉₊ : ℝ) -
        (u - 1 : ℕ) * (⌈2 * ρ * h * m⌉₊ : ℝ)) / (h * m) := by
  apply exists_ceiling_and_dominant_margin u m hm ρ (999 / 1000) (998 / 1000) hρ
  · nlinarith
  · have hk : ((u - 1 : ℕ) : ℝ) ≤ (u : ℝ) := Nat.cast_le.mpr (Nat.sub_le u 1)
    have hprod := mul_le_mul_of_nonneg_right hk hρ
    nlinarith

end Paper2.DuplicationMargins
