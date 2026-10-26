import Paper2.DefectInductionRational

/-!
# Interlacing with column deletion

Frozen v12 Appendix A, `cl:strong-seed` (lines 477--505).
The actual retained-matrix bound is proved for both uniform and positive
rational laws. The uniform minimum-over-restrictions statement is then
obtained over a proved nonempty family. The base complexity parameter is
only a lower bound; no equality with the full matrix cost is assumed.
-/

namespace Paper2.StrongSeed

open Workspace.Types.CommComplexity

/-- Integral form of `9*2^a/16`, used only for `a>=4`. -/
def copies (a : ℕ) : ℕ := 9 * 2 ^ (a - 4)

theorem pow_split (a : ℕ) (ha : 4 ≤ a) : 2 ^ a = 16 * 2 ^ (a - 4) := by
  conv_lhs => rw [show a = (a - 4) + 4 by omega]
  rw [pow_add]
  norm_num
  ring

theorem copies_eq (a : ℕ) (ha : 4 ≤ a) : copies a = 9 * 2 ^ a / 16 := by
  rw [pow_split a ha]
  unfold copies
  omega

theorem copies_guard (a : ℕ) (ha : 4 ≤ a) : 2 ^ a < 2 * copies a := by
  rw [pow_split a ha]
  have hpow := Nat.two_pow_pos (a - 4)
  unfold copies
  omega

theorem defect_budget (a : ℕ) (ha : 4 ≤ a) :
    ((copies a : ℝ) - (2 : ℝ) ^ ((a : ℤ) - 1)) * (1 / 64) =
      (2 : ℝ) ^ a / 1024 := by
  have hp : (2 : ℝ) ^ a = 16 * (2 : ℝ) ^ (a - 4) := by
    exact_mod_cast pow_split a ha
  rw [zpow_sub₀ (by norm_num : (2 : ℝ) ≠ 0), zpow_natCast, zpow_one, hp]
  simp only [copies, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow]
  ring

theorem theta_le_quarter (a : ℕ) (ha : 4 ≤ a) (θ : ℝ)
    (hθ : 0 < θ) (hscale : (2 : ℝ) ^ a * θ ≤ 1) : θ ≤ 1 / 4 := by
  have hp : (16 : ℝ) ≤ (2 : ℝ) ^ a := by
    calc
      16 = (2 : ℝ) ^ 4 := by norm_num
      _ ≤ (2 : ℝ) ^ a := pow_le_pow_right₀ (by norm_num) ha
  nlinarith

/-- The precise conversion of the theorem's density threshold to defect. -/
theorem defect_of_density {mass v : ℝ} (hmass : (2 : ℝ) ^ (-v) ≤ mass) :
    ProjectionDefect.defect mass ≤ v := by
  calc
    _ ≤ ProjectionDefect.defect ((2 : ℝ) ^ (-v)) :=
      ProjectionDefect.defect_antitone (Real.rpow_pos_of_pos (by norm_num) _) hmass
    _ = v := by
      unfold ProjectionDefect.defect
      rw [Real.logb_rpow (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) ≠ 1)]
      ring

variable {X Y : Type*} [Fintype X] [Fintype Y]

theorem weaker_profile (F : X → Y → Bool) (μ : FiniteLaw X) (ν : FiniteLaw Y)
    (θ : ℝ) (H : ℕ) (h : RestrictionProfile F μ ν θ (H : ℤ)) :
    RestrictionProfile F μ ν θ ((H : ℤ) - 1) := by
  intro j U V hU hV
  have hh := h j U V hU hV
  omega

theorem near_full_from_profile (F : X → Y → Bool) (μ : FiniteLaw X) (ν : FiniteLaw Y)
    (θ : ℝ) (H : ℕ) (h : RestrictionProfile F μ ν θ (H : ℤ)) :
    RestrictionLowerBound F μ ν θ (1 - 1 / 64) (H : ℤ) := by
  have h0 := ((restrictionProfile_three_levels F μ ν θ (H : ℤ)).mp h).1
  intro U V hU hV
  exact h0 U V hU (by linarith)

/-- Actual retained-input form of T39 for arbitrary positive rational laws.
The retained column tuples may be correlated. -/
theorem rational_member (μ : PositiveRationalLaw X) (ν : PositiveRationalLaw Y)
    (F : X → Y → Bool) (H a : ℕ) (hH : 3 ≤ H) (ha : 4 ≤ a)
    (θ : ℝ) (hθ : 0 < θ) (hscale : (2 : ℝ) ^ a * θ ≤ 1)
    (hprofile : RestrictionProfile F μ.toFiniteLaw ν.toFiniteLaw θ (H : ℤ))
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
  exact DefectInduction.rational_defect_induction μ ν F H (copies a) a 0 θ (1 / 64)
    hH hθ (theta_le_quarter a ha θ hθ hscale) (by norm_num) le_rfl
    (by omega) (by omega) (copies_guard a ha) hscale
    (near_full_from_profile F _ _ θ H hprofile) (weaker_profile F _ _ θ H hprofile)
    R K hKne hR (by
      simpa only [Nat.cast_zero, zero_mul, add_zero, defect_budget a ha]
        using defect_of_density hK)

section Uniform

variable [Nonempty X] [Nonempty Y]

/-- Uniform actual-retained-matrix form; no family-minimum convention can
make this lower bound true on an empty input set. -/
theorem uniform_member (F : X → Y → Bool) (H a : ℕ) (hH : 3 ≤ H) (ha : 4 ≤ a)
    (θ : ℝ) (hθ : 0 < θ) (hscale : (2 : ℝ) ^ a * θ ≤ 1)
    (hprofile : RestrictionProfile F (FiniteLaw.uniform X) (FiniteLaw.uniform Y) θ (H : ℤ))
    (R : Finset (Fin (copies a) × X)) (K : Finset (Fin (copies a) → Y))
    (hmem : (R, K) ∈ ClassicalRows.restrictions (X := X) (Y := Y) (copies a)
      ((2 : ℝ) ^ a * θ) ((2 : ℝ) ^ (-((2 : ℝ) ^ a / 1024)))) :
    H + a ≤ D (NPCC.subgame (fullInterlace F (copies a)) R K) := by
  have hθ1 := theta_le_quarter a ha θ hθ hscale
  have hnear : H ≤ ClassicalRows.restrictionCost F 1 θ (1 - 1 / 64) := by
    have hh := ClassicalSeparation.oneCopy_family_lowerBound F θ (1 - 1 / 64) (H : ℤ)
      (by linarith) (by norm_num) (near_full_from_profile F _ _ θ H hprofile)
    exact_mod_cast hh
  have hmass : (2 : ℝ) ^ (-((2 : ℝ) ^ a / 1024)) ≤
      ProjectionDefect.columnDensity (copies a) K := by
    unfold ProjectionDefect.columnDensity
    apply (le_div_iff₀ (pow_pos (by exact_mod_cast Fintype.card_pos) _)).mpr
    have hh : (Fintype.card Y : ℝ) ^ copies a *
        (2 : ℝ) ^ (-((2 : ℝ) ^ a / 1024)) ≤ K.card :=
      (Nat.ceil_le.mp hmem.2)
    simpa only [mul_comm] using hh
  have hKne : K.Nonempty := by
    have hp := lt_of_lt_of_le (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _) hmass
    apply Finset.card_pos.mp
    have hh : (0 : ℝ) < K.card :=
      (div_pos_iff_of_pos_right (pow_pos (by exact_mod_cast Fintype.card_pos) _)).mp hp
    exact_mod_cast hh
  exact DefectInduction.defect_induction F H (copies a) a 0 θ (1 / 64)
    hH hθ hθ1 (by norm_num) le_rfl (by omega) (by omega) (copies_guard a ha) hscale
    hnear (weaker_profile F _ _ θ H hprofile) R K hKne
    (by simpa only [mul_assoc] using hmem.1)
    (by simpa only [Nat.cast_zero, zero_mul, add_zero, defect_budget a ha]
      using defect_of_density hmass)

/-- T39's minimum-over-restrictions statement, with `t=2^a` and
`copies a=9*t/16`. The quantified family is explicitly shown nonempty. -/
theorem strong_seed (F : X → Y → Bool) (H a : ℕ) (hH : 3 ≤ H) (ha : 4 ≤ a)
    (θ : ℝ) (hθ : 0 < θ) (hscale : (2 : ℝ) ^ a * θ ≤ 1)
    (hprofile : RestrictionProfile F (FiniteLaw.uniform X) (FiniteLaw.uniform Y) θ (H : ℤ)) :
    H + a ≤ ClassicalRows.restrictionCost F (copies a) ((2 : ℝ) ^ a * θ)
      ((2 : ℝ) ^ (-((2 : ℝ) ^ a / 1024))) := by
  classical
  have hz : (2 : ℝ) ^ (-((2 : ℝ) ^ a / 1024)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (neg_nonpos.mpr (by positivity))
  obtain ⟨RC, hRC⟩ := ClassicalRows.restrictions_nonempty (X := X) (Y := Y)
    (copies a) ((2 : ℝ) ^ a * θ) ((2 : ℝ) ^ (-((2 : ℝ) ^ a / 1024))) hscale hz
  have hne : {d : ℕ | ∃ RC' ∈ ClassicalRows.restrictions (X := X) (Y := Y) (copies a)
      ((2 : ℝ) ^ a * θ) ((2 : ℝ) ^ (-((2 : ℝ) ^ a / 1024))),
      d = D (NPCC.subgame (fullInterlace F (copies a)) RC'.1 RC'.2)}.Nonempty :=
    ⟨_, RC, hRC, rfl⟩
  obtain ⟨RC', hRC', heq⟩ := Nat.sInf_mem hne
  change H + a ≤ sInf {d : ℕ | ∃ RC' ∈ ClassicalRows.restrictions (X := X) (Y := Y)
    (copies a) ((2 : ℝ) ^ a * θ) ((2 : ℝ) ^ (-((2 : ℝ) ^ a / 1024))),
    d = D (NPCC.subgame (fullInterlace F (copies a)) RC'.1 RC'.2)}
  rw [heq]
  exact uniform_member F H a hH ha θ hθ hscale hprofile RC'.1 RC'.2 hRC'

end Uniform
end Paper2.StrongSeed
