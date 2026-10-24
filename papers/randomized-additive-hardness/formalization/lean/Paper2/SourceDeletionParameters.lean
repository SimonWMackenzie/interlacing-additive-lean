import Paper2.SourceProfileParameters

/-!
# Protected-source deletion guards from the stated schedule

Frozen v12 `eq:schedule` and `src:near-full`. This file unfolds the actual
minimum defining eta and proves the numerical allowances consumed by the
retained-source prefix, item and coordinate arguments. The graph theorem
supplies positive delta_v and zeta; no source lower bound is assumed here.
-/

namespace Paper2.SourceDeletionParameters

noncomputable def eta (s : ℕ) (delta zeta : ℝ) : ℝ :=
  min (min 1 delta) ((1 / 256) * zeta) / (65536 * s)

theorem eta_pos (s : ℕ) (hs : 0 < s) (delta zeta : ℝ)
    (hd : 0 < delta) (hz : 0 < zeta) : 0 < eta s delta zeta := by
  unfold eta
  apply div_pos
  · exact lt_min (lt_min (by norm_num) hd) (by positivity)
  · positivity

theorem eta_mul_width (s : ℕ) (hs : 0 < s) (delta zeta : ℝ) :
    eta s delta zeta * s = min (min 1 delta) ((1 / 256) * zeta) / 65536 := by
  unfold eta
  have hn : (s : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hs
  field_simp

theorem eta_width_bounds (s : ℕ) (hs : 0 < s) (delta zeta : ℝ) :
    eta s delta zeta * s ≤ 1 / 65536 ∧
    eta s delta zeta * s ≤ delta / 65536 ∧
    eta s delta zeta * s ≤ zeta / 16777216 := by
  rw [eta_mul_width s hs]
  have h1 : min (min (1 : ℝ) delta) ((1 / 256) * zeta) ≤ 1 :=
    (min_le_left _ _).trans (min_le_left _ _)
  have hd : min (min (1 : ℝ) delta) ((1 / 256) * zeta) ≤ delta :=
    (min_le_left _ _).trans (min_le_right _ _)
  have hz := min_le_right (min (1 : ℝ) delta) ((1 / 256) * zeta)
  constructor
  · linarith
  constructor <;> linarith

/-- Exactly the two mass conditions used by the actual common-prefix adapter. -/
theorem protected_mass_guards (s : ℕ) (hs : 4 ≤ s) (delta zeta : ℝ)
    (hd : 0 < delta) (hz : 0 < zeta) :
    eta s delta zeta * s / (255 / 256) ≤ 1 / 1000 ∧
    256 * eta s delta zeta ≤ 1 / 100 := by
  have he := eta_pos s (by omega) delta zeta hd hz
  have hw := (eta_width_bounds s (by omega) delta zeta).1
  have hsR : (4 : ℝ) ≤ s := by exact_mod_cast hs
  constructor
  · linarith
  · nlinarith

theorem vertex_allowance (s n : ℕ) (hs : 4 ≤ s) (delta zeta : ℝ)
    (hd : 0 ≤ delta) :
    4096 * eta s delta zeta * s * n ≤ (s : ℝ) / 2 * delta * n := by
  have hw := (eta_width_bounds s (by omega) delta zeta).2.1
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hsR : (4 : ℝ) ≤ s := by exact_mod_cast hs
  have hleft : 4096 * eta s delta zeta * s ≤ delta / 16 := by linarith
  have hright : delta / 16 ≤ (s : ℝ) / 2 * delta := by nlinarith
  exact mul_le_mul_of_nonneg_right (hleft.trans hright) hn

theorem auxiliary_allowance (s : ℕ) (hs : 4 ≤ s) (delta zeta : ℝ) :
    4096 * eta s delta zeta * s * (s - 3 : ℕ) < (s : ℝ) / 2 := by
  have hw := (eta_width_bounds s (by omega) delta zeta).1
  have hn : ((s - 3 : ℕ) : ℝ) = (s : ℝ) - 3 := by
    simp only [Nat.cast_sub (show 3 ≤ s by omega), Nat.cast_ofNat]
  have hp := mul_le_mul_of_nonneg_right hw (Nat.cast_nonneg (s - 3) : (0 : ℝ) ≤ (s - 3 : ℕ))
  have hsR : (4 : ℝ) ≤ s := by exact_mod_cast hs
  rw [hn] at hp ⊢
  nlinarith

/-- The total template/diagonal deficit budget is strictly below zeta*q2/4.
The first premise is the literal 8*s*q1 admissibility test. -/
theorem coordinate_allowance (s q1 q2 : ℕ) (hs : 0 < s) (hq : 0 < q2)
    (delta zeta : ℝ) (hz : 0 < zeta)
    (hcount : 8 * (s : ℝ) * q1 ≤ zeta * q2 / 16) :
    8 * (s : ℝ) * q1 + 1024 * s * eta s delta zeta * q2 < zeta * q2 / 4 := by
  have hw := (eta_width_bounds s hs delta zeta).2.2
  have hmul := mul_le_mul_of_nonneg_right hw (Nat.cast_nonneg q2 : (0 : ℝ) ≤ q2)
  have hp : (0 : ℝ) < zeta * q2 := mul_pos hz (by exact_mod_cast hq)
  nlinarith

/-- The branch assignment's 1/(2s) mass pays the extra-position row floor. -/
theorem assignment_floor (s : ℕ) (hs : 0 < s) (rho : ℝ)
    (hscale : 4 * (s : ℝ) ^ 2 * rho ≤ 1) :
    2 * (s : ℝ) * rho ≤ 1 / (2 * s) := by
  apply (le_div_iff₀ (by positivity : (0 : ℝ) < 2 * s)).mpr
  nlinarith

end Paper2.SourceDeletionParameters
