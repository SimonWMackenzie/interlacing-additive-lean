import Paper2.SourceProfileParameters
import Paper2.SourceProfilesInner

/-!
# Instantiating all three source-profile calls from the public schedule

Frozen v12 `src:profiles`, `eq:schedule`, and `eq:admissibility`.
The hypotheses below are literal finite checks of the public schedule.
Every strong-seed guard is derived; no qualifying-population or communication
conclusion is supplied by the caller. The full eventual-admissibility and
machine compiler theorems are not asserted here.
-/

namespace Paper2.SourceProfilesSchedule

open SourceProfileParameters SourceProfilesInner

theorem inner_guards (L : ℕ)
    (hsmall : (width L : ℝ) * rho L ≤ 1 / 1000) (j : Fin 3) :
    RungGuards (width L - 2) (exponent L - j.val) (rho L) (x L) (beta j.val) := by
  have hn : 8 ≤ exponent L := le_trans (by decide) (exponent_ge L)
  have hj : j.val ≤ 2 := by omega
  have hs : (2 : ℝ) ^ exponent L * rho L ≤ 1 / 1000 := by
    simpa only [width, Nat.cast_pow, Nat.cast_ofNat] using hsmall
  refine ⟨(rung_bounds _ _ hn hj).1, rho_pos L,
    rung_scale_lt_one _ _ _ (rho_pos L).le hs, ?_, ?_⟩
  · apply density_threshold L (exponent L) j.val (by omega) hj
    simpa only [width, Nat.cast_pow, Nat.cast_ofNat] using width_density_guard L
  · simpa only [width] using (inner_population _ _ hn hj _ (rho_pos L).le hs).le

theorem outer_guards (L : ℕ)
    (hsmall : (outerWidth L : ℝ) * x L ≤ 1 / 10000)
    (hwide : (10 * L : ℝ) ≤ (outerWidth L : ℝ) / 4096) (j : Fin 3) :
    RungGuards (outerWidth L) (outerExponent L - j.val) (x L) (x L) (beta j.val) := by
  have ha := exponent_ge L
  have hn : 8 ≤ outerExponent L := by unfold outerExponent; omega
  have hj : j.val ≤ 2 := by omega
  have hs : (2 : ℝ) ^ outerExponent L * x L ≤ 1 / 10000 := by
    simpa only [outerWidth, Nat.cast_pow, Nat.cast_ofNat] using hsmall
  refine ⟨(rung_bounds _ _ hn hj).1, x_pos L,
    rung_scale_lt_one _ _ _ (x_pos L).le (by linarith), ?_, ?_⟩
  · apply density_threshold L (outerExponent L) j.val (by omega) hj
    simpa only [outerWidth, Nat.cast_pow, Nat.cast_ofNat] using hwide
  · simpa only [outerWidth, Nat.cast_pow, Nat.cast_ofNat] using
      (outer_population _ _ hn hj _ (x_pos L).le hs).le

theorem reference_guards (L : ℕ)
    (hsmall : (width L : ℝ) * x L ≤ 1 / 10000) (j : Fin 3) :
    RungGuards (width L) (exponent L - j.val) (x L) (x L)
      ((beta j.val - (1 - 255 / 256)) / (255 / 256)) := by
  have hn : 8 ≤ exponent L := le_trans (by decide) (exponent_ge L)
  have hj : j.val ≤ 2 := by omega
  have hs : (2 : ℝ) ^ exponent L * x L ≤ 1 / 10000 := by
    simpa only [width, Nat.cast_pow, Nat.cast_ofNat] using hsmall
  refine ⟨(rung_bounds _ _ hn hj).1, x_pos L,
    rung_scale_lt_one _ _ _ (x_pos L).le (by linarith), ?_, ?_⟩
  · apply density_threshold L (exponent L) j.val (by omega) hj
    simpa only [width, Nat.cast_pow, Nat.cast_ofNat] using width_density_guard L
  · simpa only [width, Nat.cast_pow, Nat.cast_ofNat] using
      (reference_population _ _ hn hj _ (x_pos L).le hs).le

end Paper2.SourceProfilesSchedule
