import Paper2.SourceOverheadBounds
import Paper2.LogSquareCutoff

/-!
# Elementary checks for the actual public dyadic schedule

Frozen v12 Appendix C, `eq:schedule` and `eq:admissibility`. A single
explicit all-larger cutoff proves the smallness checks that do not depend
on the graph's deletion allowance. Other checks remain separate.
-/

namespace Paper2.SourceSmallnessSchedule

open SourceProfileParameters

def cutoff : ℕ := LogSquareCutoff.cutoff 2 6 64

private theorem logarithmic_bound (L : ℕ) (hL : cutoff ≤ L) :
    2 * (RestorationWidthScheduleScratch.ell L) ^ 2 +
      6 * RestorationWidthScheduleScratch.ell L + 64 ≤ L :=
  LogSquareCutoff.quadratic_log_le 2 6 64 L hL

theorem sixteen_le (L : ℕ) (hL : cutoff ≤ L) : 16 ≤ L := by
  have h := logarithmic_bound L hL
  omega

private theorem dyadic_small (a b d : ℕ) (h : a + d ≤ b) :
    (2 : ℝ) ^ a * (1 / 2 : ℝ) ^ b ≤ 1 / (2 : ℝ) ^ d := by
  have hp : (2 : ℝ) ^ (a + d) ≤ (2 : ℝ) ^ b :=
    pow_le_pow_right₀ (by norm_num) h
  rw [pow_add] at hp
  rw [one_div, inv_pow, ← div_eq_mul_inv]
  apply (div_le_div_iff₀ (by positivity) (by positivity)).2
  simpa only [one_mul] using hp

theorem source_scale (L : ℕ) (hL : cutoff ≤ L) :
    4 * (width L : ℝ) ^ 2 * rho L ≤ 1 := by
  have h := logarithmic_bound L hL
  have ha := SourceOverheadBounds.source_exponent_le L
  have he : 2 * exponent L + 2 ≤ L := by omega
  have hp := dyadic_small (2 * exponent L) L 2 he
  have hs : (width L : ℝ) ^ 2 = (2 : ℝ) ^ (2 * exponent L) := by
    simp only [width, Nat.cast_pow, Nat.cast_ofNat, ← pow_mul]
    rw [Nat.mul_comm]
  rw [hs]
  unfold rho
  norm_num at hp
  linarith

theorem inner_small (L : ℕ) (hL : cutoff ≤ L) :
    (width L : ℝ) * rho L ≤ 1 / 1000 := by
  have h := logarithmic_bound L hL
  have ha := SourceOverheadBounds.source_exponent_le L
  have he : exponent L + 10 ≤ L := by omega
  have hp := dyadic_small (exponent L) L 10 he
  simp only [width, rho, Nat.cast_pow, Nat.cast_ofNat]
  exact hp.trans (by norm_num)

theorem outer_small (L : ℕ) (hL : cutoff ≤ L) :
    (outerWidth L : ℝ) * x L ≤ 1 / 10000 := by
  have h := logarithmic_bound L hL
  have ha := SourceOverheadBounds.source_exponent_le L
  have he : outerExponent L + 14 ≤ 10 * L := by
    unfold outerExponent
    omega
  have hp := dyadic_small (outerExponent L) (10 * L) 14 he
  simp only [outerWidth, x, Nat.cast_pow, Nat.cast_ofNat]
  exact hp.trans (by norm_num)

theorem reference_small (L : ℕ) (hL : cutoff ≤ L) :
    (width L : ℝ) * x L ≤ 1 / 10000 := by
  have h := logarithmic_bound L hL
  have ha := SourceOverheadBounds.source_exponent_le L
  have he : exponent L + 14 ≤ 10 * L := by omega
  have hp := dyadic_small (exponent L) (10 * L) 14 he
  simp only [width, x, Nat.cast_pow, Nat.cast_ofNat]
  exact hp.trans (by norm_num)

theorem restoration_small (L : ℕ) (hL : cutoff ≤ L) :
    (RestorationWidthScheduleScratch.width L : ℝ) * x L ≤ 1 / 10000 := by
  have h := logarithmic_bound L hL
  have he : RestorationWidthScheduleScratch.depth L + 14 ≤ 10 * L := by
    unfold RestorationWidthScheduleScratch.depth
    omega
  have hp := dyadic_small (RestorationWidthScheduleScratch.depth L)
    (10 * L) 14 he
  simp only [RestorationWidthScheduleScratch.width, x, Nat.cast_pow, Nat.cast_ofNat]
  exact hp.trans (by norm_num)

theorem outer_density (L : ℕ) :
    (10 * L : ℝ) ≤ (outerWidth L : ℝ) / 4096 := by
  have hs : width L ≤ outerWidth L := by
    unfold width outerWidth
    exact Nat.pow_le_pow_right (by decide) (by unfold outerExponent; omega)
  have hsR : (width L : ℝ) ≤ outerWidth L := by exact_mod_cast hs
  have h := width_density_guard L
  linarith

theorem two_outer_small (L : ℕ) (hL : cutoff ≤ L) :
    2 * (outerWidth L : ℝ) * x L ≤ 1 / 8 := by
  have h := outer_small L hL
  linarith

theorem two_reference_small (L : ℕ) (hL : cutoff ≤ L) :
    2 * (width L : ℝ) * x L ≤ 1 / 1000 := by
  have h := reference_small L hL
  linarith

theorem seed_depth (L : ℕ) (hL : cutoff ≤ L) :
    LookupSeed.exponent L + 1 ≤ L := by
  have h := logarithmic_bound L hL
  have hl : L + 1 ≤ 2 ^ RestorationWidthScheduleScratch.ell L :=
    Nat.le_pow_clog (by decide) _
  have hp : 64 * (L + 1) ≤
      2 ^ (6 + RestorationWidthScheduleScratch.ell L) := by
    simpa [pow_add] using Nat.mul_le_mul_left 64 hl
  have ha : LookupSeed.exponent L ≤ 6 + RestorationWidthScheduleScratch.ell L :=
    Nat.clog_le_of_le_pow hp
  omega

#print axioms source_scale
#print axioms inner_small
#print axioms outer_small
#print axioms reference_small
#print axioms restoration_small
#print axioms outer_density
#print axioms two_outer_small
#print axioms two_reference_small
#print axioms seed_depth

end Paper2.SourceSmallnessSchedule
