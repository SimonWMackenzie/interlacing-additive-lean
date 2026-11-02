import Paper2.SourceProfileParameters

/-!
# The public restoration width and its exact scale guard

Frozen v12 Appendix C, `eq:schedule` and the `x ≤ 1/(w²q₂)` check in
`eq:admissibility`. This scratch proof derives the corresponding product
bound directly from the displayed dyadic schedule for `L ≥ 16`; it does not
construct `Q`, prove all admissibility checks, or supply a compiler.
-/

namespace Paper2.RestorationWidthScheduleScratch

open SourceProfileParameters

/-- The paper's `ℓ = ceil(log₂(L+1))`. -/
def ell (L : ℕ) : ℕ := Nat.clog 2 (L + 1)

/-- The paper's internal interlace depth `r = ℓ²`. -/
def depth (L : ℕ) : ℕ := (ell L) ^ 2

/-- The paper's public restoration width `w = 2^r`. -/
def width (L : ℕ) : ℕ := 2 ^ depth L

private theorem quadratic_le_dyadic (n : ℕ) (hn : 5 ≤ n) :
    2 * n ^ 2 + 2 * n + 32 ≤ 9 * 2 ^ (n - 1) := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
      have hquad : 2 * (n + 1) ^ 2 + 2 * (n + 1) + 32 ≤
          2 * (2 * n ^ 2 + 2 * n + 32) := by
        nlinarith
      have hpow : 2 * (9 * 2 ^ (n - 1)) = 9 * 2 ^ (n + 1 - 1) := by
        have hs : n + 1 - 1 = (n - 1) + 1 := by omega
        rw [hs, pow_succ]
        omega
      exact hquad.trans ((Nat.mul_le_mul_left 2 ih).trans_eq hpow)

/-- The exact exponent comparison needed for the restoration-width guard.
It is proved from ceiling-log intervals, not assumed as an admissibility
certificate. -/
theorem exponent_guard (L : ℕ) (hL : 16 ≤ L) :
    2 * (ell L) ^ 2 + 2 * exponent L ≤ 9 * L := by
  have hell : 5 ≤ ell L := by
    have hm : 17 ≤ L + 1 := by omega
    have hc := Nat.clog_mono_right 2 hm
    simpa [ell] using hc
  have hpow : L + 1 ≤ 2 ^ ell L := by
    exact Nat.le_pow_clog (by decide) _
  have hsource : 65536 * (L + 1) ≤ 2 ^ (16 + ell L) := by
    simpa [pow_add] using Nat.mul_le_mul_left 65536 hpow
  have ha : exponent L ≤ 16 + ell L := exponent_minimal L _ hsource
  have hdyadic := quadratic_le_dyadic (ell L) hell
  have hfloor : 2 ^ (ell L - 1) ≤ L := by
    have hp := Nat.pow_pred_clog_lt_self (by decide : 1 < 2)
      (show 1 < L + 1 by omega)
    change 2 ^ (ell L - 1) < L + 1 at hp
    omega
  omega

/-- `w² q₂ x ≤ 1` for the *literal* public `w=2^(ℓ²)` and the already
defined `q₂=outerWidth L`, `x=x L`. This is stronger than merely
rearranging the corresponding finite admissibility check. -/
theorem restoration_scale_guard (L : ℕ) (hL : 16 ≤ L) :
    ((width L : ℝ) ^ 2 * outerWidth L) * x L ≤ 1 := by
  have hexp : 2 * depth L + outerExponent L ≤ 10 * L := by
    have h := exponent_guard L hL
    dsimp [depth, outerExponent] at *
    omega
  have hpow : (2 : ℝ) ^ (2 * depth L + outerExponent L) ≤
      (2 : ℝ) ^ (10 * L) :=
    pow_le_pow_right₀ (by norm_num) hexp
  have hx : (2 : ℝ) ^ (10 * L) * x L = 1 := by
    unfold x
    rw [← mul_pow]
    norm_num
  calc
    ((width L : ℝ) ^ 2 * outerWidth L) * x L =
        (2 : ℝ) ^ (2 * depth L + outerExponent L) * x L := by
      simp only [width, outerWidth, Nat.cast_pow, Nat.cast_ofNat]
      rw [← pow_mul, show depth L * 2 = 2 * depth L by omega, pow_add]
    _ ≤ (2 : ℝ) ^ (10 * L) * x L :=
      mul_le_mul_of_nonneg_right hpow (x_pos L).le
    _ = 1 := hx

/-- The literal Appendix C admissibility check, now derived for the public
restoration width rather than assumed as a certificate. -/
theorem appendix_reciprocal_check (L : ℕ) (hL : 16 ≤ L) :
    x L ≤ 1 / ((width L : ℝ) ^ 2 * outerWidth L) := by
  have hw : 0 < (width L : ℝ) := by unfold width; positivity
  have hq : 0 < (outerWidth L : ℝ) := by unfold outerWidth; positivity
  have hden : 0 < (width L : ℝ) ^ 2 * outerWidth L :=
    mul_pos (pow_pos hw _) hq
  apply (le_div_iff₀ hden).2
  simpa only [mul_comm] using restoration_scale_guard L hL

end Paper2.RestorationWidthScheduleScratch

#print axioms Paper2.RestorationWidthScheduleScratch.exponent_guard
#print axioms Paper2.RestorationWidthScheduleScratch.restoration_scale_guard
#print axioms Paper2.RestorationWidthScheduleScratch.appendix_reciprocal_check
