import Paper2.RestorationWidthSchedule
import Paper2.SourceRationalSchedule

/-!
# An explicit eventual polynomial bound for the public restoration width

This supplies one-sided numerical domination only. The constant and degree
are explicit natural inputs, and the threshold is computable from them.
-/

namespace Paper2.WidthDomination

open RestorationWidthScheduleScratch

theorem width_eq_rational_schedule (L : ℕ) :
    width L = SourceRationalScheduleScratch.restorationWidth L := rfl

/-- A computable ceiling-log exponent for the coefficient. -/
def coefficientExponent (C : ℕ) : ℕ := Nat.clog 2 (max 1 C)

/-- A conservative explicit threshold in `ell(L)` for degree `d`. -/
def threshold (C d : ℕ) : ℕ := d + coefficientExponent C + 1

theorem coefficient_le_pow (C : ℕ) : C ≤ 2 ^ coefficientExponent C := by
  exact (le_max_right 1 C).trans (Nat.le_pow_clog (by decide) _)

theorem nat_le_two_pow (n : ℕ) : n ≤ 2 ^ n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      rw [pow_succ]
      have hp : 0 < 2 ^ n := pow_pos (by omega) _
      omega

theorem exponent_domination (C d e : ℕ) (he : threshold C d ≤ e) :
    coefficientExponent C + d * e ≤ e ^ 2 := by
  have hc : coefficientExponent C ≤ e := by
    unfold threshold at he
    omega
  have hd : d + coefficientExponent C ≤ e := by
    unfold threshold at he
    omega
  have he1 : 1 ≤ e := by
    unfold threshold at he
    omega
  have hmul := Nat.mul_le_mul_left e hd
  have hcoeff : coefficientExponent C ≤ e * coefficientExponent C := by
    nlinarith
  nlinarith

/-- `2^(ell²)` dominates any specified fixed polynomial in `L+1` once
the public ceiling-log exponent crosses the explicit threshold. -/
theorem polynomial_domination (C d L : ℕ)
    (hlarge : threshold C d ≤ ell L) :
    C * (L + 1) ^ d ≤ width L := by
  have hc := coefficient_le_pow C
  have hL : L + 1 ≤ 2 ^ ell L := by
    exact Nat.le_pow_clog (by decide) _
  have hexp := exponent_domination C d (ell L) hlarge
  calc
    C * (L + 1) ^ d ≤ 2 ^ coefficientExponent C * (2 ^ ell L) ^ d := by
      gcongr
    _ = 2 ^ (coefficientExponent C + d * ell L) := by
      rw [← pow_mul, pow_add]
      congr 1
      ring
    _ ≤ 2 ^ ((ell L) ^ 2) := by
      exact pow_le_pow_right₀ (by omega : 1 ≤ (2 : ℕ)) hexp
    _ = width L := rfl

/-- A directly computable (conservative) cutoff in the public `L`, not
merely an uninstantiated eventuality assertion. -/
theorem ell_large_of_L_large (C d L : ℕ)
    (hL : 2 ^ threshold C d ≤ L) : threshold C d ≤ ell L := by
  have hp : 2 ^ threshold C d ≤ L + 1 := by omega
  have hc := Nat.clog_mono_right 2 hp
  simpa only [ell, Nat.clog_pow 2 (threshold C d) (by decide)] using hc

theorem polynomial_domination_large_L (C d L : ℕ)
    (hL : 2 ^ threshold C d ≤ L) :
    C * (L + 1) ^ d ≤ width L :=
  polynomial_domination C d L (ell_large_of_L_large C d L hL)

/-- Directly useful for a bound of the frozen Appendix C shape
`K_* E / eta ≤ C (L+1)^3 ell^6`, once its rational coefficient is known. -/
theorem cubic_sixth_domination (C L : ℕ)
    (hlarge : threshold C 9 ≤ ell L) :
    C * (L + 1) ^ 3 * (ell L) ^ 6 ≤ width L := by
  have hc := coefficient_le_pow C
  have hL : L + 1 ≤ 2 ^ ell L := by
    exact Nat.le_pow_clog (by decide) _
  have hell := nat_le_two_pow (ell L)
  have hexp := exponent_domination C 9 (ell L) hlarge
  calc
    C * (L + 1) ^ 3 * (ell L) ^ 6 ≤
        2 ^ coefficientExponent C * (2 ^ ell L) ^ 3 * (2 ^ ell L) ^ 6 := by
      gcongr
    _ = 2 ^ (coefficientExponent C + ell L * 3 + ell L * 6) := by
      simp only [pow_add, pow_mul]
    _ = 2 ^ (coefficientExponent C + 9 * ell L) := by
      congr 1
      ring
    _ ≤ 2 ^ ((ell L) ^ 2) := by
      exact pow_le_pow_right₀ (by omega : 1 ≤ (2 : ℕ)) hexp
    _ = width L := rfl

theorem cubic_sixth_domination_large_L (C L : ℕ)
    (hL : 2 ^ threshold C 9 ≤ L) :
    C * (L + 1) ^ 3 * (ell L) ^ 6 ≤ width L :=
  cubic_sixth_domination C L (ell_large_of_L_large C 9 L hL)

end Paper2.WidthDomination

#print axioms Paper2.WidthDomination.polynomial_domination
#print axioms Paper2.WidthDomination.cubic_sixth_domination
#print axioms Paper2.WidthDomination.cubic_sixth_domination_large_L
