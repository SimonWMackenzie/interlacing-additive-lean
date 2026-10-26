import Paper2.StrongSeed
import Paper2.LookupSeed

/-!
# The public numerical guards for the source profiles

Frozen v12 `src:profiles` and Appendix C `eq:schedule`, `eq:admissibility`.
These are the actual dyadic widths of that schedule. The three population
inequalities below are derived from its explicit smallness checks, not
assumed qualifying-block counts. The effective all-large cutoff and complete
parameter compiler remain separate obligations.
-/

namespace Paper2.SourceProfileParameters

def exponent (L : ℕ) : ℕ := Nat.clog 2 (65536 * (L + 1))
def width (L : ℕ) : ℕ := 2 ^ exponent L
def outerExponent (L : ℕ) : ℕ := L + 2 * exponent L
def outerWidth (L : ℕ) : ℕ := 2 ^ outerExponent L
noncomputable def rho (L : ℕ) : ℝ := (1 / 2 : ℝ) ^ L
noncomputable def x (L : ℕ) : ℝ := (1 / 2 : ℝ) ^ (10 * L)
noncomputable def beta (j : ℕ) : ℝ := (3 / 5 : ℝ) * (1 / 2 : ℝ) ^ j

theorem width_admissible (L : ℕ) : 65536 * (L + 1) ≤ width L :=
  Nat.le_pow_clog (by decide) _

theorem exponent_minimal (L b : ℕ) (hb : 65536 * (L + 1) ≤ 2 ^ b) :
    exponent L ≤ b := Nat.clog_le_of_le_pow hb

theorem exponent_ge (L : ℕ) : 16 ≤ exponent L := by
  have h := Nat.clog_mono_right 2 (show 2 ^ 16 ≤ 65536 * (L + 1) by omega)
  simpa only [Nat.clog_pow 2 16 (by decide)] using h

theorem outerWidth_eq (L : ℕ) : outerWidth L = 2 ^ L * width L ^ 2 := by
  unfold outerWidth outerExponent width
  rw [pow_add, show 2 * exponent L = exponent L * 2 by omega, pow_mul]

theorem rho_pos (L : ℕ) : 0 < rho L := by unfold rho; positivity
theorem x_pos (L : ℕ) : 0 < x L := by unfold x; positivity

theorem copies_cast (e : ℕ) (he : 4 ≤ e) :
    (StrongSeed.copies e : ℝ) = (9 / 16 : ℝ) * (2 : ℝ) ^ e := by
  have h : (2 : ℝ) ^ e = 16 * (2 : ℝ) ^ (e - 4) := by
    exact_mod_cast StrongSeed.pow_split e he
  simp only [StrongSeed.copies, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow]
  rw [h]
  ring

theorem rung_factor (n j : ℕ) (hj : j ≤ n) :
    (2 : ℝ) ^ n = (2 : ℝ) ^ j * (2 : ℝ) ^ (n - j) := by
  rw [← pow_add, Nat.add_sub_of_le hj]

theorem beta_mul_width (n j : ℕ) (hj : j ≤ n) :
    beta j * (2 : ℝ) ^ n = (3 / 5 : ℝ) * (2 : ℝ) ^ (n - j) := by
  rw [rung_factor n j hj]
  unfold beta
  have h : (1 / 2 : ℝ) ^ j * (2 : ℝ) ^ j = 1 := by
    rw [← mul_pow]
    norm_num
  calc
    _ = (3 / 5 : ℝ) * ((1 / 2 : ℝ) ^ j * (2 : ℝ) ^ j) *
        (2 : ℝ) ^ (n - j) := by ring
    _ = _ := by rw [h]; ring

theorem beta_pos (j : ℕ) : 0 < beta j := by unfold beta; positivity
theorem beta_le (j : ℕ) : beta j ≤ 3 / 5 := by
  have h : (1 / 2 : ℝ) ^ j ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  unfold beta
  linarith

theorem rung_bounds (n j : ℕ) (hn : 8 ≤ n) (hj : j ≤ 2) :
    4 ≤ n - j ∧ 64 ≤ (2 : ℝ) ^ (n - j) ∧
    (2 : ℝ) ^ (n - j) ≤ (2 : ℝ) ^ n ∧
    (2 : ℝ) ^ n ≤ 4 * (2 : ℝ) ^ (n - j) := by
  have hjn : j ≤ n := by omega
  have h64 : (64 : ℝ) ≤ (2 : ℝ) ^ (n - j) := by
    calc
      64 = (2 : ℝ) ^ 6 := by norm_num
      _ ≤ _ := pow_le_pow_right₀ (by norm_num) (by omega)
  have hu : (2 : ℝ) ^ (n - j) ≤ (2 : ℝ) ^ n :=
    pow_le_pow_right₀ (by norm_num) (Nat.sub_le _ _)
  have h4 : (2 : ℝ) ^ j ≤ 4 := by
    calc
      _ ≤ (2 : ℝ) ^ 2 := pow_le_pow_right₀ (by norm_num) hj
      _ = 4 := by norm_num
  refine ⟨by omega, h64, hu, ?_⟩
  rw [rung_factor n j hjn]
  exact mul_le_mul_of_nonneg_right h4 (by positivity)

theorem rung_scale_lt_one (n j : ℕ) (theta : ℝ) (htheta : 0 ≤ theta)
    (hsmall : (2 : ℝ) ^ n * theta ≤ 1 / 1000) :
    (2 : ℝ) ^ (n - j) * theta < 1 := by
  have h := mul_le_mul_of_nonneg_right
    (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (Nat.sub_le n j)) htheta
  linarith

/-- The first source interlace has two fewer blocks than its dyadic scale. -/
theorem inner_population (n j : ℕ) (hn : 8 ≤ n) (hj : j ≤ 2)
    (theta : ℝ) (htheta : 0 ≤ theta)
    (hsmall : (2 : ℝ) ^ n * theta ≤ 1 / 1000) :
    ((2 ^ n - 2 : ℕ) : ℝ) * (beta j - (2 : ℝ) ^ (n - j) * theta) >
      (StrongSeed.copies (n - j) : ℝ) * (1 - (2 : ℝ) ^ (n - j) * theta) := by
  obtain ⟨he, hu64, hu, hfour⟩ := rung_bounds n j hn hj
  have htwo : 2 ≤ 2 ^ n := by
    calc
      2 = 2 ^ 1 := by norm_num
      _ ≤ _ := Nat.pow_le_pow_right (by decide) (by omega)
  have hq : ((2 ^ n - 2 : ℕ) : ℝ) = (2 : ℝ) ^ n - 2 := by
    simp only [Nat.cast_sub htwo, Nat.cast_pow, Nat.cast_ofNat]
  have hb := beta_mul_width n j (by omega)
  have hb1 := beta_le j
  have hp := copies_cast (n - j) he
  have htu : 0 ≤ (2 : ℝ) ^ (n - j) * theta := mul_nonneg (by positivity) htheta
  have hc : 0 ≤ (StrongSeed.copies (n - j) : ℝ) := by positivity
  have hprod := mul_le_mul_of_nonneg_left hsmall
    (show 0 ≤ (2 : ℝ) ^ (n - j) by positivity)
  rw [hq, hp]
  nlinarith [mul_nonneg hc htu]

/-- The second interlace has exactly the dyadic number of blocks. -/
theorem outer_population (n j : ℕ) (hn : 8 ≤ n) (hj : j ≤ 2)
    (theta : ℝ) (htheta : 0 ≤ theta)
    (hsmall : (2 : ℝ) ^ n * theta ≤ 1 / 10000) :
    (2 : ℝ) ^ n * (beta j - (2 : ℝ) ^ (n - j) * theta) >
      (StrongSeed.copies (n - j) : ℝ) * (1 - (2 : ℝ) ^ (n - j) * theta) := by
  obtain ⟨he, hu64, hu, hfour⟩ := rung_bounds n j hn hj
  have hb := beta_mul_width n j (by omega)
  have hp := copies_cast (n - j) he
  have htu : 0 ≤ (2 : ℝ) ^ (n - j) * theta := mul_nonneg (by positivity) htheta
  have hc : 0 ≤ (StrongSeed.copies (n - j) : ℝ) := by positivity
  have hprod := mul_le_mul_of_nonneg_left hsmall
    (show 0 ≤ (2 : ℝ) ^ (n - j) by positivity)
  rw [hp]
  nlinarith [mul_nonneg hc htu]

/-- In the reference matrix, the template mixture has weight 255/256. -/
theorem reference_population (n j : ℕ) (hn : 8 ≤ n) (hj : j ≤ 2)
    (theta : ℝ) (htheta : 0 ≤ theta)
    (hsmall : (2 : ℝ) ^ n * theta ≤ 1 / 10000) :
    (2 : ℝ) ^ n * ((beta j - (1 - 255 / 256)) / (255 / 256) -
        (2 : ℝ) ^ (n - j) * theta) >
      (StrongSeed.copies (n - j) : ℝ) * (1 - (2 : ℝ) ^ (n - j) * theta) := by
  obtain ⟨he, hu64, hu, hfour⟩ := rung_bounds n j hn hj
  have hb := beta_mul_width n j (by omega)
  have hp := copies_cast (n - j) he
  have htu : 0 ≤ (2 : ℝ) ^ (n - j) * theta := mul_nonneg (by positivity) htheta
  have hc : 0 ≤ (StrongSeed.copies (n - j) : ℝ) := by positivity
  have hprod := mul_le_mul_of_nonneg_left hsmall
    (show 0 ≤ (2 : ℝ) ^ (n - j) by positivity)
  rw [hp]
  norm_num only [show (1 : ℝ) - 255 / 256 = 1 / 256 by norm_num,
    div_div_eq_mul_div, div_mul_eq_mul_div]
  nlinarith [mul_nonneg hc htu]

theorem density_threshold (L n j : ℕ) (hj : j ≤ n) (hj2 : j ≤ 2)
    (hwide : (10 * L : ℝ) ≤ (2 : ℝ) ^ n / 4096) :
    (2 : ℝ) ^ (-((2 : ℝ) ^ (n - j) / 1024)) ≤ x L := by
  have h4 : (2 : ℝ) ^ j ≤ 4 := by
    calc
      _ ≤ (2 : ℝ) ^ 2 := pow_le_pow_right₀ (by norm_num) hj2
      _ = 4 := by norm_num
  have hfactor := rung_factor n j hj
  have hwidth : (2 : ℝ) ^ n ≤ 4 * (2 : ℝ) ^ (n - j) := by
    rw [hfactor]
    exact mul_le_mul_of_nonneg_right h4 (by positivity)
  have hexp : -((2 : ℝ) ^ (n - j) / 1024) ≤ -((10 * L : ℕ) : ℝ) := by
    push_cast
    nlinarith
  calc
    _ ≤ (2 : ℝ) ^ (-((10 * L : ℕ) : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
    _ = x L := by
      rw [Real.rpow_neg (by norm_num), Real.rpow_natCast]
      simp only [x, one_div, inv_pow]

theorem width_density_guard (L : ℕ) : (10 * L : ℝ) ≤ (width L : ℝ) / 4096 := by
  have h : (65536 : ℝ) * (L + 1) ≤ width L := by exact_mod_cast width_admissible L
  nlinarith

end Paper2.SourceProfileParameters
