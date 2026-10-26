import CurrentAdditive.ConditioningFiniteTV
import Paper2.SourcePadding

/-!
Private v27 Appendix I `det:parameters` development.  This is the deterministic
schedule, unrelated to Appendix C's randomized quartic restoration schedule.
The public size is `N L = 2^L`; `s L = 2^ceil(L/4)` is encoded by integer
division.  The graph constants are a degree bound `Δ` and source density `γ`.
-/

namespace CurrentAdditive.DeterministicParameters

def N (L : ℕ) : ℕ := 2 ^ L
def s (L : ℕ) : ℕ := 2 ^ ((L + 3) / 4)
def q₁ (L : ℕ) : ℕ := s L - 2
def q₂ (L : ℕ) : ℕ := N L ^ 4
def w (L : ℕ) : ℕ := N L ^ 2
def Q (L : ℕ) : ℕ := N L ^ 6
def ρ (L : ℕ) : ℚ := 1 / N L
def x (L : ℕ) : ℚ := 1 / N L ^ 16

def c (Δ : ℕ) (γ : ℚ) : ℚ :=
  min 1 (min (γ / (4 * Δ)) (γ / (24 * 256))) / 65536

def reciprocalCut (Δ : ℕ) (γ : ℚ) : ℕ := Nat.ceil (1 / c Δ γ)

def η (L Δ : ℕ) (γ : ℚ) : ℚ := c Δ γ / s L
def δU (L Δ : ℕ) (γ : ℚ) : ℚ := η L Δ γ / (16 * w L)
def θ (L : ℕ) : ℚ := 1 / (512 * Q L)
def h (L : ℕ) : ℕ := 12 * L + 2 * ((L + 3) / 4)
noncomputable def ownerException (L Δ : ℕ) (γ : ℚ) : ℕ :=
  Nat.ceil ((16 * (CurrentAdditive.conditioningExceptionCount (θ L : ℝ)
    ((η L Δ γ / 2 : ℚ) : ℝ) : ℚ)) / 7)
def Kstar (L : ℕ) : ℕ := 8 * (L + 1) * s L

theorem N_pos (L : ℕ) : 0 < N L := by unfold N; positivity
theorem s_pos (L : ℕ) : 0 < s L := by unfold s; positivity
theorem q₂_pos (L : ℕ) : 0 < q₂ L := by unfold q₂ N; positivity
theorem w_pos (L : ℕ) : 0 < w L := by unfold w N; positivity
theorem Q_pos (L : ℕ) : 0 < Q L := by unfold Q N; positivity

theorem c_pos (Δ : ℕ) (γ : ℚ) (hΔ : 0 < Δ) (hγ : 0 < γ) :
    0 < c Δ γ := by
  unfold c
  have hΔq : (0 : ℚ) < (Δ : ℚ) := by exact_mod_cast hΔ
  positivity

theorem c_le_one (Δ : ℕ) (γ : ℚ) : c Δ γ ≤ 1 / 65536 := by
  unfold c
  have hh : min (1 : ℚ) (min (γ / (4 * Δ)) (γ / (24 * 256))) ≤ 1 := min_le_left _ _
  linarith

theorem c_le_deletion (Δ : ℕ) (γ : ℚ) :
    c Δ γ ≤ γ / (4 * Δ) / 65536 := by
  unfold c
  have hh : min (1 : ℚ) (min (γ / (4 * Δ)) (γ / (24 * 256))) ≤
      γ / (4 * Δ) := (min_le_right _ _).trans (min_le_left _ _)
  linarith

theorem c_le_mu_zeta (Δ : ℕ) (γ : ℚ) :
    c Δ γ ≤ (1 / 256 : ℚ) * (γ / 24) / 65536 := by
  unfold c
  have hh : min (1 : ℚ) (min (γ / (4 * Δ)) (γ / (24 * 256))) ≤
      γ / (24 * 256) := (min_le_right _ _).trans (min_le_right _ _)
  linarith

theorem eta_pos (L Δ : ℕ) (γ : ℚ) (hΔ : 0 < Δ) (hγ : 0 < γ) :
    0 < η L Δ γ := by
  unfold η
  exact div_pos (c_pos Δ γ hΔ hγ) (by exact_mod_cast s_pos L)

theorem deltaU_pos (L Δ : ℕ) (γ : ℚ) (hΔ : 0 < Δ) (hγ : 0 < γ) :
    0 < δU L Δ γ := by
  unfold δU
  have hw : (0 : ℚ) < (w L : ℚ) := by exact_mod_cast w_pos L
  have hη := eta_pos L Δ γ hΔ hγ
  positivity

theorem theta_pos (L : ℕ) : 0 < θ L := by
  unfold θ
  have hQ : (0 : ℚ) < (Q L : ℚ) := by exact_mod_cast Q_pos L
  positivity

theorem Q_theta (L : ℕ) : (Q L : ℚ) * θ L = 1 / 512 := by
  unfold θ
  have hQ : (Q L : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (Q_pos L))
  field_simp

theorem overhead_formula (L : ℕ) :
    h L = 2 * ((L + 3) / 4) + 4 * L + 2 * L + 4 * L + 2 * L := by
  unfold h
  omega

/-- Elementary effective domination: one extra exponent bit pays for each
unit of a fixed coefficient. This intentionally gives a very coarse cutoff. -/
private theorem coefficient_le_power (K : ℕ) : K ≤ 2 ^ K := by
  induction K with
  | zero => norm_num
  | succ K ih =>
      rw [pow_succ]
      have hp0 : 0 < 2 ^ K := pow_pos (by omega) _
      have hp : 1 ≤ 2 ^ K := by omega
      omega

theorem c_lower_dyadic (Δ : ℕ) (γ : ℚ) (hΔ : 0 < Δ) (hγ : 0 < γ) :
    (1 : ℚ) / (2 ^ reciprocalCut Δ γ) ≤ c Δ γ := by
  have hc := c_pos Δ γ hΔ hγ
  have hceil : (1 : ℚ) / c Δ γ ≤ reciprocalCut Δ γ :=
    Nat.le_ceil (1 / c Δ γ)
  have hd : reciprocalCut Δ γ ≤ 2 ^ reciprocalCut Δ γ :=
    coefficient_le_power (reciprocalCut Δ γ)
  have hdQ : (reciprocalCut Δ γ : ℚ) ≤ 2 ^ reciprocalCut Δ γ := by
    exact_mod_cast hd
  have hcd : (1 : ℚ) ≤ c Δ γ * (2 ^ reciprocalCut Δ γ) := by
    have hh := (div_le_iff₀ hc).1 hceil
    nlinarith [mul_le_mul_of_nonneg_left hdQ hc.le]
  have hp : (0 : ℚ) < (2 : ℚ) ^ reciprocalCut Δ γ := by positivity
  exact (div_le_iff₀ hp).2 (by simpa only [mul_comm] using hcd)

private theorem ceil_quarter_add (L K : ℕ) (hL : 2 * K + 4 ≤ L) :
    (L + 3) / 4 + K ≤ L := by
  have hdiv : 4 * ((L + 3) / 4) ≤ L + 3 := Nat.mul_div_le (L + 3) 4
  omega

/-- A usable source-only cutoff for `K*s ≤ N`, with no assumption that a
chosen schedule passes an admissibility test. -/
theorem coefficient_mul_s_le_N (K L : ℕ) (hL : 2 * K + 4 ≤ L) :
    K * s L ≤ N L := by
  unfold s N
  calc
    K * 2 ^ ((L + 3) / 4) ≤ 2 ^ K * 2 ^ ((L + 3) / 4) :=
      Nat.mul_le_mul_right _ (coefficient_le_power K)
    _ = 2 ^ (((L + 3) / 4) + K) := by rw [← pow_add]; congr 1; omega
    _ ≤ 2 ^ L := Nat.pow_le_pow_right (by decide) (ceil_quarter_add L K hL)

theorem s_le_N (L : ℕ) (hL : 6 ≤ L) : s L ≤ N L := by
  simpa using coefficient_mul_s_le_N 1 L (by omega)

theorem s_ge_64 (L : ℕ) (hL : 24 ≤ L) : 64 ≤ s L := by
  unfold s
  have he : 6 ≤ (L + 3) / 4 := by omega
  exact (show 2 ^ 6 ≤ 2 ^ ((L + 3) / 4) from
    Nat.pow_le_pow_right (by decide) he)

private theorem four_b_plus_one_le_pow (b : ℕ) (hb : 5 ≤ b) :
    4 * b + 1 ≤ 2 ^ b := by
  induction b, hb using Nat.le_induction with
  | base => norm_num
  | succ b hb ih =>
      rw [pow_succ]
      have hp : 5 ≤ 2 ^ b := by omega
      omega

theorem L_plus_one_le_s (L : ℕ) (hL : 24 ≤ L) : L + 1 ≤ s L := by
  let b := (L + 3) / 4
  have hb : 5 ≤ b := by omega
  have hceil : L ≤ 4 * b := by omega
  calc
    L + 1 ≤ 4 * b + 1 := by omega
    _ ≤ 2 ^ b := four_b_plus_one_le_pow b hb
    _ = s L := rfl

theorem four_s_sq_le_N (L : ℕ) (hL : 12 ≤ L) : 4 * s L ^ 2 ≤ N L := by
  unfold s N
  have he : 2 * ((L + 3) / 4) + 2 ≤ L := by
    have hd : 4 * ((L + 3) / 4) ≤ L + 3 := Nat.mul_div_le (L + 3) 4
    omega
  calc
    4 * (2 ^ ((L + 3) / 4)) ^ 2 = 2 ^ (2 * ((L + 3) / 4) + 2) := by
      rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul, ← pow_add]
      congr 1
      omega
    _ ≤ 2 ^ L := Nat.pow_le_pow_right (by decide) he

theorem q₂_eq_pow (L : ℕ) : q₂ L = 2 ^ (4 * L) := by
  unfold q₂ N
  rw [← pow_mul]
  congr 1
  omega

theorem w_eq_pow (L : ℕ) : w L = 2 ^ (2 * L) := by
  unfold w N
  rw [← pow_mul]
  congr 1
  omega

theorem Q_eq_pow (L : ℕ) : Q L = 2 ^ (6 * L) := by
  unfold Q N
  rw [← pow_mul]
  congr 1
  omega

theorem N_ge_four (L : ℕ) (hL : 2 ≤ L) : 4 ≤ N L := by
  unfold N
  exact (show 2 ^ 2 ≤ 2 ^ L from Nat.pow_le_pow_right (by decide) hL)

theorem q₂_mul_x (L : ℕ) : (q₂ L : ℚ) * x L = 1 / (N L : ℚ) ^ 12 := by
  unfold q₂ x
  have hN : (N L : ℚ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt (N_pos L)
  push_cast
  field_simp

theorem s_mul_x_le (L : ℕ) (hL : 6 ≤ L) :
    (s L : ℚ) * x L ≤ 1 / (N L : ℚ) ^ 15 := by
  have hs : (s L : ℚ) ≤ N L := by exact_mod_cast s_le_N L hL
  have hn : (0 : ℚ) < N L := by exact_mod_cast N_pos L
  have hx : 0 ≤ x L := by unfold x; positivity
  calc
    (s L : ℚ) * x L ≤ (N L : ℚ) * x L := mul_le_mul_of_nonneg_right hs hx
    _ = 1 / (N L : ℚ) ^ 15 := by
      unfold x
      have hne : (N L : ℚ) ≠ 0 := ne_of_gt hn
      field_simp

theorem q₂_mul_x_small (L : ℕ) (hL : 2 ≤ L) :
    (q₂ L : ℚ) * x L ≤ 1 / 10000 := by
  rw [q₂_mul_x]
  have hn : (4 : ℚ) ≤ N L := by exact_mod_cast N_ge_four L hL
  have hp : (10000 : ℚ) ≤ (N L : ℚ) ^ 12 := by
    have hh := pow_le_pow_left₀ (by norm_num : (0 : ℚ) ≤ 4) hn 12
    norm_num at hh
    nlinarith
  have hp0 : (0 : ℚ) < (N L : ℚ) ^ 12 := by positivity
  apply (div_le_iff₀ hp0).2
  nlinarith

theorem four_s_sq_rho (L : ℕ) (hL : 12 ≤ L) :
    4 * (s L : ℚ) ^ 2 * ρ L ≤ 1 := by
  have hs : (4 * s L ^ 2 : ℕ) ≤ N L := four_s_sq_le_N L hL
  have hsQ : (4 : ℚ) * (s L : ℚ) ^ 2 ≤ N L := by exact_mod_cast hs
  have hn : (0 : ℚ) < N L := by exact_mod_cast N_pos L
  unfold ρ
  rw [mul_one_div]
  exact (div_le_iff₀ hn).2 (by simpa using hsQ)

theorem s_rho_small (L : ℕ) (hL : 2004 ≤ L) :
    (s L : ℚ) * ρ L ≤ 1 / 1000 := by
  have hs : 1000 * s L ≤ N L := coefficient_mul_s_le_N 1000 L (by omega)
  have hsQ : (1000 : ℚ) * s L ≤ N L := by exact_mod_cast hs
  have hn : (0 : ℚ) < N L := by exact_mod_cast N_pos L
  unfold ρ
  rw [mul_one_div]
  apply (div_le_iff₀ hn).2
  nlinarith

theorem two_q₂_x_small (L : ℕ) (hL : 2 ≤ L) :
    2 * (q₂ L : ℚ) * x L ≤ 1 / 8 := by
  have hh := q₂_mul_x_small L hL
  nlinarith

theorem x_le_inverse_wsq_q₂ (L : ℕ) :
    x L ≤ 1 / ((w L : ℚ) ^ 2 * q₂ L) := by
  have hN : (0 : ℚ) < N L := by exact_mod_cast N_pos L
  have hN1 : (1 : ℚ) ≤ N L := by exact_mod_cast N_pos L
  have hpow : (N L : ℚ) ^ 8 ≤ (N L : ℚ) ^ 16 :=
    pow_le_pow_right₀ hN1 (by omega)
  unfold x w q₂
  push_cast
  have heq : ((N L : ℚ) ^ 2) ^ 2 * (N L : ℚ) ^ 4 = (N L : ℚ) ^ 8 := by ring
  rw [heq]
  exact one_div_le_one_div_of_le (pow_pos hN _) hpow

theorem x_le_rho (L : ℕ) : x L ≤ ρ L := by
  have hN : (0 : ℚ) < N L := by exact_mod_cast N_pos L
  have hN1 : (1 : ℚ) ≤ N L := by exact_mod_cast N_pos L
  have hp : (N L : ℚ) ≤ (N L : ℚ) ^ 16 := by
    simpa using pow_le_pow_right₀ hN1 (show 1 ≤ 16 by omega)
  unfold x ρ
  exact one_div_le_one_div_of_le hN hp

theorem s_x_small (L : ℕ) (hL : 2004 ≤ L) :
    (s L : ℚ) * x L ≤ 1 / 1000 := by
  have hs : (0 : ℚ) ≤ s L := by positivity
  calc
    (s L : ℚ) * x L ≤ (s L : ℚ) * ρ L :=
      mul_le_mul_of_nonneg_left (x_le_rho L) hs
    _ ≤ 1 / 1000 := s_rho_small L hL

theorem q₁_rho_small (L : ℕ) (hL : 2004 ≤ L) :
    (q₁ L : ℚ) * ρ L ≤ 1 / 1000 := by
  have hq : q₁ L ≤ s L := Nat.sub_le _ _
  have hqQ : (q₁ L : ℚ) ≤ s L := by exact_mod_cast hq
  have hr : 0 ≤ ρ L := by unfold ρ; positivity
  calc
    (q₁ L : ℚ) * ρ L ≤ (s L : ℚ) * ρ L := mul_le_mul_of_nonneg_right hqQ hr
    _ ≤ 1 / 1000 := s_rho_small L hL

/-- The three strict population margins of `det:profiles`. The first and
third bounds are uniform over all three profile rungs. -/
theorem profile_A_ratio (L : ℕ) (hL : 2004 ≤ L) :
    (3 / 5 : ℚ) * (1 - 2 / (s L : ℚ)) - (q₁ L : ℚ) * ρ L > 9 / 16 := by
  have hs : (64 : ℚ) ≤ s L := by exact_mod_cast s_ge_64 L (by omega)
  have hq := q₁_rho_small L hL
  have hsp : (0 : ℚ) < s L := by exact_mod_cast s_pos L
  have htwo : 2 / (s L : ℚ) ≤ 1 / 32 := by
    apply (div_le_iff₀ hsp).2
    nlinarith
  nlinarith

theorem profile_T_ratio (L : ℕ) (hL : 2 ≤ L) :
    (3 / 5 : ℚ) - (q₂ L : ℚ) * x L > 9 / 16 := by
  have hq := q₂_mul_x_small L hL
  linarith

theorem profile_Nref_ratio (L : ℕ) (hL : 2004 ≤ L) (j : Fin 3) :
    (2 : ℚ) ^ j.val *
      (((3 / 5 : ℚ) * (1 / 2 : ℚ) ^ j.val - (1 - (255 / 256 : ℚ))) /
        (255 / 256 : ℚ)) - (s L : ℚ) * x L > 9 / 16 := by
  have hx := s_x_small L hL
  have hj : j.val < 3 := j.isLt
  interval_cases hjv : j.val <;> norm_num [hjv] at * <;> linarith

theorem profile_A_ratio_real (L : ℕ) (hL : 2004 ≤ L) :
    (3 / 5 : ℝ) * (1 - 2 / (s L : ℝ)) - (q₁ L : ℝ) * (ρ L : ℝ) > 9 / 16 := by
  have hh : (((3 / 5 : ℚ) * (1 - 2 / (s L : ℚ)) -
      (q₁ L : ℚ) * ρ L : ℚ) : ℝ) > ((9 / 16 : ℚ) : ℝ) := by
    exact_mod_cast profile_A_ratio L hL
  simpa only [Rat.cast_sub, Rat.cast_mul, Rat.cast_div, Rat.cast_ofNat,
    Rat.cast_natCast, Rat.cast_one] using hh

theorem profile_T_ratio_real (L : ℕ) (hL : 2 ≤ L) :
    (3 / 5 : ℝ) - (q₂ L : ℝ) * (x L : ℝ) > 9 / 16 := by
  have hh : (((3 / 5 : ℚ) - (q₂ L : ℚ) * x L : ℚ) : ℝ) >
      ((9 / 16 : ℚ) : ℝ) := by exact_mod_cast profile_T_ratio L hL
  simpa only [Rat.cast_sub, Rat.cast_mul, Rat.cast_div, Rat.cast_ofNat,
    Rat.cast_natCast, Rat.cast_one] using hh

theorem profile_Nref_ratio_real (L : ℕ) (hL : 2004 ≤ L) (j : Fin 3) :
    (2 : ℝ) ^ j.val *
      (((3 / 5 : ℝ) * (1 / 2 : ℝ) ^ j.val - (1 - (255 / 256 : ℝ))) /
        (255 / 256 : ℝ)) - (s L : ℝ) * (x L : ℝ) > 9 / 16 := by
  have hh : (((2 : ℚ) ^ j.val *
      (((3 / 5 : ℚ) * (1 / 2 : ℚ) ^ j.val - (1 - (255 / 256 : ℚ))) /
        (255 / 256 : ℚ)) - (s L : ℚ) * x L : ℚ) : ℝ) >
        ((9 / 16 : ℚ) : ℝ) := by exact_mod_cast profile_Nref_ratio L hL j
  simpa only [Rat.cast_sub, Rat.cast_mul, Rat.cast_div, Rat.cast_ofNat,
    Rat.cast_natCast, Rat.cast_one, Rat.cast_pow] using hh

theorem x_real_pos (L : ℕ) : (0 : ℝ) < (x L : ℝ) := by
  have hx : (0 : ℚ) < x L := by
    unfold x
    have hn : (0 : ℚ) < N L := by exact_mod_cast N_pos L
    positivity
  exact_mod_cast hx

theorem x_real_le_one (L : ℕ) : (x L : ℝ) ≤ 1 := by
  have hx : x L ≤ (1 : ℚ) := by
    have hn : (1 : ℚ) ≤ N L := by exact_mod_cast N_pos L
    unfold x
    have hp : (1 : ℚ) ≤ (N L : ℚ) ^ 16 := one_le_pow₀ hn
    exact (div_le_iff₀ (lt_of_lt_of_le (by norm_num) hp)).2 (by simpa using hp)
  exact_mod_cast hx

theorem conditioning_epsilon_x_small (L : ℕ) :
    CurrentAdditive.conditioningEpsilon (x L : ℝ) 1 ≤ 1 / 1000 := by
  have hp : (x L : ℝ) ^ ((4 : ℝ) / 1024) ≤ 1 :=
    Real.rpow_le_one (x_real_pos L).le (x_real_le_one L) (by norm_num)
  unfold CurrentAdditive.conditioningEpsilon
  calc
    min (1 : ℝ) (2 ^ (-(20 : ℝ)) / 1024 * (x L : ℝ) ^ ((4 : ℝ) / 1024)) ≤
        2 ^ (-(20 : ℝ)) / 1024 * (x L : ℝ) ^ ((4 : ℝ) / 1024) := min_le_right _ _
    _ ≤ 2 ^ (-(20 : ℝ)) / 1024 := by
      apply mul_le_of_le_one_right
      · positivity
      · exact hp
    _ ≤ 1 / 1000 := by norm_num [Real.rpow_neg, Real.rpow_natCast]

private theorem x_real_dyadic (L : ℕ) :
    (x L : ℝ) = (2 : ℝ) ^ (-(16 * (L : ℝ))) := by
  simp only [x, Rat.cast_div, Rat.cast_one, Rat.cast_pow, N,
    Nat.cast_pow, Nat.cast_ofNat]
  rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
  change 1 / ((2 : ℝ) ^ L) ^ 16 = ((2 : ℝ) ^ (16 * (L : ℝ)))⁻¹
  rw [one_div, ← pow_mul]
  congr 1
  calc
    (2 : ℝ) ^ (L * 16) = (2 : ℝ) ^ ((L * 16 : ℕ) : ℝ) :=
      (Real.rpow_natCast _ _).symm
    _ = (2 : ℝ) ^ (16 * (L : ℝ)) := by congr 1; push_cast; ring

private theorem x_real_rpow_four (L : ℕ) :
    (x L : ℝ) ^ ((4 : ℝ) / 1024) = (2 : ℝ) ^ (-(L : ℝ) / 16) := by
  rw [x_real_dyadic, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
  congr 1
  ring

private theorem x_real_rpow_neg_two (L : ℕ) :
    (x L : ℝ) ^ (-(2 / (1024 : ℝ))) = (2 : ℝ) ^ ((L : ℝ) / 32) := by
  rw [x_real_dyadic, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
  congr 1
  ring

private theorem epsilon_x_eq (L : ℕ) :
    CurrentAdditive.conditioningEpsilon (x L : ℝ) 1 =
      (2 : ℝ) ^ (-(30 : ℝ) - (L : ℝ) / 16) := by
  have hv := x_real_rpow_four L
  have hvle : (x L : ℝ) ^ ((4 : ℝ) / 1024) ≤ 1 :=
    Real.rpow_le_one (x_real_pos L).le (x_real_le_one L) (by norm_num)
  have hcoeff : (2 : ℝ) ^ (-(20 : ℝ)) / 1024 = 2 ^ (-(30 : ℝ)) := by
    norm_num [Real.rpow_neg, Real.rpow_natCast]
  unfold CurrentAdditive.conditioningEpsilon
  rw [min_eq_right]
  · rw [hcoeff, hv, ← Real.rpow_add (by norm_num : 0 < (2 : ℝ))]
    congr 1
    ring
  · have hc : (2 : ℝ) ^ (-(20 : ℝ)) / 1024 ≤ 1 := by
      norm_num [Real.rpow_neg, Real.rpow_natCast]
    have hpos : 0 ≤ (2 : ℝ) ^ (-(20 : ℝ)) / 1024 := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hvle hpos]

private theorem exception_x_inner_eq (L : ℕ) :
    (1024 : ℝ) *
      (CurrentAdditive.conditioningEpsilon (x L : ℝ) 1) ^ (-(2 : ℝ)) *
      (x L : ℝ) ^ (-(2 / (1024 : ℝ))) =
      (2 : ℝ) ^ ((70 : ℝ) + 5 * (L : ℝ) / 32) := by
  rw [epsilon_x_eq, x_real_rpow_neg_two]
  have hh : ((2 : ℝ) ^ (-(30 : ℝ) - (L : ℝ) / 16)) ^ (-(2 : ℝ)) =
      (2 : ℝ) ^ (60 + (L : ℝ) / 8) := by
    rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    congr 1
    ring
  rw [hh]
  rw [show (1024 : ℝ) = 2 ^ (10 : ℝ) by norm_num [Real.rpow_natCast]]
  rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2),
    ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
  congr 1
  ring

private theorem ceil_five_thirtytwo (L : ℕ) :
    5 * (L : ℝ) / 32 ≤ (((5 * L + 31) / 32 : ℕ) : ℝ) := by
  have hh : 5 * L ≤ 32 * ((5 * L + 31) / 32) := by omega
  have hhR : (5 : ℝ) * L ≤ 32 * (((5 * L + 31) / 32 : ℕ) : ℝ) := by
    exact_mod_cast hh
  linarith

private theorem exception_x_count_upper (L : ℕ) :
    CurrentAdditive.conditioningExceptionCount (x L : ℝ) 1 ≤
      2 ^ (73 + (5 * L + 31) / 32) := by
  let a := (5 * L + 31) / 32
  have hinner : (2 : ℝ) ^ (70 + 5 * (L : ℝ) / 32) ≤
      (2 : ℝ) ^ ((70 + a : ℕ) : ℝ) := by
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
    have ha := ceil_five_thirtytwo L
    push_cast
    linarith
  have hceil : ⌈(2 : ℝ) ^ (70 + 5 * (L : ℝ) / 32)⌉₊ ≤ 2 ^ (70 + a) := by
    apply (Nat.ceil_le).2
    simpa only [Real.rpow_natCast, Nat.cast_pow, Nat.cast_ofNat] using hinner
  unfold CurrentAdditive.conditioningExceptionCount
  rw [exception_x_inner_eq]
  calc
    8 * ⌈(2 : ℝ) ^ (70 + 5 * (L : ℝ) / 32)⌉₊ ≤ 8 * 2 ^ (70 + a) :=
      Nat.mul_le_mul_left _ hceil
    _ = 2 ^ (73 + a) := by rw [show 8 = 2 ^ 3 by norm_num, ← pow_add]; congr 1; omega

/-- The exact Appendix H exceptional-coordinate count at the source mass `x`.
`L≥2004` is deliberately coarse but independent of the base matrix and round. -/
theorem conditioning_exception_x_small (L : ℕ) (hL : 2004 ≤ L) :
    128 * CurrentAdditive.conditioningExceptionCount (x L : ℝ) 1 ≤ s L := by
  let a := (5 * L + 31) / 32
  let b := (L + 3) / 4
  have he : 80 + a ≤ b := by
    have ha : 32 * a ≤ 5 * L + 31 := Nat.mul_div_le (5 * L + 31) 32
    have hb : L ≤ 4 * b := by omega
    omega
  have hcount := exception_x_count_upper L
  calc
    128 * CurrentAdditive.conditioningExceptionCount (x L : ℝ) 1 ≤
        128 * 2 ^ (73 + a) := Nat.mul_le_mul_left _ hcount
    _ = 2 ^ (80 + a) := by rw [show 128 = 2 ^ 7 by norm_num, ← pow_add]; congr 1; omega
    _ ≤ 2 ^ b := Nat.pow_le_pow_right (by decide) he
    _ = s L := rfl

private noncomputable def dyadicMass (a : ℕ) : ℝ := (2 : ℝ) ^ (-(a : ℝ))

private theorem dyadicMass_pos (a : ℕ) : 0 < dyadicMass a := by
  unfold dyadicMass
  positivity

private theorem dyadicMass_le_one (a : ℕ) : dyadicMass a ≤ 1 := by
  unfold dyadicMass
  exact Real.rpow_le_one_of_one_le_of_nonpos (by norm_num : (1 : ℝ) ≤ 2)
    (neg_nonpos.mpr (Nat.cast_nonneg _))

private theorem dyadicMass_nat (a : ℕ) :
    dyadicMass a = 1 / ((2 : ℝ) ^ a) := by
  unfold dyadicMass
  rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_natCast]
  simp [one_div]

private theorem dyadicMass_add (a b : ℕ) :
    dyadicMass (a + b) = dyadicMass a * dyadicMass b := by
  simp only [dyadicMass_nat, pow_add]
  ring

private theorem dyadicMass_s (L : ℕ) :
    dyadicMass ((L + 3) / 4) = 1 / (s L : ℝ) := by
  simp [dyadicMass_nat, s]

private theorem dyadicMass_w (L : ℕ) :
    dyadicMass (2 * L) = 1 / (w L : ℝ) := by
  simp [dyadicMass_nat, w_eq_pow]

private theorem eta_half_lower_dyadic (L Δ : ℕ) (γ : ℚ)
    (hΔ : 0 < Δ) (hγ : 0 < γ) :
    dyadicMass (reciprocalCut Δ γ + 1 + (L + 3) / 4) ≤
      ((η L Δ γ / 2 : ℚ) : ℝ) := by
  let d := reciprocalCut Δ γ
  have hcQ := c_lower_dyadic Δ γ hΔ hγ
  have hc : (1 : ℝ) / (2 : ℝ) ^ d ≤ (c Δ γ : ℝ) := by
    have hh : (((1 : ℚ) / (2 : ℚ) ^ d) : ℝ) ≤ (c Δ γ : ℝ) := by
      exact_mod_cast hcQ
    simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_pow, Rat.cast_ofNat] using hh
  have hs : (0 : ℝ) ≤ 1 / (2 * (s L : ℝ)) := by positivity
  calc
    dyadicMass (d + 1 + (L + 3) / 4) =
        dyadicMass d * dyadicMass 1 * dyadicMass ((L + 3) / 4) := by
      rw [dyadicMass_add, dyadicMass_add]
    _ = (1 / (2 : ℝ) ^ d) * (1 / (2 * (s L : ℝ))) := by
      rw [dyadicMass_nat, dyadicMass_nat, dyadicMass_s]
      norm_num
      ring
    _ ≤ (c Δ γ : ℝ) * (1 / (2 * (s L : ℝ))) :=
      mul_le_mul_of_nonneg_right hc hs
    _ = ((η L Δ γ / 2 : ℚ) : ℝ) := by
      simp only [η, Rat.cast_div, Rat.cast_ofNat, Rat.cast_natCast]
      ring

private theorem deltaU_half_lower_dyadic (L Δ : ℕ) (γ : ℚ)
    (hΔ : 0 < Δ) (hγ : 0 < γ) :
    dyadicMass (reciprocalCut Δ γ + 5 + (L + 3) / 4 + 2 * L) ≤
      ((δU L Δ γ / 2 : ℚ) : ℝ) := by
  let d := reciprocalCut Δ γ
  have hcQ := c_lower_dyadic Δ γ hΔ hγ
  have hc : (1 : ℝ) / (2 : ℝ) ^ d ≤ (c Δ γ : ℝ) := by
    have hh : (((1 : ℚ) / (2 : ℚ) ^ d) : ℝ) ≤ (c Δ γ : ℝ) := by
      exact_mod_cast hcQ
    simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_pow, Rat.cast_ofNat] using hh
  have hs : (0 : ℝ) ≤ 1 / (32 * (s L : ℝ) * (w L : ℝ)) := by positivity
  calc
    dyadicMass (d + 5 + (L + 3) / 4 + 2 * L) =
        dyadicMass d * dyadicMass 5 * dyadicMass ((L + 3) / 4) *
          dyadicMass (2 * L) := by
      simp only [dyadicMass_add]
    _ = (1 / (2 : ℝ) ^ d) * (1 / (32 * (s L : ℝ) * (w L : ℝ))) := by
      rw [dyadicMass_nat, dyadicMass_nat, dyadicMass_s, dyadicMass_w]
      norm_num
      ring
    _ ≤ (c Δ γ : ℝ) * (1 / (32 * (s L : ℝ) * (w L : ℝ))) :=
      mul_le_mul_of_nonneg_right hc hs
    _ = ((δU L Δ γ / 2 : ℚ) : ℝ) := by
      simp only [δU, η, Rat.cast_div, Rat.cast_ofNat, Rat.cast_natCast]
      have hs0 : (s L : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt (s_pos L)
      have hw0 : (w L : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt (w_pos L)
      push_cast
      field_simp
      ring

private theorem dyadic_epsilon_eq (a : ℕ) :
    CurrentAdditive.conditioningEpsilon (dyadicMass a) 1 =
      (2 : ℝ) ^ (-(30 : ℝ) - (a : ℝ) / 256) := by
  have hv : (dyadicMass a) ^ ((4 : ℝ) / 1024) =
      (2 : ℝ) ^ (-(a : ℝ) / 256) := by
    unfold dyadicMass
    rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    congr 1
    ring
  have hvle : dyadicMass a ^ ((4 : ℝ) / 1024) ≤ 1 :=
    Real.rpow_le_one (dyadicMass_pos a).le (dyadicMass_le_one a) (by norm_num)
  have hcoeff : (2 : ℝ) ^ (-(20 : ℝ)) / 1024 = 2 ^ (-(30 : ℝ)) := by
    norm_num [Real.rpow_neg, Real.rpow_natCast]
  unfold CurrentAdditive.conditioningEpsilon
  rw [min_eq_right]
  · rw [hcoeff, hv, ← Real.rpow_add (by norm_num : 0 < (2 : ℝ))]
    congr 1
    ring
  · have hc : (2 : ℝ) ^ (-(20 : ℝ)) / 1024 ≤ 1 := by
      norm_num [Real.rpow_neg, Real.rpow_natCast]
    have hpos : 0 ≤ (2 : ℝ) ^ (-(20 : ℝ)) / 1024 := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hvle hpos]

private theorem dyadic_exception_inner_eq (a : ℕ) :
    (1024 : ℝ) *
      (CurrentAdditive.conditioningEpsilon (dyadicMass a) 1) ^ (-(2 : ℝ)) *
      (dyadicMass a) ^ (-(2 / (1024 : ℝ))) =
      (2 : ℝ) ^ ((70 : ℝ) + 5 * (a : ℝ) / 512) := by
  rw [dyadic_epsilon_eq]
  have hv : dyadicMass a ^ (-(2 / (1024 : ℝ))) =
      (2 : ℝ) ^ ((a : ℝ) / 512) := by
    unfold dyadicMass
    rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    congr 1
    ring
  rw [hv]
  have hh : ((2 : ℝ) ^ (-(30 : ℝ) - (a : ℝ) / 256)) ^ (-(2 : ℝ)) =
      (2 : ℝ) ^ (60 + (a : ℝ) / 128) := by
    rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    congr 1
    ring
  rw [hh]
  rw [show (1024 : ℝ) = 2 ^ (10 : ℝ) by norm_num [Real.rpow_natCast]]
  rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2),
    ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
  congr 1
  ring

private theorem dyadic_exception_upper (a : ℕ) :
    CurrentAdditive.conditioningExceptionCount (dyadicMass a) 1 ≤
      2 ^ (73 + (5 * a + 511) / 512) := by
  let t := (5 * a + 511) / 512
  have ht : 5 * (a : ℝ) / 512 ≤ t := by
    have hh : 5 * a ≤ 512 * t := by omega
    have hhR : (5 : ℝ) * a ≤ 512 * (t : ℝ) := by exact_mod_cast hh
    linarith
  have hinner : (2 : ℝ) ^ (70 + 5 * (a : ℝ) / 512) ≤
      (2 : ℝ) ^ ((70 + t : ℕ) : ℝ) := by
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
    push_cast
    linarith
  have hceil : ⌈(2 : ℝ) ^ (70 + 5 * (a : ℝ) / 512)⌉₊ ≤ 2 ^ (70 + t) := by
    apply (Nat.ceil_le).2
    simpa only [Real.rpow_natCast, Nat.cast_pow, Nat.cast_ofNat] using hinner
  unfold CurrentAdditive.conditioningExceptionCount
  rw [dyadic_exception_inner_eq]
  calc
    8 * ⌈(2 : ℝ) ^ (70 + 5 * (a : ℝ) / 512)⌉₊ ≤ 8 * 2 ^ (70 + t) :=
      Nat.mul_le_mul_left _ hceil
    _ = 2 ^ (73 + t) := by rw [show 8 = 2 ^ 3 by norm_num, ← pow_add]; congr 1; omega

/-- A coarse bound that also covers a shrinking tolerance. `t` is any
integer for which the tolerance is at least `2^{-t}`. -/
private theorem dyadic_exception_upper_at_tolerance
    (a t : ℕ) (τ : ℝ) (hτ : (2 : ℝ) ^ (-(t : ℝ)) ≤ τ) :
    CurrentAdditive.conditioningExceptionCount (dyadicMass a) τ ≤
      2 ^ (13 + 2 * max t (30 + (a + 255) / 256) + (a + 511) / 512) := by
  let m := max t (30 + (a + 255) / 256)
  let u := (a + 511) / 512
  have hma : (30 : ℝ) + (a : ℝ) / 256 ≤ m := by
    have hd : a ≤ 256 * ((a + 255) / 256) := by omega
    have hdr : (a : ℝ) ≤ 256 * (((a + 255) / 256 : ℕ) : ℝ) := by exact_mod_cast hd
    have hm : 30 + (a + 255) / 256 ≤ m := le_max_right _ _
    have hmr : (30 : ℝ) + (((a + 255) / 256 : ℕ) : ℝ) ≤ m := by exact_mod_cast hm
    linarith
  have hmt : t ≤ m := le_max_left _ _
  have hmtR : (t : ℝ) ≤ m := by exact_mod_cast hmt
  have hsmall : (0 : ℝ) < (2 : ℝ) ^ (-(m : ℝ)) := by positivity
  have hsmallτ : (2 : ℝ) ^ (-(m : ℝ)) ≤ τ :=
    (Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
      (by linarith)).trans hτ
  have hsmallk : (2 : ℝ) ^ (-(m : ℝ)) ≤
      (2 : ℝ) ^ (-(30 : ℝ) - (a : ℝ) / 256) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) (by linarith)
  have hε : (2 : ℝ) ^ (-(m : ℝ)) ≤
      CurrentAdditive.conditioningEpsilon (dyadicMass a) τ := by
    unfold CurrentAdditive.conditioningEpsilon
    rw [show (2 : ℝ) ^ (-(20 : ℝ)) / 1024 = 2 ^ (-(30 : ℝ)) by
      norm_num [Real.rpow_neg, Real.rpow_natCast]]
    have hv : dyadicMass a ^ ((4 : ℝ) / 1024) =
        (2 : ℝ) ^ (-(a : ℝ) / 256) := by
      unfold dyadicMass
      rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
      congr 1
      ring
    rw [hv, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    have hsmallk' : (2 : ℝ) ^ (-(m : ℝ)) ≤
        (2 : ℝ) ^ (-(30 : ℝ) + -(a : ℝ) / 256) := by
      convert hsmallk using 1
      ring
    exact le_min hsmallτ hsmallk'
  have hεinv : (CurrentAdditive.conditioningEpsilon (dyadicMass a) τ) ^
      (-(2 : ℝ)) ≤ (2 : ℝ) ^ (2 * (m : ℝ)) := by
    have hh := Real.rpow_le_rpow_of_nonpos hsmall hε (by norm_num : -(2 : ℝ) ≤ 0)
    convert hh using 1
    rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    congr 1
    ring
  have hau : (a : ℝ) / 512 ≤ u := by
    have hd : a ≤ 512 * u := by omega
    have hdr : (a : ℝ) ≤ 512 * (u : ℝ) := by exact_mod_cast hd
    linarith
  have hvpow : dyadicMass a ^ (-(2 / (1024 : ℝ))) ≤ (2 : ℝ) ^ (u : ℝ) := by
    have hv : dyadicMass a ^ (-(2 / (1024 : ℝ))) =
        (2 : ℝ) ^ ((a : ℝ) / 512) := by
      unfold dyadicMass
      rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
      congr 1
      ring
    rw [hv]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hau
  have hinner : (1024 : ℝ) *
      (CurrentAdditive.conditioningEpsilon (dyadicMass a) τ) ^ (-(2 : ℝ)) *
      dyadicMass a ^ (-(2 / (1024 : ℝ))) ≤
      (2 : ℝ) ^ ((10 + 2 * m + u : ℕ) : ℝ) := by
    have hεpos : 0 < CurrentAdditive.conditioningEpsilon (dyadicMass a) τ :=
      lt_of_lt_of_le hsmall hε
    have hnonneg : 0 ≤ (CurrentAdditive.conditioningEpsilon (dyadicMass a) τ) ^
        (-(2 : ℝ)) := (Real.rpow_pos_of_pos hεpos _).le
    have hvnonneg : 0 ≤ dyadicMass a ^ (-(2 / (1024 : ℝ))) :=
      (Real.rpow_pos_of_pos (dyadicMass_pos a) _).le
    calc
      _ ≤ (1024 : ℝ) * (2 : ℝ) ^ (2 * (m : ℝ)) *
          dyadicMass a ^ (-(2 / (1024 : ℝ))) := by
        gcongr
      _ ≤ (1024 : ℝ) * (2 : ℝ) ^ (2 * (m : ℝ)) * (2 : ℝ) ^ (u : ℝ) := by
        gcongr
      _ = (2 : ℝ) ^ ((10 + 2 * m + u : ℕ) : ℝ) := by
        rw [show (1024 : ℝ) = 2 ^ (10 : ℝ) by norm_num [Real.rpow_natCast]]
        rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2),
          ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
        congr 1
        push_cast
        ring
  have hceil : ⌈(1024 : ℝ) *
      (CurrentAdditive.conditioningEpsilon (dyadicMass a) τ) ^ (-(2 : ℝ)) *
      dyadicMass a ^ (-(2 / (1024 : ℝ)))⌉₊ ≤ 2 ^ (10 + 2 * m + u) := by
    apply (Nat.ceil_le).2
    simpa only [Nat.cast_pow, Nat.cast_ofNat, Real.rpow_natCast] using hinner
  unfold CurrentAdditive.conditioningExceptionCount
  calc
    8 * ⌈(1024 : ℝ) *
        (CurrentAdditive.conditioningEpsilon (dyadicMass a) τ) ^ (-(2 : ℝ)) *
        dyadicMass a ^ (-(2 / (1024 : ℝ)))⌉₊ ≤ 8 * 2 ^ (10 + 2 * m + u) :=
      Nat.mul_le_mul_left _ hceil
    _ = 2 ^ (13 + 2 * m + u) := by
      rw [show 8 = 2 ^ 3 by norm_num, ← pow_add]
      congr 1
      omega

private theorem theta_real_dyadic (L : ℕ) :
    (θ L : ℝ) = dyadicMass (9 + 6 * L) := by
  unfold θ dyadicMass
  simp only [Rat.cast_div, Rat.cast_one, Rat.cast_mul, Rat.cast_natCast]
  rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_natCast]
  rw [one_div]
  congr 1
  norm_cast
  rw [Q_eq_pow, pow_add, pow_mul]
  norm_num

private theorem theta_quarter_real_dyadic (L : ℕ) :
    ((θ L / 4 : ℚ) : ℝ) = dyadicMass (11 + 6 * L) := by
  rw [Rat.cast_div, Rat.cast_ofNat, theta_real_dyadic]
  unfold dyadicMass
  rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2),
    Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
  rw [Real.rpow_natCast, Real.rpow_natCast]
  rw [div_eq_inv_mul, ← mul_inv_rev]
  congr 1
  rw [pow_add, pow_add]
  norm_num
  ring

private theorem rho_real_dyadic (L : ℕ) :
    (ρ L : ℝ) = dyadicMass L := by
  unfold ρ dyadicMass
  simp only [Rat.cast_div, Rat.cast_one, Rat.cast_natCast]
  rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_natCast]
  rw [one_div]
  congr 1
  simp [N]

theorem conditioning_exception_theta_small (L : ℕ) (hL : 2004 ≤ L) :
    128 * CurrentAdditive.conditioningExceptionCount (θ L : ℝ) 1 ≤ w L := by
  let t := (5 * (9 + 6 * L) + 511) / 512
  have ht : 80 + t ≤ 2 * L := by
    have hd : 512 * t ≤ 5 * (9 + 6 * L) + 511 := Nat.mul_div_le _ 512
    omega
  rw [theta_real_dyadic]
  have hh := dyadic_exception_upper (9 + 6 * L)
  calc
    128 * CurrentAdditive.conditioningExceptionCount (dyadicMass (9 + 6 * L)) 1 ≤
        128 * 2 ^ (73 + t) := Nat.mul_le_mul_left _ hh
    _ = 2 ^ (80 + t) := by rw [show 128 = 2 ^ 7 by norm_num, ← pow_add]; congr 1; omega
    _ ≤ 2 ^ (2 * L) := Nat.pow_le_pow_right (by decide) ht
    _ = w L := (w_eq_pow L).symm

theorem conditioning_exception_theta_quarter_small (L : ℕ) (hL : 2004 ≤ L) :
    CurrentAdditive.conditioningExceptionCount ((θ L / 4 : ℚ) : ℝ) 1 ≤ s L * q₂ L := by
  let t := (5 * (11 + 6 * L) + 511) / 512
  have ht : 73 + t ≤ 4 * L := by
    have hd : 512 * t ≤ 5 * (11 + 6 * L) + 511 := Nat.mul_div_le _ 512
    omega
  rw [theta_quarter_real_dyadic]
  have hh := dyadic_exception_upper (11 + 6 * L)
  calc
    CurrentAdditive.conditioningExceptionCount (dyadicMass (11 + 6 * L)) 1 ≤
        2 ^ (73 + t) := hh
    _ ≤ 2 ^ (4 * L) := Nat.pow_le_pow_right (by decide) ht
    _ = q₂ L := (q₂_eq_pow L).symm
    _ ≤ s L * q₂ L := Nat.le_mul_of_pos_left (q₂ L) (s_pos L)

theorem conditioning_exception_theta_eta_upper (L Δ : ℕ) (γ : ℚ)
    (hΔ : 0 < Δ) (hγ : 0 < γ)
    (hL : 6 * reciprocalCut Δ γ + 2004 ≤ L) :
    CurrentAdditive.conditioningExceptionCount (θ L : ℝ)
      ((η L Δ γ / 2 : ℚ) : ℝ) ≤ N L := by
  let d := reciprocalCut Δ γ
  let b := (L + 3) / 4
  let a := 9 + 6 * L
  let t := d + 1 + b
  let m := max t (30 + (a + 255) / 256)
  let u := (a + 511) / 512
  have hexp : 13 + 2 * m + u ≤ L := by
    have hdL : 6 * d + 2004 ≤ L := hL
    have hb : 4 * b ≤ L + 3 := Nat.mul_div_le _ 4
    have hm1 : 256 * ((a + 255) / 256) ≤ a + 255 := Nat.mul_div_le _ 256
    have hu : 512 * u ≤ a + 511 := Nat.mul_div_le _ 512
    have hcase1 : 13 + 2 * t + u ≤ L := by omega
    have hcase2 : 13 + 2 * (30 + (a + 255) / 256) + u ≤ L := by omega
    rcases le_total t (30 + (a + 255) / 256) with h | h
    · simpa [m, max_eq_right h] using hcase2
    · simpa [m, max_eq_left h] using hcase1
  have hτ := eta_half_lower_dyadic L Δ γ hΔ hγ
  rw [theta_real_dyadic]
  have hh := dyadic_exception_upper_at_tolerance a t
    ((η L Δ γ / 2 : ℚ) : ℝ) hτ
  calc
    CurrentAdditive.conditioningExceptionCount (dyadicMass a)
        ((η L Δ γ / 2 : ℚ) : ℝ) ≤ 2 ^ (13 + 2 * m + u) := hh
    _ ≤ 2 ^ L := Nat.pow_le_pow_right (by decide) hexp
    _ = N L := rfl

theorem conditioning_exception_rho_delta_upper (L Δ : ℕ) (γ : ℚ)
    (hΔ : 0 < Δ) (hγ : 0 < γ)
    (hL : 6 * reciprocalCut Δ γ + 2004 ≤ L) :
    CurrentAdditive.conditioningExceptionCount (ρ L : ℝ)
      ((δU L Δ γ / 2 : ℚ) : ℝ) ≤ N L ^ 5 := by
  let d := reciprocalCut Δ γ
  let b := (L + 3) / 4
  let a := L
  let t := d + 5 + b + 2 * L
  let m := max t (30 + (a + 255) / 256)
  let u := (a + 511) / 512
  have hexp : 13 + 2 * m + u ≤ 5 * L := by
    have hdL : 6 * d + 2004 ≤ L := hL
    have hb : 4 * b ≤ L + 3 := Nat.mul_div_le _ 4
    have hu : 512 * u ≤ a + 511 := Nat.mul_div_le _ 512
    have hcase1 : 13 + 2 * t + u ≤ 5 * L := by omega
    have hcase2 : 13 + 2 * (30 + (a + 255) / 256) + u ≤ 5 * L := by omega
    rcases le_total t (30 + (a + 255) / 256) with h | h
    · simpa [m, max_eq_right h] using hcase2
    · simpa [m, max_eq_left h] using hcase1
  have hτ := deltaU_half_lower_dyadic L Δ γ hΔ hγ
  rw [rho_real_dyadic]
  have hh := dyadic_exception_upper_at_tolerance a t
    ((δU L Δ γ / 2 : ℚ) : ℝ) hτ
  calc
    CurrentAdditive.conditioningExceptionCount (dyadicMass a)
        ((δU L Δ γ / 2 : ℚ) : ℝ) ≤ 2 ^ (13 + 2 * m + u) := hh
    _ ≤ 2 ^ (5 * L) := Nat.pow_le_pow_right (by decide) hexp
    _ = N L ^ 5 := by simp [N, ← pow_mul, mul_comm]

theorem conditioning_exception_rho_delta_Q (L Δ : ℕ) (γ : ℚ)
    (hΔ : 0 < Δ) (hγ : 0 < γ)
    (hL : 6 * reciprocalCut Δ γ + 2004 ≤ L) :
    128 * (CurrentAdditive.conditioningExceptionCount (ρ L : ℝ)
      ((δU L Δ γ / 2 : ℚ) : ℝ) + 1) ≤ Q L := by
  have he := conditioning_exception_rho_delta_upper L Δ γ hΔ hγ hL
  have hp0 : 0 < N L ^ 5 := pow_pos (N_pos L) _
  have hp : 1 ≤ N L ^ 5 := by omega
  have h1 : CurrentAdditive.conditioningExceptionCount (ρ L : ℝ)
      ((δU L Δ γ / 2 : ℚ) : ℝ) + 1 ≤ 2 * N L ^ 5 := by omega
  calc
    128 * (CurrentAdditive.conditioningExceptionCount (ρ L : ℝ)
        ((δU L Δ γ / 2 : ℚ) : ℝ) + 1) ≤ 128 * (2 * N L ^ 5) :=
      Nat.mul_le_mul_left _ h1
    _ = 2 ^ (5 * L + 8) := by simp [N, ← pow_mul, pow_add]; ring
    _ ≤ 2 ^ (6 * L) := Nat.pow_le_pow_right (by decide) (by omega)
    _ = Q L := (Q_eq_pow L).symm

private theorem ceiling_sixteen_sevenths (e : ℕ) :
    Nat.ceil ((16 * (e : ℚ)) / 7) ≤ 3 * e := by
  apply (Nat.ceil_le).2
  push_cast
  nlinarith

theorem ownerException_le_three_N (L Δ : ℕ) (γ : ℚ)
    (hΔ : 0 < Δ) (hγ : 0 < γ)
    (hL : 6 * reciprocalCut Δ γ + 2004 ≤ L) :
    ownerException L Δ γ ≤ 3 * N L := by
  have he := conditioning_exception_theta_eta_upper L Δ γ hΔ hγ hL
  unfold ownerException
  exact (ceiling_sixteen_sevenths _).trans (Nat.mul_le_mul_left 3 he)

theorem ownerException_quarter (L Δ : ℕ) (γ : ℚ)
    (hΔ : 0 < Δ) (hγ : 0 < γ)
    (hL : 6 * reciprocalCut Δ γ + 2004 ≤ L) :
    4 * ownerException L Δ γ ≤ w L := by
  have he := ownerException_le_three_N L Δ γ hΔ hγ hL
  have hN : 12 ≤ N L := by
    unfold N
    exact (show 2 ^ 4 ≤ 2 ^ L from Nat.pow_le_pow_right (by decide) (by omega)).trans'
      (by norm_num : 12 ≤ 2 ^ 4)
  calc
    4 * ownerException L Δ γ ≤ 4 * (3 * N L) := Nat.mul_le_mul_left _ he
    _ = 12 * N L := by ring
    _ ≤ N L ^ 2 := by nlinarith [N_pos L]
    _ = w L := rfl

private theorem cubic_s_dyadic_cutoff (L d : ℕ) (hL : 6 * d + 2004 ≤ L) :
    384 * 2 ^ d * s L ^ 3 ≤ N L := by
  let b := (L + 3) / 4
  have hb : 4 * b ≤ L + 3 := Nat.mul_div_le _ 4
  have he : 9 + d + 3 * b ≤ L := by omega
  calc
    384 * 2 ^ d * s L ^ 3 ≤ 512 * 2 ^ d * s L ^ 3 :=
      (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by norm_num : 384 ≤ 512)))
    _ = 2 ^ (9 + d + 3 * b) := by
      rw [show 512 = 2 ^ 9 by norm_num, show s L = 2 ^ b by rfl,
        ← pow_mul, ← pow_add, ← pow_add]
      congr 1
      omega
    _ ≤ 2 ^ L := Nat.pow_le_pow_right (by decide) he
    _ = N L := rfl

theorem s_le_cN (L Δ : ℕ) (γ : ℚ)
    (hΔ : 0 < Δ) (hγ : 0 < γ)
    (hL : 6 * reciprocalCut Δ γ + 2004 ≤ L) :
    (s L : ℚ) ≤ c Δ γ * N L := by
  let d := reciprocalCut Δ γ
  let b := (L + 3) / 4
  have hb : 4 * b ≤ L + 3 := Nat.mul_div_le _ 4
  have he : d + b ≤ L := by omega
  have hnat : 2 ^ d * s L ≤ N L := by
    calc
      2 ^ d * s L = 2 ^ (d + b) := by rw [show s L = 2 ^ b by rfl, ← pow_add]
      _ ≤ 2 ^ L := Nat.pow_le_pow_right (by decide) he
      _ = N L := rfl
  have hq : (2 : ℚ) ^ d * s L ≤ N L := by exact_mod_cast hnat
  have hc := c_lower_dyadic Δ γ hΔ hγ
  have hp : (0 : ℚ) < (2 : ℚ) ^ d := by positivity
  have hn : (0 : ℚ) ≤ N L := by exact_mod_cast (N_pos L).le
  calc
    (s L : ℚ) ≤ (N L : ℚ) / (2 : ℚ) ^ d :=
      (le_div_iff₀ hp).2 (by simpa only [mul_comm] using hq)
    _ = (1 / (2 : ℚ) ^ d) * N L := by ring
    _ ≤ c Δ γ * N L := mul_le_mul_of_nonneg_right hc hn

private theorem moment_guard (L C : ℕ) (hL : C + 2004 ≤ L) :
    (2048 * C * Q L : ℕ) ≤ s L ^ 128 := by
  let b := (L + 3) / 4
  have hb : L ≤ 4 * b := by omega
  have he : 11 + C + 6 * L ≤ 128 * b := by omega
  have hC := coefficient_le_power C
  calc
    2048 * C * Q L ≤ 2048 * 2 ^ C * Q L := by gcongr
    _ = 2 ^ (11 + C + 6 * L) := by
      rw [show 2048 = 2 ^ 11 by norm_num, Q_eq_pow,
        ← pow_add, ← pow_add]
    _ ≤ 2 ^ (128 * b) := Nat.pow_le_pow_right (by decide) he
    _ = s L ^ 128 := by
      rw [show s L = 2 ^ b by rfl, ← pow_mul]
      congr 1
      omega

theorem moment_guard_rational (L C : ℕ) (hL : C + 2004 ≤ L) :
    (C : ℚ) / (s L : ℚ) ^ 128 ≤ θ L / 4 := by
  have hpow := moment_guard L C hL
  have hs : (0 : ℚ) < (s L : ℚ) ^ 128 := by
    have hh : (0 : ℚ) < s L := by exact_mod_cast s_pos L
    positivity
  have hq : (0 : ℚ) < (Q L : ℚ) := by exact_mod_cast Q_pos L
  have hpowQ : (2048 : ℚ) * C * Q L ≤ (s L : ℚ) ^ 128 := by
    exact_mod_cast hpow
  have hden : (0 : ℚ) < (2048 : ℚ) * Q L := by positivity
  have hh : (C : ℚ) ≤ (s L : ℚ) ^ 128 / ((2048 : ℚ) * Q L) :=
    (le_div_iff₀ hden).2 (by convert hpowQ using 1 <;> ring)
  calc
    (C : ℚ) / (s L : ℚ) ^ 128 ≤
        ((s L : ℚ) ^ 128 / ((2048 : ℚ) * Q L)) /
          (s L : ℚ) ^ 128 := div_le_div_of_nonneg_right hh hs.le
    _ = θ L / 4 := by
      unfold θ
      have hs0 : (s L : ℚ) ^ 128 ≠ 0 := ne_of_gt hs
      have hq0 : (Q L : ℚ) ≠ 0 := ne_of_gt hq
      field_simp
      have hss : (s L : ℚ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt (s_pos L)
      field_simp [hss]
      norm_num

theorem s_le_q₂ (L : ℕ) (hL : 6 ≤ L) : s L ≤ q₂ L := by
  have hs := s_le_N L hL
  have hn : 1 ≤ N L := N_pos L
  unfold q₂
  exact hs.trans (by simpa using
    (pow_le_pow_right₀ hn (show 1 ≤ 4 by omega)))

theorem w_le_q₂ (L : ℕ) : w L ≤ q₂ L := by
  have hn : 1 ≤ N L := N_pos L
  unfold w q₂
  exact pow_le_pow_right₀ hn (by omega)

theorem scalar_x_all_small (L : ℕ) (hL : 6 ≤ L) :
    (q₂ L : ℚ) * x L ≤ 1 / 10000 ∧
    (s L : ℚ) * x L ≤ 1 / 10000 ∧
    (w L : ℚ) * x L ≤ 1 / 10000 := by
  have hx : 0 ≤ x L := by unfold x; positivity
  have hs : (s L : ℚ) ≤ q₂ L := by exact_mod_cast s_le_q₂ L hL
  have hw : (w L : ℚ) ≤ q₂ L := by exact_mod_cast w_le_q₂ L
  have hq := q₂_mul_x_small L (by omega)
  exact ⟨hq,
    (mul_le_mul_of_nonneg_right hs hx).trans hq,
    (mul_le_mul_of_nonneg_right hw hx).trans hq⟩

theorem rho_le_eta (L Δ : ℕ) (γ : ℚ)
    (hΔ : 0 < Δ) (hγ : 0 < γ)
    (hL : 6 * reciprocalCut Δ γ + 2004 ≤ L) :
    ρ L ≤ η L Δ γ := by
  have hs := s_le_cN L Δ γ hΔ hγ hL
  have hc := c_pos Δ γ hΔ hγ
  have hn : (0 : ℚ) < N L := by exact_mod_cast N_pos L
  have hsq : (0 : ℚ) < s L := by exact_mod_cast s_pos L
  unfold ρ η
  apply (le_div_iff₀ hsq).2
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ hn).2
  convert hs using 1 <;> ring

theorem eta_le_one (L Δ : ℕ) (γ : ℚ) :
    η L Δ γ ≤ 1 / 65536 := by
  have hc := c_le_one Δ γ
  have hs : (1 : ℚ) ≤ s L := by exact_mod_cast s_pos L
  have hsn : (0 : ℚ) < s L := by exact_mod_cast s_pos L
  unfold η
  apply (div_le_iff₀ hsn).2
  nlinarith

theorem fixed_eta_guards (L Δ : ℕ) (γ : ℚ)
    (hΔ : 0 < Δ) (hγ : 0 < γ) :
    η L Δ γ / (1 / 256 : ℚ) < 1 / 100 ∧
    η L Δ γ * s L / (255 / 256 : ℚ) < 1 / 1000 ∧
    δU L Δ γ ≤ 1 / 64 := by
  have he := eta_le_one L Δ γ
  have hc := c_le_one Δ γ
  have hη := eta_pos L Δ γ hΔ hγ
  have hs : (0 : ℚ) < s L := by exact_mod_cast s_pos L
  have hw : (1 : ℚ) ≤ w L := by exact_mod_cast w_pos L
  have hηs : η L Δ γ * s L = c Δ γ := by
    unfold η
    field_simp
  constructor
  · norm_num at *
    linarith
  constructor
  · rw [hηs]
    norm_num at *
    linarith
  · unfold δU
    apply (div_le_iff₀ (by positivity : (0 : ℚ) < (16 : ℚ) * w L)).2
    nlinarith

theorem q₂_x_le_rho_div32 (L : ℕ) (hL : 2 ≤ L) :
    (q₂ L : ℚ) * x L ≤ ρ L / 32 := by
  rw [q₂_mul_x]
  have hn : (4 : ℚ) ≤ N L := by exact_mod_cast N_ge_four L hL
  have hp : (32 : ℚ) ≤ (N L : ℚ) ^ 11 := by
    have hh := pow_le_pow_left₀ (by norm_num : (0 : ℚ) ≤ 4) hn 11
    norm_num at hh
    linarith
  have hn0 : (0 : ℚ) < N L := by exact_mod_cast N_pos L
  have hmul := mul_le_mul_of_nonneg_right hp hn0.le
  have hpow : (32 : ℚ) * N L ≤ (N L : ℚ) ^ 12 := by
    nlinarith [hmul]
  unfold ρ
  have hden : (0 : ℚ) < (N L : ℚ) ^ 12 := by positivity
  have hdiv : (1 / (N L : ℚ)) / 32 = 1 / (32 * N L) := by
    field_simp
  rw [hdiv]
  exact one_div_le_one_div_of_le
    (by positivity : (0 : ℚ) < 32 * N L) hpow

theorem w_q₂_x_le_rho (L : ℕ) :
    (w L : ℚ) * q₂ L * x L ≤ ρ L := by
  have hn : (0 : ℚ) < N L := by exact_mod_cast N_pos L
  have hn1 : (1 : ℚ) ≤ N L := by exact_mod_cast N_pos L
  have hp : (N L : ℚ) ≤ (N L : ℚ) ^ 10 := by
    simpa using pow_le_pow_right₀ hn1 (show 1 ≤ 10 by omega)
  have hnn : (N L : ℚ) ≠ 0 := ne_of_gt hn
  unfold w q₂ x ρ
  push_cast
  have heq : (N L : ℚ) ^ 2 * (N L : ℚ) ^ 4 *
      (1 / (N L : ℚ) ^ 16) = 1 / (N L : ℚ) ^ 10 := by field_simp
  rw [heq]
  exact one_div_le_one_div_of_le hn hp

theorem w_div_q₂_le_rho (L : ℕ) :
    (w L : ℚ) / q₂ L ≤ ρ L := by
  have hn : (0 : ℚ) < N L := by exact_mod_cast N_pos L
  have hn1 : (1 : ℚ) ≤ N L := by exact_mod_cast N_pos L
  have hp : (N L : ℚ) ≤ (N L : ℚ) ^ 2 := by
    simpa using pow_le_pow_right₀ hn1 (show 1 ≤ 2 by omega)
  have hnn : (N L : ℚ) ≠ 0 := ne_of_gt hn
  unfold w q₂ ρ
  push_cast
  have heq : (N L : ℚ) ^ 2 / (N L : ℚ) ^ 4 =
      1 / (N L : ℚ) ^ 2 := by field_simp
  rw [heq]
  exact one_div_le_one_div_of_le hn hp

theorem scalar_eta_guards (L Δ : ℕ) (γ : ℚ)
    (hΔ : 0 < Δ) (hγ : 0 < γ)
    (hL : 6 * reciprocalCut Δ γ + 2004 ≤ L) :
    2 * (w L : ℚ) * x L + η L Δ γ / (16 * (127 / 128 : ℚ)) < 1 ∧
    2 * (w L : ℚ) ^ 2 * x L ≤
      η L Δ γ / (16 * (127 / 128 : ℚ)) ∧
    4 * (1 / 256 : ℚ) * w L * q₂ L * x L ≤ η L Δ γ / 32 ∧
    4 * (1 / 256 : ℚ) * w L / q₂ L ≤ η L Δ γ / 32 := by
  have he := eta_le_one L Δ γ
  have hη := eta_pos L Δ γ hΔ hγ
  have hr := rho_le_eta L Δ γ hΔ hγ hL
  have hx := (scalar_x_all_small L (by omega)).2.2
  have hq := q₂_x_le_rho_div32 L (by omega)
  have hwq := w_q₂_x_le_rho L
  have hwr := w_div_q₂_le_rho L
  have hsq : (w L : ℚ) ^ 2 = q₂ L := by
    unfold w q₂
    push_cast
    ring
  constructor
  · norm_num at *
    linarith
  constructor
  · rw [hsq]
    norm_num at *
    linarith
  constructor
  · norm_num at *
    linarith
  · calc
      4 * (1 / 256 : ℚ) * w L / q₂ L =
          (1 / 64 : ℚ) * ((w L : ℚ) / q₂ L) := by ring
      _ ≤ (1 / 64 : ℚ) * ρ L :=
        mul_le_mul_of_nonneg_left hwr (by norm_num)
      _ ≤ η L Δ γ / 32 := by linarith

theorem q₂_large_for_graph (L Δ n m : ℕ)
    (hL : 24 * Δ + 2004 ≤ L) (hn : n ≤ N L)
    (hm : 0 < m) (hdegree : 2 * m ≤ Δ * n) :
    Paper2.SourcePadding.powTwoCeil (12 * s L * m) ≤ q₂ L := by
  have hs : 12 * Δ * s L ≤ N L := by
    simpa only [mul_assoc, mul_comm, mul_left_comm] using
      coefficient_mul_s_le_N (12 * Δ) L (by omega)
  have hsn := Nat.mul_le_mul_right n hs
  have hnn := Nat.mul_le_mul_left (N L) hn
  have hN : 1 ≤ N L := N_pos L
  have hpow : N L ^ 2 ≤ N L ^ 4 := pow_le_pow_right₀ hN (by omega)
  have h2 : 2 * (12 * s L * m) ≤ q₂ L := by
    calc
      2 * (12 * s L * m) = (12 * s L) * (2 * m) := by ring
      _ ≤ (12 * s L) * (Δ * n) := Nat.mul_le_mul_left _ hdegree
      _ = (12 * Δ * s L) * n := by ring
      _ ≤ N L * n := hsn
      _ ≤ N L ^ 2 := by simpa only [pow_two] using hnn
      _ ≤ q₂ L := by simpa only [q₂] using hpow
  have hpos : 0 < 12 * s L * m := by
    have hsp := s_pos L
    positivity
  exact (Nat.le_of_lt (Paper2.SourcePadding.powTwoCeil_lt_two_mul hpos)).trans h2

theorem q₂_large_for_rows (L n : ℕ) (hL : 6 ≤ L)
    (hn : n ≤ N L) : 2 * (n + s L - 3) ≤ q₂ L := by
  have hs := s_le_N L hL
  have hN : 4 ≤ N L := N_ge_four L (by omega)
  have hpow : 4 * N L ≤ q₂ L := by
    unfold q₂
    calc
      4 * N L ≤ N L * N L := Nat.mul_le_mul_right _ hN
      _ = N L ^ 2 := by ring
      _ ≤ N L ^ 4 := pow_le_pow_right₀ (by omega) (by omega)
  omega

theorem graph_owner_budget (L Δ : ℕ) (γ : ℚ)
    (hΔ : 0 < Δ) (hγ : 0 < γ)
    (hL : 6 * reciprocalCut Δ γ + 2004 ≤ L) :
    8 * (s L : ℚ) * q₁ L ≤ (γ / 24) * q₂ L / 16 := by
  have hs := s_le_cN L Δ γ hΔ hγ hL
  have hc := c_le_mu_zeta Δ γ
  have hcp := c_pos Δ γ hΔ hγ
  have hq : (q₁ L : ℚ) ≤ N L := by
    exact_mod_cast (Nat.sub_le (s L) 2 |>.trans (s_le_N L (by omega)))
  have hN : (0 : ℚ) < N L := by exact_mod_cast N_pos L
  have hN1 : (1 : ℚ) ≤ N L := by exact_mod_cast N_pos L
  have hpow : (N L : ℚ) ^ 2 ≤ q₂ L := by
    have hh : (N L : ℚ) ^ 2 ≤ (N L : ℚ) ^ 4 :=
      pow_le_pow_right₀ hN1 (by omega)
    simpa only [q₂, Nat.cast_pow] using hh
  have h8c : 8 * c Δ γ ≤ (γ / 24) / 16 := by linarith
  have ha := mul_le_mul_of_nonneg_right hs
    (by positivity : (0 : ℚ) ≤ q₁ L)
  have hb := mul_le_mul_of_nonneg_left hq
    (by positivity : (0 : ℚ) ≤ c Δ γ * N L)
  have hmid : 8 * (s L : ℚ) * q₁ L ≤
      8 * c Δ γ * (N L : ℚ) ^ 2 := by nlinarith [ha, hb]
  calc
    8 * (s L : ℚ) * q₁ L ≤ 8 * c Δ γ * (N L : ℚ) ^ 2 := hmid
    _ ≤ ((γ / 24) / 16) * (N L : ℚ) ^ 2 := by
      exact mul_le_mul_of_nonneg_right h8c (sq_nonneg _)
    _ ≤ (γ / 24) * q₂ L / 16 := by
      have hz : 0 ≤ (γ / 24) / 16 := by positivity
      nlinarith [mul_le_mul_of_nonneg_left hpow hz]

theorem fixed_numeric_guards (Δ : ℕ) (γ : ℚ) :
    5 * (1 / 256 : ℚ) / (4 * (127 / 128 : ℚ)) < 1 / 32 ∧
    ((99 / 100 + (255 / 256 : ℚ) ^ 2 - 1) /
      (255 / 256 : ℚ) ^ 2) - 1 / 1000 > 49 / 64 ∧
    1 - c Δ γ / (2 * (255 / 256 : ℚ)) > 1 / 1000 := by
  have hc := c_le_one Δ γ
  constructor
  · norm_num
  constructor
  · norm_num
  · norm_num at *
    linarith

theorem ownerException_mass (L Δ : ℕ) (γ : ℚ)
    (hΔ : 0 < Δ) (hγ : 0 < γ)
    (hL : 6 * reciprocalCut Δ γ + 2004 ≤ L) :
    (Kstar L : ℚ) * ownerException L Δ γ ≤ η L Δ γ * w L / 16 := by
  have hE := ownerException_le_three_N L Δ γ hΔ hγ hL
  have hLs := L_plus_one_le_s L (by omega)
  have hpow := cubic_s_dyadic_cutoff L (reciprocalCut Δ γ) hL
  have hc := c_lower_dyadic Δ γ hΔ hγ
  have hp : (0 : ℚ) < (2 : ℚ) ^ reciprocalCut Δ γ := by positivity
  have hs : (0 : ℚ) < s L := by exact_mod_cast s_pos L
  have hn : (0 : ℚ) < N L := by exact_mod_cast N_pos L
  have h384 : (384 : ℚ) * (s L : ℚ) ^ 3 ≤ c Δ γ * N L := by
    have hpowQ : (384 : ℚ) * (2 : ℚ) ^ reciprocalCut Δ γ * (s L : ℚ) ^ 3 ≤
        N L := by exact_mod_cast hpow
    have hcmul : (1 : ℚ) ≤ c Δ γ * (2 : ℚ) ^ reciprocalCut Δ γ :=
      (div_le_iff₀ hp).1 hc
    nlinarith [mul_nonneg (sub_nonneg.mpr hcmul)
      (by positivity : (0 : ℚ) ≤ (384 : ℚ) * (s L : ℚ) ^ 3)]
  have hLQ : (L + 1 : ℚ) ≤ s L := by exact_mod_cast hLs
  have hEQ : (ownerException L Δ γ : ℚ) ≤ 3 * N L := by exact_mod_cast hE
  have hK : (Kstar L : ℚ) * ownerException L Δ γ ≤
      24 * (s L : ℚ) ^ 2 * N L := by
    simp only [Kstar]
    push_cast
    have hmul : ((L + 1 : ℕ) : ℚ) * ownerException L Δ γ ≤
        (s L : ℚ) * (3 * N L) := by
      calc
        ((L + 1 : ℕ) : ℚ) * ownerException L Δ γ ≤
            (s L : ℚ) * ownerException L Δ γ :=
          mul_le_mul_of_nonneg_right
            (by simpa only [Nat.cast_add, Nat.cast_one] using hLQ) (by positivity)
        _ ≤ (s L : ℚ) * (3 * N L) :=
          mul_le_mul_of_nonneg_left hEQ hs.le
    have hmul8 := mul_le_mul_of_nonneg_left hmul
      (by positivity : (0 : ℚ) ≤ 8 * (s L : ℚ))
    convert hmul8 using 1 <;> push_cast <;> ring
  calc
    (Kstar L : ℚ) * ownerException L Δ γ ≤
        24 * (s L : ℚ) ^ 2 * N L := hK
    _ ≤ η L Δ γ * w L / 16 := by
      unfold η w
      push_cast
      apply (le_div_iff₀ (by norm_num : (0 : ℚ) < (16 : ℚ))).2
      rw [div_mul_eq_mul_div]
      apply (le_div_iff₀ hs).2
      have hmul := mul_le_mul_of_nonneg_right h384 hn.le
      nlinarith [hmul]

/-- Every numerical test in Appendix I, with the actual conditioning-count
function and the graph edge count. Integer-multiplied variants strengthen the
fractional tests in the source. -/
structure Admissible (L Δ n m C : ℕ) (γ : ℚ) : Prop where
  exception_x : 128 * CurrentAdditive.conditioningExceptionCount (x L : ℝ) 1 ≤ s L
  exception_theta : 128 * CurrentAdditive.conditioningExceptionCount (θ L : ℝ) 1 ≤ w L
  exception_theta_quarter :
    CurrentAdditive.conditioningExceptionCount ((θ L / 4 : ℚ) : ℝ) 1 ≤ s L * q₂ L
  exception_rho : 128 * (CurrentAdditive.conditioningExceptionCount (ρ L : ℝ)
    ((δU L Δ γ / 2 : ℚ) : ℝ) + 1) ≤ Q L
  moment : (C : ℚ) / (s L : ℚ) ^ 128 ≤ θ L / 4
  owner_reserve : 4 * ownerException L Δ γ ≤ w L
  owner_mass : (Kstar L : ℚ) * ownerException L Δ γ ≤ η L Δ γ * w L / 16
  graph_width : Paper2.SourcePadding.powTwoCeil (12 * s L * m) ≤ q₂ L
  row_width : 2 * (n + s L - 3) ≤ q₂ L
  rung_size : 16 ≤ s L / 4
  square_rho : 4 * (s L : ℚ) ^ 2 * ρ L ≤ 1
  s_rho : (s L : ℚ) * ρ L ≤ 1 / 1000
  q₂_x : (q₂ L : ℚ) * x L ≤ 1 / 10000
  s_x : (s L : ℚ) * x L ≤ 1 / 10000
  w_x : (w L : ℚ) * x L ≤ 1 / 10000
  graph_owner : 8 * (s L : ℚ) * q₁ L ≤ (γ / 24) * q₂ L / 16
  double_q₂_x : 2 * (q₂ L : ℚ) * x L ≤ 1 / 8
  double_s_x : 2 * (s L : ℚ) * x L ≤ 1 / 1000
  owner_gap : 2 * (w L : ℚ) * x L + η L Δ γ / (16 * (127 / 128 : ℚ)) < 1
  square_x : 2 * (w L : ℚ) ^ 2 * x L ≤
    η L Δ γ / (16 * (127 / 128 : ℚ))
  inverse_x : x L ≤ 1 / ((w L : ℚ) ^ 2 * q₂ L)
  loss1 : 4 * (1 / 256 : ℚ) * w L * q₂ L * x L ≤ η L Δ γ / 32
  loss2 : 4 * (1 / 256 : ℚ) * w L / q₂ L ≤ η L Δ γ / 32
  ratio_A : (3 / 5 : ℝ) * (1 - 2 / (s L : ℝ)) -
    (q₁ L : ℝ) * (ρ L : ℝ) > 9 / 16
  ratio_T : (3 / 5 : ℝ) - (q₂ L : ℝ) * (x L : ℝ) > 9 / 16
  ratio_N : ∀ j : Fin 3, (2 : ℝ) ^ j.val *
    (((3 / 5 : ℝ) * (1 / 2 : ℝ) ^ j.val - (1 - (255 / 256 : ℝ))) /
      (255 / 256 : ℝ)) - (s L : ℝ) * (x L : ℝ) > 9 / 16

def cutoffLog (Δ C : ℕ) (γ : ℚ) : ℕ :=
  max (6 * reciprocalCut Δ γ + 2004) (max (24 * Δ + 2004) (C + 2004))

theorem admissible_from_cutoff (L Δ n m C : ℕ) (γ : ℚ)
    (hΔ : 0 < Δ) (hγ : 0 < γ) (hm : 0 < m)
    (hdegree : 2 * m ≤ Δ * n)
    (hL : cutoffLog Δ C γ ≤ L) (hn : n ≤ N L) :
    Admissible L Δ n m C γ := by
  have hbase : 2004 ≤ L := by unfold cutoffLog at hL; omega
  have hd : 6 * reciprocalCut Δ γ + 2004 ≤ L := by
    unfold cutoffLog at hL
    omega
  have hΔL : 24 * Δ + 2004 ≤ L := by
    unfold cutoffLog at hL
    omega
  have hC : C + 2004 ≤ L := by
    unfold cutoffLog at hL
    omega
  have hx := scalar_x_all_small L (by omega)
  have hη := scalar_eta_guards L Δ γ hΔ hγ hd
  refine ⟨conditioning_exception_x_small L hbase,
    conditioning_exception_theta_small L hbase,
    conditioning_exception_theta_quarter_small L hbase,
    conditioning_exception_rho_delta_Q L Δ γ hΔ hγ hd,
    moment_guard_rational L C hC,
    ownerException_quarter L Δ γ hΔ hγ hd,
    ownerException_mass L Δ γ hΔ hγ hd,
    q₂_large_for_graph L Δ n m hΔL hn hm hdegree,
    q₂_large_for_rows L n (by omega) hn,
    ?_, four_s_sq_rho L (by omega), s_rho_small L hbase,
    hx.1, hx.2.1, hx.2.2,
    graph_owner_budget L Δ γ hΔ hγ hd,
    two_q₂_x_small L (by omega), ?_, hη.1, hη.2.1,
    x_le_inverse_wsq_q₂ L, hη.2.2.1, hη.2.2.2,
    profile_A_ratio_real L hbase, profile_T_ratio_real L (by omega),
    profile_Nref_ratio_real L hbase⟩
  · have hs := s_ge_64 L (by omega)
    omega
  · have hs := hx.2.1
    linarith

/-- This logarithm is an explicit deterministic choice. Every larger
exponent passes all guards. Therefore the first passing dyadic exponent is
no larger than this one; no search predicate is used as a premise. -/
def chosenLog (n Δ C : ℕ) (γ : ℚ) : ℕ :=
  max (cutoffLog Δ C γ) (Nat.clog 2 n)

theorem chosenLog_ge_cutoff (n Δ C : ℕ) (γ : ℚ) :
    cutoffLog Δ C γ ≤ chosenLog n Δ C γ := by
  unfold chosenLog
  exact le_max_left _ _

theorem chosen_dyadic_size (n Δ C : ℕ) (γ : ℚ) :
    n ≤ N (chosenLog n Δ C γ) ∧
    N (chosenLog n Δ C γ) ≤ 2 * max n (N (cutoffLog Δ C γ)) := by
  let k := cutoffLog Δ C γ
  let t := Nat.clog 2 n
  have hnceil : n ≤ N t := by
    simpa only [N, t, Paper2.SourcePadding.powTwoCeil] using
      Paper2.SourcePadding.le_powTwoCeil n
  rcases le_total k t with hkt | htk
  · have hchoose : chosenLog n Δ C γ = t := by
      simp [chosenLog, k, t, max_eq_right hkt]
    rw [hchoose]
    have hkpos : 0 < k := by
      dsimp [k, cutoffLog]
      omega
    have hnp : 0 < n := by
      by_contra h
      have hzero : n = 0 := by omega
      subst n
      simp [t] at hkt
      omega
    have htwo : N t < 2 * n := by
      simpa only [N, t, Paper2.SourcePadding.powTwoCeil] using
        Paper2.SourcePadding.powTwoCeil_lt_two_mul hnp
    exact ⟨hnceil, (Nat.le_of_lt htwo).trans (Nat.mul_le_mul_left 2 (le_max_left _ _))⟩
  · have hchoose : chosenLog n Δ C γ = k := by
      simp [chosenLog, k, t, max_eq_left htk]
    rw [hchoose]
    have hpow : N t ≤ N k := by
      unfold N
      exact Nat.pow_le_pow_right (by decide) htk
    have hmax : N k ≤ max n (N k) := le_max_right _ _
    exact ⟨hnceil.trans hpow,
      hmax.trans (by omega : max n (N k) ≤ 2 * max n (N k))⟩

theorem chosen_dyadic_admissible (n Δ m C : ℕ) (γ : ℚ)
    (hΔ : 0 < Δ) (hγ : 0 < γ) (hm : 0 < m)
    (hdegree : 2 * m ≤ Δ * n) :
    Admissible (chosenLog n Δ C γ) Δ n m C γ ∧
    N (chosenLog n Δ C γ) ≤
      2 * max n (N (cutoffLog Δ C γ)) := by
  have hsize := chosen_dyadic_size n Δ C γ
  exact ⟨admissible_from_cutoff _ _ _ _ _ _ hΔ hγ hm hdegree
    (chosenLog_ge_cutoff n Δ C γ) hsize.1, hsize.2⟩

noncomputable def firstAcceptedLog (n Δ m C : ℕ) (γ : ℚ)
    (hΔ : 0 < Δ) (hγ : 0 < γ) (hm : 0 < m)
    (hdegree : 2 * m ≤ Δ * n) : ℕ := by
  classical
  exact Nat.find (show ∃ L : ℕ, n ≤ N L ∧ Admissible L Δ n m C γ from
    ⟨chosenLog n Δ C γ, (chosen_dyadic_size n Δ C γ).1,
      (chosen_dyadic_admissible n Δ m C γ hΔ hγ hm hdegree).1⟩)

theorem firstAcceptedLog_valid (n Δ m C : ℕ) (γ : ℚ)
    (hΔ : 0 < Δ) (hγ : 0 < γ) (hm : 0 < m)
    (hdegree : 2 * m ≤ Δ * n) :
    n ≤ N (firstAcceptedLog n Δ m C γ hΔ hγ hm hdegree) ∧
    Admissible (firstAcceptedLog n Δ m C γ hΔ hγ hm hdegree)
      Δ n m C γ := by
  classical
  let H : ∃ L : ℕ, n ≤ N L ∧ Admissible L Δ n m C γ :=
    ⟨chosenLog n Δ C γ, (chosen_dyadic_size n Δ C γ).1,
      (chosen_dyadic_admissible n Δ m C γ hΔ hγ hm hdegree).1⟩
  simpa only [firstAcceptedLog] using (Nat.find_spec H)

theorem firstAccepted_dyadic_bound (n Δ m C : ℕ) (γ : ℚ)
    (hΔ : 0 < Δ) (hγ : 0 < γ) (hm : 0 < m)
    (hdegree : 2 * m ≤ Δ * n) :
    N (firstAcceptedLog n Δ m C γ hΔ hγ hm hdegree) ≤
      2 * max n (N (cutoffLog Δ C γ)) := by
  have hchosen := chosen_dyadic_admissible n Δ m C γ hΔ hγ hm hdegree
  have hsize := chosen_dyadic_size n Δ C γ
  have hlog : firstAcceptedLog n Δ m C γ hΔ hγ hm hdegree ≤
      chosenLog n Δ C γ := by
    classical
    let H : ∃ L : ℕ, n ≤ N L ∧ Admissible L Δ n m C γ :=
      ⟨chosenLog n Δ C γ, hsize.1, hchosen.1⟩
    have hh : Nat.find H ≤ chosenLog n Δ C γ :=
      Nat.find_min' H ⟨hsize.1, hchosen.1⟩
    simpa only [firstAcceptedLog] using hh
  have hpow : N (firstAcceptedLog n Δ m C γ hΔ hγ hm hdegree) ≤
      N (chosenLog n Δ C γ) := by
    unfold N
    exact Nat.pow_le_pow_right (by decide) hlog
  exact hpow.trans hsize.2

#print axioms c_pos
#print axioms c_le_deletion
#print axioms Q_theta
#print axioms overhead_formula
#print axioms coefficient_mul_s_le_N
#print axioms four_s_sq_le_N
#print axioms q₂_mul_x_small
#print axioms x_le_inverse_wsq_q₂
#print axioms profile_Nref_ratio
#print axioms profile_Nref_ratio_real
#print axioms conditioning_epsilon_x_small
#print axioms x_real_dyadic
#print axioms epsilon_x_eq
#print axioms exception_x_inner_eq
#print axioms conditioning_exception_x_small
#print axioms dyadic_exception_upper
#print axioms conditioning_exception_theta_small
#print axioms conditioning_exception_theta_quarter_small
#print axioms conditioning_exception_theta_eta_upper
#print axioms conditioning_exception_rho_delta_Q
#print axioms ownerException_mass
#print axioms s_le_cN
#print axioms moment_guard_rational
#print axioms scalar_eta_guards
#print axioms q₂_large_for_graph
#print axioms graph_owner_budget
#print axioms admissible_from_cutoff
#print axioms chosen_dyadic_admissible
#print axioms firstAccepted_dyadic_bound

end CurrentAdditive.DeterministicParameters
