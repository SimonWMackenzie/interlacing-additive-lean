import Paper2.SourcePadding

/-!
Numerical cover parameters for frozen Paper 2 v12, restoration and Appendix C.
The strict power gaps below follow from the displayed public constants.
-/

namespace Paper2.RestorationCoverParameters

noncomputable def theta (Q : ℕ) : ℝ := 1 / (320 * Q : ℕ)
def b (Q : ℕ) : ℕ := Nat.clog 2 (320 * Q)
def B0 (Q : ℕ) : ℕ := 4 * (b Q + 1)
def B2 (Q : ℕ) : ℕ := 100 * (b Q + 1)
noncomputable def B1 (Q : ℕ) (eta : ℝ) : ℕ := Nat.ceil (((b Q + 1 : ℕ) : ℝ) / eta)
def tStar (Q : ℕ) : ℕ := SourcePadding.powTwoCeil (1024 * (b Q + 1))
def tExponent (Q : ℕ) : ℕ := Nat.clog 2 (1024 * (b Q + 1))

theorem theta_pos {Q : ℕ} (hQ : 0 < Q) : 0 < theta Q := by
  unfold theta
  positivity

theorem theta_le_one {Q : ℕ} (hQ : 0 < Q) : theta Q ≤ 1 := by
  unfold theta
  have h : (1 : ℝ) ≤ (320 * Q : ℕ) := by exact_mod_cast (by omega : 1 ≤ 320 * Q)
  exact (div_le_iff₀ (by positivity)).2 (by nlinarith)

theorem b_power {Q : ℕ} (hQ : 0 < Q) :
    (320 * Q : ℕ) ≤ 2 ^ b Q := by
  exact Nat.le_pow_clog (by decide) _

theorem two_neg_b_le_theta {Q : ℕ} (hQ : 0 < Q) :
    (1 / 2 : ℝ) ^ b Q ≤ theta Q := by
  have hN : (0 : ℝ) < (320 * Q : ℕ) := by exact_mod_cast (by omega : 0 < 320 * Q)
  have hp : (320 * Q : ℕ) ≤ 2 ^ b Q := b_power hQ
  calc
    (1 / 2 : ℝ) ^ b Q = ((2 : ℝ) ^ b Q)⁻¹ := by rw [one_div, inv_pow]
    _ ≤ ((320 * Q : ℕ) : ℝ)⁻¹ :=
      (inv_le_inv₀ (by positivity : 0 < (2 : ℝ) ^ b Q) hN).2
        (by exact_mod_cast hp)
    _ = theta Q := by simp [theta, one_div]

theorem half_power_lt_theta {Q : ℕ} (hQ : 0 < Q) :
    (1 / 2 : ℝ) ^ (b Q + 1) < theta Q := by
  have hN : (0 : ℝ) < (320 * Q : ℕ) := by exact_mod_cast (by omega : 0 < 320 * Q)
  have hp : (320 * Q : ℕ) ≤ 2 ^ b Q := b_power hQ
  have hp' : (320 * Q : ℝ) < (2 : ℝ) ^ (b Q + 1) := by
    have hcast : (320 * Q : ℝ) ≤ (2 : ℝ) ^ b Q := by exact_mod_cast hp
    rw [pow_succ]
    nlinarith [show (0 : ℝ) < (2 : ℝ) ^ b Q by positivity]
  calc
    (1 / 2 : ℝ) ^ (b Q + 1) = ((2 : ℝ) ^ (b Q + 1))⁻¹ := by rw [one_div, inv_pow]
    _ < ((320 * Q : ℕ) : ℝ)⁻¹ :=
      (inv_lt_inv₀ (by positivity : 0 < (2 : ℝ) ^ (b Q + 1)) hN).2
        (by simpa only [Nat.cast_mul, Nat.cast_ofNat] using hp')
    _ = theta Q := by simp [theta, one_div]

private theorem power_gap {Q k : ℕ} (hQ : 0 < Q) {rho : ℝ}
    (hrho : 0 ≤ rho) (hbase : rho ^ k < 1 / 2) :
    rho ^ (k * (b Q + 1)) < theta Q := by
  rw [pow_mul]
  exact (pow_lt_pow_left₀ hbase (pow_nonneg hrho _) (by omega)).trans
    (half_power_lt_theta hQ)

theorem B0_gap {Q : ℕ} (hQ : 0 < Q) :
    (18 / 25 : ℝ) ^ B0 Q < theta Q := by
  have hbase : (18 / 25 : ℝ) ^ 4 < 1 / 2 := by norm_num
  exact power_gap hQ (by norm_num : (0 : ℝ) ≤ 18 / 25) hbase

theorem B2_gap {Q : ℕ} (hQ : 0 < Q) :
    (99 / 100 : ℝ) ^ B2 Q < theta Q := by
  have hbase : (99 / 100 : ℝ) ^ 100 < 1 / 2 := by norm_num
  exact power_gap hQ (by norm_num : (0 : ℝ) ≤ 99 / 100) hbase

theorem B1_eta_count (Q : ℕ) {eta : ℝ} (heta : 0 < eta) :
    ((b Q + 1 : ℕ) : ℝ) ≤ eta * (B1 Q eta : ℝ) := by
  have hceil : ((b Q + 1 : ℕ) : ℝ) / eta ≤ (B1 Q eta : ℝ) := by
    exact Nat.le_ceil _
  exact (div_le_iff₀ heta).mp hceil |>.trans_eq (by ring)

theorem B1_gap {Q : ℕ} (hQ : 0 < Q) {eta : ℝ}
    (heta : 0 < eta) (heta1 : eta < 1) :
    (1 - eta) ^ B1 Q eta < theta Q := by
  have hnonneg : 0 ≤ 1 - eta := by linarith
  have hpow : (1 - eta) ^ B1 Q eta ≤ (Real.exp (-eta)) ^ B1 Q eta :=
    pow_le_pow_left₀ hnonneg (Real.one_sub_le_exp_neg eta) _
  have hcount := B1_eta_count Q heta
  simp only [Nat.cast_add, Nat.cast_one] at hcount
  have hexp : (Real.exp (-eta)) ^ B1 Q eta ≤
      (Real.exp (-1)) ^ (b Q + 1) := by
    rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    push_cast
    nlinarith [hcount]
  have hhalf : (Real.exp (-1)) ^ (b Q + 1) <
      (1 / 2 : ℝ) ^ (b Q + 1) :=
    pow_lt_pow_left₀ Real.exp_neg_one_lt_half
      (Real.exp_pos _).le (by omega)
  exact lt_of_le_of_lt (hpow.trans hexp) (hhalf.trans (half_power_lt_theta hQ))

theorem B0_pos (Q : ℕ) : 1 ≤ B0 Q := by unfold B0; omega
theorem B2_pos (Q : ℕ) : 1 ≤ B2 Q := by unfold B2; omega
theorem B1_pos (Q : ℕ) {eta : ℝ} (heta : 0 < eta) : 1 ≤ B1 Q eta := by
  rw [B1, Nat.one_le_ceil_iff]
  positivity

theorem tStar_pow (Q : ℕ) : tStar Q = 2 ^ tExponent Q := rfl
theorem tStar_ge (Q : ℕ) : 1024 ≤ tStar Q := by
  calc
    1024 ≤ 1024 * (b Q + 1) := by omega
    _ ≤ tStar Q := SourcePadding.le_powTwoCeil _

theorem tExponent_ge_two (Q : ℕ) : 2 ≤ tExponent Q := by
  by_contra h
  have hlt : tExponent Q ≤ 1 := by omega
  have hp : tStar Q ≤ 2 ^ 1 := by
    rw [tStar_pow]
    exact pow_le_pow_right₀ (by norm_num : (1 : ℕ) ≤ 2) hlt
  have hge := tStar_ge Q
  omega

end Paper2.RestorationCoverParameters

#print axioms Paper2.RestorationCoverParameters.B0_gap
#print axioms Paper2.RestorationCoverParameters.B1_gap
#print axioms Paper2.RestorationCoverParameters.B2_gap
#print axioms Paper2.RestorationCoverParameters.tExponent_ge_two
