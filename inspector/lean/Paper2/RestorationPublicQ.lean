import Paper2.RestorationCoverParameters

/-!
# A computable rational-input public `Q`

Frozen v12 Appendix C chooses `Q=pow₂(80L/δ_U)`, where `pow₂` is the
least power of two no smaller than its positive argument. This scratch
module gives that choice for a rational `δ_U`; it does not construct `δ_U`
from source data or prove the full admissibility schedule.
-/

namespace Paper2.RestorationPublicQScratch

def threshold (L : ℕ) (deltaU : ℚ) : ℚ := (80 * L : ℕ) / deltaU

def publicQ (L : ℕ) (deltaU : ℚ) : ℕ :=
  SourcePadding.powTwoCeil (Nat.ceil (threshold L deltaU))

theorem threshold_pos (L : ℕ) (hL : 1 ≤ L) (deltaU : ℚ)
    (hdelta : 0 < deltaU) : 0 < threshold L deltaU := by
  unfold threshold
  positivity

theorem publicQ_pos (L : ℕ) (deltaU : ℚ) : 0 < publicQ L deltaU := by
  unfold publicQ SourcePadding.powTwoCeil
  positivity

theorem publicQ_dyadic (L : ℕ) (deltaU : ℚ) :
    ∃ k : ℕ, publicQ L deltaU = 2 ^ k := by
  exact ⟨Nat.clog 2 (Nat.ceil (threshold L deltaU)), rfl⟩

theorem publicQ_meets (L : ℕ) (deltaU : ℚ) (hdelta : 0 < deltaU) :
    (80 * L : ℕ) ≤ (publicQ L deltaU : ℚ) * deltaU := by
  have hc : threshold L deltaU ≤ (Nat.ceil (threshold L deltaU) : ℚ) :=
    Nat.le_ceil _
  have hp : Nat.ceil (threshold L deltaU) ≤ publicQ L deltaU :=
    SourcePadding.le_powTwoCeil _
  have ht : threshold L deltaU ≤ (publicQ L deltaU : ℚ) :=
    hc.trans (by exact_mod_cast hp)
  exact (div_le_iff₀ hdelta).mp ht

theorem publicQ_le_of_dyadic_meets (L : ℕ) (deltaU : ℚ)
    (hdelta : 0 < deltaU) (k : ℕ)
    (hmeet : (80 * L : ℕ) ≤ ((2 ^ k : ℕ) : ℚ) * deltaU) :
    publicQ L deltaU ≤ 2 ^ k := by
  have ht : threshold L deltaU ≤ ((2 ^ k : ℕ) : ℚ) :=
    (div_le_iff₀ hdelta).2 hmeet
  have hc : Nat.ceil (threshold L deltaU) ≤ 2 ^ k :=
    Nat.ceil_le.mpr ht
  have hk : Nat.clog 2 (Nat.ceil (threshold L deltaU)) ≤ k :=
    (Nat.clog_le_iff_le_pow (by decide)).2 hc
  unfold publicQ SourcePadding.powTwoCeil
  exact pow_le_pow_right₀ (by omega) hk

theorem publicQ_lt_twice_ceiling (L : ℕ) (hL : 1 ≤ L)
    (deltaU : ℚ) (hdelta : 0 < deltaU) :
    (publicQ L deltaU : ℚ) < 2 * (Nat.ceil (threshold L deltaU) : ℚ) := by
  have hn : 0 < Nat.ceil (threshold L deltaU) :=
    Nat.ceil_pos.mpr (threshold_pos L hL deltaU hdelta)
  have hh := SourcePadding.powTwoCeil_lt_two_mul hn
  have hh' : (publicQ L deltaU : ℚ) <
      ((2 * Nat.ceil (threshold L deltaU) : ℕ) : ℚ) := by
    exact_mod_cast hh
  simpa only [Nat.cast_mul, Nat.cast_ofNat] using hh'

theorem publicQ_lt_twice_max (L : ℕ) (hL : 1 ≤ L)
    (deltaU : ℚ) (hdelta : 0 < deltaU) :
    (publicQ L deltaU : ℚ) < 2 * max 1 (threshold L deltaU) := by
  let n := Nat.ceil (threshold L deltaU)
  have hnpos : 0 < n := Nat.ceil_pos.mpr (threshold_pos L hL deltaU hdelta)
  by_cases hsmall : n = 1
  · have hQ : publicQ L deltaU = 1 := by
      change 2 ^ Nat.clog 2 n = 1
      rw [hsmall]
      norm_num
    rw [hQ]
    have hm : (1 : ℚ) ≤ max 1 (threshold L deltaU) := le_max_left _ _
    norm_num only [Nat.cast_one]
    linarith
  · have hnlarge : 1 < n := by omega
    have hcpos : 0 < Nat.clog 2 n := Nat.clog_pos (by decide) hnlarge
    have hp : 2 ^ (Nat.clog 2 n).pred < n :=
      Nat.pow_pred_clog_lt_self (by decide) hnlarge
    have ht : (((2 ^ (Nat.clog 2 n).pred : ℕ) : ℚ)) <
        threshold L deltaU := by
      exact (Nat.lt_ceil).mp (by simpa only [n] using hp)
    have hQ : publicQ L deltaU = 2 * 2 ^ (Nat.clog 2 n).pred := by
      change 2 ^ Nat.clog 2 n = _
      have heq : (Nat.clog 2 n).pred + 1 = Nat.clog 2 n :=
        Nat.succ_pred_eq_of_pos hcpos
      calc
        2 ^ Nat.clog 2 n = 2 ^ ((Nat.clog 2 n).pred + 1) :=
          congrArg (2 ^ ·) heq.symm
        _ = 2 * 2 ^ (Nat.clog 2 n).pred := by rw [pow_succ]; omega
    have hQcast : (publicQ L deltaU : ℚ) =
        2 * (((2 ^ (Nat.clog 2 n).pred : ℕ) : ℚ)) := by
      exact_mod_cast hQ
    rw [hQcast]
    have hm : threshold L deltaU ≤ max 1 (threshold L deltaU) :=
      le_max_right _ _
    linarith

theorem publicQ_theta_exact (L : ℕ) (deltaU : ℚ) :
    (publicQ L deltaU : ℝ) *
      RestorationCoverParameters.theta (publicQ L deltaU) = 1 / 320 := by
  have hQ : (0 : ℝ) < publicQ L deltaU := by
    exact_mod_cast publicQ_pos L deltaU
  unfold RestorationCoverParameters.theta
  field_simp
  simp only [Nat.cast_mul, Nat.cast_ofNat]
  ring

theorem publicQ_theta_lt_twentieth (L : ℕ) (deltaU : ℚ) :
    (publicQ L deltaU : ℝ) *
      RestorationCoverParameters.theta (publicQ L deltaU) < 1 / 20 := by
  rw [publicQ_theta_exact]
  norm_num

theorem rational_threshold_real (L : ℕ) (deltaU : ℚ) :
    ((threshold L deltaU : ℚ) : ℝ) =
      (80 * (L : ℝ)) / (deltaU : ℝ) := by
  simp [threshold, Nat.cast_mul]

theorem publicQ_real_schedule (L : ℕ) (deltaU : ℚ) :
    publicQ L deltaU = SourcePadding.powTwoCeil
      (Nat.ceil ((80 * (L : ℝ)) / (deltaU : ℝ))) := by
  have hc : Nat.ceil (((threshold L deltaU : ℚ) : ℝ)) =
      Nat.ceil (threshold L deltaU) := by
    rw [← Int.ceil_toNat, ← Int.ceil_toNat, Rat.ceil_cast]
  rw [← rational_threshold_real]
  unfold publicQ
  rw [hc]

#eval publicQ 1 (1 : ℚ)
#eval publicQ 1 (1000 : ℚ)

#print axioms publicQ_meets
#print axioms publicQ_le_of_dyadic_meets
#print axioms publicQ_lt_twice_ceiling
#print axioms publicQ_lt_twice_max
#print axioms publicQ_theta_exact
#print axioms publicQ_real_schedule

end Paper2.RestorationPublicQScratch
