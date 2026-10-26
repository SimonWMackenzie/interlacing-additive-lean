import EthInapproximability.CurrentPaper.EncodedETHTail

/-!
# Fixed polynomial table costs are subexponential

Source: frozen v8 `06-eth.tex`, the uniform table size and final runtime
absorption. These numerical bounds use the actual compiled cutoff clock,
not a supplied unbounded repetition oracle. They are separate from the
remaining operational theorem implementing the whole SAT solver.
-/

namespace EthInapproximability.CurrentPaper.ETHTailGrowth

open Filter

noncomputable def repetitions (c A d : ℕ) : ℕ → ℕ :=
  SlowClock.repetitions (CutoffBitMachine.actualClock c A d)

theorem table_exponent_eventually_small (c A d B : ℕ) (η : ℝ) (hη : 0 < η) :
    ∀ᶠ n : ℕ in atTop,
      (B : ℝ) * (2 * (FinalPadding.exponent (repetitions c A d) n : ℝ)) ≤ η * n := by
  have ht := (CutoffBitMachine.actualClock_exponent_ratio_tendsto_zero c A d).const_mul
    (2 * (B : ℝ))
  simp only [mul_zero] at ht
  have he := ht.eventually (gt_mem_nhds hη)
  filter_upwards [he, eventually_ge_atTop (1 : ℕ)] with n hn hpos
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hquot : ((B : ℝ) * (2 * (FinalPadding.exponent (repetitions c A d) n : ℝ))) /
      (n : ℝ) < η := by
    simpa only [repetitions, mul_div_assoc, mul_comm (2 : ℝ) (B : ℝ), mul_assoc] using hn
  exact ((div_lt_iff₀ hnpos).mp hquot).le

theorem polynomial_table_eventually_subexponential (c A d B : ℕ)
    (η : ℝ) (hη : 0 < η) :
    ∀ᶠ n : ℕ in atTop,
      ((FinalPadding.tableSize (repetitions c A d) n : ℕ) : ℝ) ^ B ≤
        (2 : ℝ) ^ (η * n) := by
  filter_upwards [table_exponent_eventually_small c A d B η hη] with n hn
  have hpow := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hn
  convert hpow using 1
  simp only [FinalPadding.tableSize, Nat.cast_pow, Nat.cast_ofNat]
  rw [← pow_mul, ← Real.rpow_natCast]
  congr 1
  push_cast
  ring

/-- This is the quantitative spare-exponent argument in the final proof.
Any fixed polynomial in the common table length fits into the difference
between the source-list exponent and the forbidden ETH exponent. -/
theorem source_times_table_eventually (c A d B : ℕ) (ε δ : ℝ) (hεδ : ε < δ) :
    ∀ᶠ n : ℕ in atTop,
      (2 : ℝ) ^ (ε * n) *
        ((FinalPadding.tableSize (repetitions c A d) n : ℕ) : ℝ) ^ B ≤
          (2 : ℝ) ^ (δ * n) := by
  filter_upwards [polynomial_table_eventually_subexponential c A d B (δ - ε) (by linarith)]
    with n hn
  calc
    _ ≤ (2 : ℝ) ^ (ε * n) * (2 : ℝ) ^ ((δ - ε) * n) :=
      mul_le_mul_of_nonneg_left hn (Real.rpow_nonneg (by norm_num) _)
    _ = (2 : ℝ) ^ (δ * n) := by
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      congr 1
      ring

end EthInapproximability.CurrentPaper.ETHTailGrowth
