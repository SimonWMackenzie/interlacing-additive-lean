import CurrentAdditive.IndexedProfileRung

/-! The finite spare capacity behind the manuscript's `count/u > 9/16`
calculation. The `+1` in rareboost and the exceptional positions are both
charged explicitly. -/

namespace CurrentAdditive.DeterministicIndexedMatrix

theorem dyadic_budget_of_ratio
    (k e : ℕ) (hk : 5 ≤ k) (he : 32 * e ≤ 2^k)
    (t total : ℝ) (ht : 0 ≤ t)
    (hratio : (9/16 : ℝ) * (2^k : ℝ) ≤ total) :
    (((2^(k-1)+1+e : ℕ) : ℝ) * (1-t)) ≤ total := by
  let m := 2^(k-5)
  have hm : 1 ≤ m := by
    have hp : 0 < m := by dsimp [m]; positivity
    omega
  have hpow : 2^k = 32*m := by
    dsimp [m]
    conv_lhs => rw [show k = (k-5)+5 by omega, pow_add]
    norm_num [mul_comm]
  have hprev : 2^(k-1) = 16*m := by
    dsimp [m]
    conv_lhs => rw [show k-1 = (k-5)+4 by omega, pow_add]
    norm_num [mul_comm]
  have hnat : 16 * (2^(k-1)+1+e) ≤ 9 * 2^k := by
    rw [hpow, hprev]
    omega
  have hreal : (16 : ℝ) * ((2^(k-1)+1+e : ℕ) : ℝ) ≤
      9 * (2^k : ℝ) := by
    exact_mod_cast hnat
  have hn : (0 : ℝ) ≤ ((2^(k-1)+1+e : ℕ) : ℝ) := by positivity
  nlinarith [mul_nonneg hn ht]

end CurrentAdditive.DeterministicIndexedMatrix
