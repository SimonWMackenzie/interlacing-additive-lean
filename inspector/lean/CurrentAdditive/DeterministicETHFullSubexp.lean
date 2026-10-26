import CurrentAdditive.DeterministicEndpointSubexp
import Paper2.SubexpLen

/-! Promote the finite reciprocal-power estimate of `det:eth` to the
explicit every-positive-rate subexponential runtime form used by sparse ETH.
No machine is inferred from this arithmetic theorem. -/

namespace CurrentAdditive.DeterministicETHFullSubexp

open CurrentAdditive.DeterministicEndpointNumeric

def tableBound (a C₀ b m : ℕ) : ℕ :=
  m ^ (b*C₀*(2^a)^ethIterations a m)

theorem tableBound_subexp (a C₀ b : ℕ)
    (ha : 1 ≤ a) (hC₀ : 1 ≤ C₀) (hb : 1 ≤ b) :
    Paper2.AEth.Subexp (tableBound a C₀ b) := by
  intro ε hε
  obtain ⟨n, hn⟩ := exists_nat_gt (1/ε)
  have hnpos : 1 ≤ n := by
    have hdiv : (0:ℝ) < 1/ε := by positivity
    exact_mod_cast (by exact_mod_cast (lt_trans hdiv hn) : (0:ℝ) < n)
  have hrate : 1 ≤ ε * (n:ℝ) := by
    have hh : 1 < (n:ℝ) * ε := (div_lt_iff₀ hε).mp hn
    nlinarith
  refine ⟨1, 0, 2^(max (32*(n*b*C₀)+16) (8*a)), ?_⟩
  intro m hm
  have hpow := eth_discrete_subexponential_bound a C₀ b n m
    ha hC₀ hb hnpos hm
  have hpowR : ((tableBound a C₀ b m:ℝ)^n) ≤ ((2:ℝ)^m) := by
    exact_mod_cast hpow
  have hmR : (0:ℝ) ≤ m := by positivity
  have hexp : (m:ℝ) ≤ (ε*(m:ℝ))*(n:ℝ) := by
    nlinarith
  have htwo : (2:ℝ)^m ≤ (2:ℝ)^((ε*(m:ℝ))*(n:ℝ)) := by
    simpa only [Real.rpow_natCast] using
      (Real.rpow_le_rpow_of_exponent_le (x := (2:ℝ))
        (by norm_num) hexp)
  have hrpow : ((2:ℝ)^(ε*(m:ℝ)))^n =
      (2:ℝ)^((ε*(m:ℝ))*(n:ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
  have htarget : ((tableBound a C₀ b m:ℝ)^n) ≤
      ((2:ℝ)^(ε*(m:ℝ)))^n := by
    rw [hrpow]
    exact hpowR.trans htwo
  have hle : (tableBound a C₀ b m:ℝ) ≤ (2:ℝ)^(ε*(m:ℝ)) :=
    le_of_pow_le_pow_left₀ (by omega : n ≠ 0) (by positivity) htarget
  have hceil := Nat.le_ceil ((2:ℝ)^(ε*(m:ℝ)))
  have hnat : tableBound a C₀ b m ≤ ⌈(2:ℝ)^(ε*(m:ℝ))⌉₊ := by
    exact_mod_cast hle.trans hceil
  simpa using hnat

#print axioms tableBound_subexp

/-- Any fixed polynomial overhead on the generated table remains within
the same explicit sparse-ETH time class. -/
theorem tableBound_power_subexp (a C₀ b p : ℕ)
    (ha : 1 ≤ a) (hC₀ : 1 ≤ C₀) (hb : 1 ≤ b) (hp : 1 ≤ p) :
    Paper2.AEth.Subexp (fun m => (tableBound a C₀ b m)^p) := by
  have hCp : 1 ≤ C₀*p := by nlinarith
  have heq : (fun m => (tableBound a C₀ b m)^p) =
      tableBound a (C₀*p) b := by
    funext m
    dsimp [tableBound]
    rw [← pow_mul]
    congr 1
    ring
  rw [heq]
  exact tableBound_subexp a (C₀*p) b ha hCp hb

#print axioms tableBound_power_subexp

end CurrentAdditive.DeterministicETHFullSubexp
