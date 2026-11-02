import CurrentAdditive.V39ExceptionBudget

/-! The literal public exception budget for every rational tolerance in (0,1].
This discharges the schedule's owner-exception bound without replacing its
computed tolerance by one. -/

namespace CurrentAdditive.V39GeneralExceptionBudget

open V39ExceptionBudget V38Schedule

theorem exception_le_ebar (b : ℕ) (τ : ℚ) (hτ : 0 < τ) (hτ1 : τ ≤ 1) :
    V38Moments.exceptionCount (dyadic b) (τ : ℝ) ≤ ebar b τ := by
  have ht : (0 : ℝ) < τ := by exact_mod_cast hτ
  have ht1 : (τ : ℝ) ≤ 1 := by exact_mod_cast hτ1
  let e := V38Moments.epsilon (dyadic b) 1
  have he : 0 < e := by
    dsimp [e]
    rw [dyadic_epsilon]
    positivity
  have he1 : e ≤ 1 := min_le_left _ _
  have hea : e ≤ (2 : ℝ)^(-30 : ℤ) * (dyadic b)^((1 : ℝ)/256) :=
    min_le_right _ _
  have hprod : (τ : ℝ)*e ≤ V38Moments.epsilon (dyadic b) (τ : ℝ) := by
    apply le_min
    · nlinarith
    · have hte : (τ : ℝ)*e ≤ e := by nlinarith
      exact hte.trans hea
  have heτ : 0 < V38Moments.epsilon (dyadic b) (τ : ℝ) :=
    (mul_pos ht he).trans_le hprod
  have hdpos := dyadic_pos b
  have hp := Real.rpow_le_rpow_of_nonpos (mul_pos ht he) hprod
    (by norm_num : -(2 : ℝ) ≤ 0)
  rw [Real.mul_rpow ht.le he.le] at hp
  let a := (2 : ℝ)^(20 : ℕ) *
    (V38Moments.epsilon (dyadic b) (τ : ℝ))^(-(2 : ℝ)) *
    (dyadic b)^(-(1 : ℝ)/512)
  have ha0 : 0 ≤ a := by dsimp [a]; positivity
  have ha : a ≤ (τ : ℝ)^(-(2 : ℝ)) * (2 : ℝ)^(80+5*(b : ℝ)/512) := by
    have h := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hp (by positivity : (0 : ℝ) ≤ 2^20))
      (by positivity : (0 : ℝ) ≤ (dyadic b)^(-(1 : ℝ)/512))
    calc
      a ≤ (2 : ℝ)^20*((τ : ℝ)^(-(2 : ℝ))*e^(-(2 : ℝ)))*
          (dyadic b)^(-(1 : ℝ)/512) := h
      _ = (τ : ℝ)^(-(2 : ℝ)) *
          ((2 : ℝ)^20*e^(-(2 : ℝ))*(dyadic b)^(-(1 : ℝ)/512)) := by ring
      _ = _ := by rw [show e=V38Moments.epsilon (dyadic b) 1 from rfl,
        dyadic_exception_inner]
  let j := (b+63)/64
  have hj : 5*(b : ℝ)/512 ≤ (j : ℝ) := by
    have hb : 5*b ≤ 512*j := by dsimp [j]; omega
    have hh : 5*(b : ℝ) ≤ 512*(j : ℝ) := by exact_mod_cast hb
    linarith
  have hpow : (2 : ℝ)^(80+5*(b : ℝ)/512) ≤ (2 : ℝ)^(80+j) := by
    rw [← Real.rpow_natCast]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    push_cast
    linarith
  let Z := (τ : ℝ)^(-(2 : ℝ))*(2 : ℝ)^(80+j)
  have haZ : a ≤ Z := ha.trans
    (mul_le_mul_of_nonneg_left hpow (by positivity))
  have htinv : (1 : ℝ) ≤ (τ : ℝ)^(-(2 : ℝ)) := by
    have h := Real.rpow_le_rpow_of_nonpos ht ht1
      (by norm_num : -(2 : ℝ) ≤ 0)
    simpa using h
  have hZ : 1 ≤ Z := by
    have hp1 : (1 : ℝ) ≤ (2 : ℝ)^(80+j) := one_le_pow₀ (by norm_num)
    dsimp [Z]
    nlinarith
  have hceil : (⌈a⌉₊ : ℝ) ≤ 2*Z := by
    have hh := Nat.ceil_lt_add_one ha0
    linarith
  have hcount : (V38Moments.exceptionCount (dyadic b) (τ : ℝ) : ℝ) ≤ 16*Z := by
    change ((8*⌈a⌉₊ : ℕ) : ℝ) ≤ _
    push_cast
    linarith
  have heb : (2 : ℝ)^90 / (τ : ℝ)^2 * (2 : ℝ)^j ≤ (ebar b τ : ℝ) := by
    have hh : (2^90 : ℚ)/τ^2*(2^j : ℚ) ≤ (ebar b τ : ℚ) := Nat.le_ceil _
    exact_mod_cast hh
  have hzeb : 16*Z ≤ (2 : ℝ)^90 / (τ : ℝ)^2 * (2 : ℝ)^j := by
    dsimp [Z]
    rw [Real.rpow_neg ht.le, Real.rpow_two, pow_add]
    norm_num [div_eq_mul_inv]
    nlinarith [mul_nonneg (inv_nonneg.mpr (sq_nonneg (τ : ℝ)))
      (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) j)]
  have hh := hcount.trans (hzeb.trans heb)
  exact_mod_cast hh

#print axioms exception_le_ebar

end CurrentAdditive.V39GeneralExceptionBudget
