import CurrentAdditive.V42NumericPowerMargins

namespace CurrentAdditive.V42NumericMargins
set_option maxHeartbeats 3000000
set_option maxRecDepth 32768

/-- The source's E_exc uses the actual count at tolerance eta/2. -/
noncomputable def Eexc (s : ℝ) : ℝ :=
  2*(V38Moments.exceptionCount (1/(512*s^24)) ((1/s^2)/2):ℝ)

private theorem reciprocal_scaled_rpow (s : ℝ) (hs : 0<s)
    (A N : ℕ) (p : ℝ) :
    (1/((2:ℝ)^A*s^N))^(-p)=(2:ℝ)^((A:ℝ)*p)*s^((N:ℝ)*p) := by
  rw [one_div,←Real.rpow_neg_eq_inv_rpow,neg_neg,
    Real.mul_rpow (by positivity) (by positivity),
    ←Real.rpow_natCast_mul (by norm_num : (0:ℝ) ≤ 2),←Real.rpow_natCast_mul hs.le]

private theorem theta_bounds (s : ℝ) (hs : 1 ≤ s) :
    0<1/(512*s^24) ∧ 1/(512*s^24) ≤ 1 ∧
    0<(1/s^2)/2 ∧ (1/s^2)/2 ≤ 1 := by
  have hsp : 0<s := lt_of_lt_of_le (by norm_num) hs
  have h24 : 1 ≤ s^24 := one_le_pow₀ hs
  have h2 : 1 ≤ s^2 := one_le_pow₀ hs
  refine ⟨by positivity,?_,by positivity,?_⟩
  · apply (div_le_one (by positivity)).2
    nlinarith
  · have hi : 1/s^2 ≤ 1 := (div_le_one (by positivity)).2 h2
    linarith

/-- The exact displayed e(theta/4) estimate, derived from the reviewed
2^84 bound with real exponent 3/8. -/
theorem quarter_exception_bound (s : ℝ) (hs : 1 ≤ s) :
    (V38Moments.exceptionCount ((1/(512*s^24))/4) 1:ℝ)  ≤
      (2:ℝ)^85*s^((3:ℝ)/8) := by
  have hsp : 0<s := lt_of_lt_of_le (by norm_num) hs
  obtain ⟨hθ,hθ1,_,_⟩ := theta_bounds s hs
  have he := V42ExceptionBudget.exceptionCount_real_bound ((1/(512*s^24))/4) 1
    (by positivity) (by linarith) (by norm_num) (by norm_num)
  have hθq : (1/(512*s^24))/4=1/((2:ℝ)^11*s^24) := by norm_num; ring
  have hp : ((1/(512*s^24))/4)^(-(1:ℝ)/64)=
      (2:ℝ)^((11:ℝ)/64)*s^((3:ℝ)/8) := by
    rw [hθq]
    convert reciprocal_scaled_rpow s hsp 11 24 ((1:ℝ)/64) using 1 <;> norm_num
  have hc : (2:ℝ)^((11:ℝ)/64) ≤ 2 := by
    calc
      _  ≤  (2:ℝ)^(1:ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      _ = _ := by norm_num
  calc
    _  ≤  (2:ℝ)^84*((2:ℝ)^((11:ℝ)/64)*s^((3:ℝ)/8)) := by simpa only [Real.one_rpow,mul_one,hp] using he
    _  ≤  (2:ℝ)^84*(2*s^((3:ℝ)/8)) := by gcongr
    _ = _ := by norm_num; ring

/-- The exact displayed E_exc estimate; no ebar/EexcBudget replaces the count. -/
theorem owner_exception_bound (s : ℝ) (hs : 1 ≤ s) :
    Eexc s  ≤  (2:ℝ)^88*s^((35:ℝ)/8) := by
  have hsp : 0<s := lt_of_lt_of_le (by norm_num) hs
  obtain ⟨hθ,hθ1,hτ,hτ1⟩ := theta_bounds s hs
  have he := V42ExceptionBudget.exceptionCount_real_bound (1/(512*s^24)) ((1/s^2)/2)
    hθ hθ1 hτ hτ1
  have hθ : (1/(512*s^24))^(-(1:ℝ)/64)=
      (2:ℝ)^((9:ℝ)/64)*s^((3:ℝ)/8) := by
    have h512 : (512:ℝ)=(2:ℝ)^9 := by norm_num
    rw [h512]
    convert reciprocal_scaled_rpow s hsp 9 24 ((1:ℝ)/64) using 1 <;> norm_num
  have hτpow : ((1/s^2)/2)^(-(2:ℝ))=4*s^4 := by
    have heq : (1/s^2)/2=1/((2:ℝ)^1*s^2) := by norm_num; ring
    rw [heq]
    convert reciprocal_scaled_rpow s hsp 1 2 (2:ℝ) using 1; norm_num
  have hc : (2:ℝ)^((9:ℝ)/64) ≤ 2 := by
    calc
      _  ≤  (2:ℝ)^(1:ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      _ = _ := by norm_num
  calc
    Eexc s  ≤  2*((2:ℝ)^84*(4*s^4)*((2:ℝ)^((9:ℝ)/64)*s^((3:ℝ)/8))) := by
      unfold Eexc
      exact mul_le_mul_of_nonneg_left (by simpa only [hτpow,hθ] using he) (by norm_num)
    _  ≤  2*((2:ℝ)^84*(4*s^4)*(2*s^((3:ℝ)/8))) := by gcongr
    _ = (2:ℝ)^88*(s^4*s^((3:ℝ)/8)) := by norm_num; ring
    _ = _ := by
      rw [←Real.rpow_natCast s 4,←Real.rpow_add hsp]
      norm_num

theorem quarter_exception_ratio (s ρ : ℝ) (hs : 1 ≤ s) (hρ : 0<ρ)
    (hsmall : ρ ≤ s^(-(4:ℝ))) :
    (V38Moments.exceptionCount ((1/(512*s^24))/4) 1:ℝ)/(s*(s^2/ρ))  ≤
      (2:ℝ)^85*s^(-(53:ℝ)/8) := by
  have hsp : 0<s := lt_of_lt_of_le (by norm_num) hs
  have he := quarter_exception_bound s hs
  have hcount : (0:ℝ) ≤ (V38Moments.exceptionCount ((1/(512*s^24))/4) 1:ℝ) := by positivity
  calc
    _ = (V38Moments.exceptionCount ((1/(512*s^24))/4) 1:ℝ)*ρ/s^3 := by field_simp
    _  ≤  ((2:ℝ)^85*s^((3:ℝ)/8))*s^(-(4:ℝ))/s^3 := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact mul_le_mul he hsmall hρ.le (by positivity)
    _ = (2:ℝ)^85*(s^((3:ℝ)/8)*s^(-(4:ℝ))/s^3) := by ring
    _ = _ := by
      rw [←Real.rpow_add hsp,rpow_div_nat s _ hsp 3]
      congr 1
      congr 1
      norm_num

theorem owner_exception_ratio (s : ℝ) (hs : 1 ≤ s) :
    2*s*Eexc s/((1/s^2)*s^8)  ≤  (2:ℝ)^89*s^(-(5:ℝ)/8) := by
  have hsp : 0<s := lt_of_lt_of_le (by norm_num) hs
  calc
    _ = 2*Eexc s/s^5 := by field_simp
    _  ≤  2*((2:ℝ)^88*s^((35:ℝ)/8))/s^5 := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact mul_le_mul_of_nonneg_left (owner_exception_bound s hs) (by norm_num)
    _ = (2:ℝ)^89*(s^((35:ℝ)/8)/s^5) := by norm_num; ring
    _ = _ := by
      rw [rpow_div_nat s _ hsp 5]
      congr 1
      congr 1
      norm_num

#print axioms quarter_exception_bound
#print axioms owner_exception_bound
#print axioms quarter_exception_ratio
#print axioms owner_exception_ratio
end CurrentAdditive.V42NumericMargins



