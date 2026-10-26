import CurrentAdditive.V39GeneralExceptionBudget

/-! Literal v42 `eq:conditioning-size-bound`, including the natural ceiling
in `V38Moments.exceptionCount`. -/

namespace CurrentAdditive.V42ExceptionBudget

set_option maxHeartbeats 1000000
set_option maxRecDepth 8192

private theorem scaled_epsilon_term (v : ℝ) (hv : 0 < v) :
    (2 : ℝ)^20 * ((2 : ℝ)^(-30 : ℤ)*v^((1 : ℝ)/256))^(-(2 : ℝ)) *
      v^(-(1 : ℝ)/512) = (2 : ℝ)^80*v^(-(5 : ℝ)/512) := by
  rw [Real.mul_rpow (by positivity) (Real.rpow_nonneg hv.le _)]
  rw [← Real.rpow_mul hv.le]
  have hc : ((2 : ℝ)^(-30 : ℤ))^(-(2 : ℝ)) = (2 : ℝ)^60 := by
    norm_num [Real.rpow_neg, Real.rpow_two]
  rw [hc]
  have hexp : (1 : ℝ)/256 * (-2) = -(1 : ℝ)/128 := by norm_num
  rw [hexp]
  calc
    _ = ((2 : ℝ)^20*(2 : ℝ)^60) *
        (v^(-(1 : ℝ)/128)*v^(-(1 : ℝ)/512)) := by ring
    _ = (2 : ℝ)^80 * v^(-(5 : ℝ)/512) := by
      rw [← pow_add, ← Real.rpow_add hv]
      norm_num

/-- The first displayed source estimate, with the ceiling contributing 8. -/
theorem exceptionCount_three_term_bound (v τ : ℝ) (hv : 0 < v) (hτ : 0 < τ) :
    (V38Moments.exceptionCount v τ : ℝ) ≤
      8 + (2 : ℝ)^23*τ^(-(2 : ℝ))*v^(-(1 : ℝ)/512) +
        (2 : ℝ)^83*v^(-(5 : ℝ)/512) := by
  let z : ℝ := (2 : ℝ)^20*(V38Moments.epsilon v τ)^(-(2 : ℝ))*
    v^(-(1 : ℝ)/512)
  let A : ℝ := (2 : ℝ)^20*τ^(-(2 : ℝ))*v^(-(1 : ℝ)/512)
  let B : ℝ := (2 : ℝ)^80*v^(-(5 : ℝ)/512)
  have hε : 0 < V38Moments.epsilon v τ := by
    unfold V38Moments.epsilon
    exact lt_min hτ (mul_pos (by positivity) (Real.rpow_pos_of_pos hv _))
  have hz : 0 ≤ z := by dsimp [z]; positivity
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hzAB : z ≤ A+B := by
    by_cases hc : τ ≤ (2 : ℝ)^(-30 : ℤ)*v^((1 : ℝ)/256)
    · have heq : V38Moments.epsilon v τ = τ := min_eq_left hc
      dsimp [z]
      rw [heq]
      change A ≤ A+B
      linarith
    · have heq : V38Moments.epsilon v τ =
          (2 : ℝ)^(-30 : ℤ)*v^((1 : ℝ)/256) := min_eq_right (le_of_not_ge hc)
      dsimp [z]
      rw [heq, scaled_epsilon_term v hv]
      change B ≤ A+B
      linarith
  have hceil : (⌈z⌉₊ : ℝ) ≤ z+1 := (Nat.ceil_lt_add_one hz).le
  have hcount : (V38Moments.exceptionCount v τ : ℝ) = 8*(⌈z⌉₊ : ℝ) := by
    unfold V38Moments.exceptionCount
    change ((8*⌈z⌉₊ : ℕ) : ℝ) = _
    push_cast
    rfl
  rw [hcount]
  calc
    _ ≤ 8*(A+B+1) := by linarith
    _ = _ := by dsimp [A,B]; norm_num; ring

/-- The exact v42 bound for all admissible real masses and tolerances.
No dyadic restriction or assumed exceptional-coordinate estimate occurs. -/
theorem exceptionCount_real_bound (v τ : ℝ)
    (hv : 0 < v) (hv1 : v ≤ 1) (hτ : 0 < τ) (hτ1 : τ ≤ 1) :
    (V38Moments.exceptionCount v τ : ℝ) ≤
      (2 : ℝ)^84*τ^(-(2 : ℝ))*v^(-(1 : ℝ)/64) := by
  have hτpow : 1 ≤ τ^(-(2 : ℝ)) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hτ hτ1 (by norm_num)
  have hvpow : 1 ≤ v^(-(1 : ℝ)/64) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hv hv1 (by norm_num)
  have hvsmall : v^(-(1 : ℝ)/512) ≤ v^(-(1 : ℝ)/64) :=
    Real.rpow_le_rpow_of_exponent_ge hv hv1 (by norm_num)
  have hvlarge : v^(-(5 : ℝ)/512) ≤ v^(-(1 : ℝ)/64) :=
    Real.rpow_le_rpow_of_exponent_ge hv hv1 (by norm_num)
  let T : ℝ := τ^(-(2 : ℝ))*v^(-(1 : ℝ)/64)
  have hT : 1 ≤ T := by dsimp [T]; nlinarith
  have hfirst : τ^(-(2 : ℝ))*v^(-(1 : ℝ)/512) ≤ T :=
    mul_le_mul_of_nonneg_left hvsmall (by positivity)
  have hsecond : v^(-(5 : ℝ)/512) ≤ T := by
    calc
      _ ≤ v^(-(1 : ℝ)/64) := hvlarge
      _ ≤ T := by dsimp [T]; nlinarith
  have hthree := exceptionCount_three_term_bound v τ hv hτ
  have hscale : 8 + (2 : ℝ)^23*τ^(-(2 : ℝ))*v^(-(1 : ℝ)/512) +
      (2 : ℝ)^83*v^(-(5 : ℝ)/512) ≤
      (8+(2 : ℝ)^23+(2 : ℝ)^83)*T := by
    have hp := mul_le_mul_of_nonneg_left hfirst (by positivity : (0 : ℝ) ≤ 2^23)
    have hq := mul_le_mul_of_nonneg_left hsecond (by positivity : (0 : ℝ) ≤ 2^83)
    nlinarith
  calc
    _ ≤ (8+(2 : ℝ)^23+(2 : ℝ)^83)*T := hthree.trans hscale
    _ ≤ (2 : ℝ)^84*T := by
      apply mul_le_mul_of_nonneg_right _ (by linarith : 0 ≤ T)
      norm_num
    _ = _ := by dsimp [T]; ring

#print axioms exceptionCount_three_term_bound
#print axioms exceptionCount_real_bound

end CurrentAdditive.V42ExceptionBudget
