import CurrentAdditive.DeterministicParameters
import CurrentAdditive.ConditioningGeneralCore

namespace CurrentAdditive.DeterministicParameters

private noncomputable def incomingDyadicMass (a : ℕ) : ℝ := (2 : ℝ) ^ (-(a : ℝ))

private theorem incomingDyadicMass_pos (a : ℕ) : 0 < incomingDyadicMass a := by
  unfold incomingDyadicMass
  positivity
private theorem incoming_dyadic_exception_upper_at_tolerance
    (a t : ℕ) (τ : ℝ) (hτ : (2 : ℝ) ^ (-(t : ℝ)) ≤ τ) :
    CurrentAdditive.conditioningExceptionCount (incomingDyadicMass a) τ ≤
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
      CurrentAdditive.conditioningEpsilon (incomingDyadicMass a) τ := by
    unfold CurrentAdditive.conditioningEpsilon
    rw [show (2 : ℝ) ^ (-(20 : ℝ)) / 1024 = 2 ^ (-(30 : ℝ)) by
      norm_num [Real.rpow_neg, Real.rpow_natCast]]
    have hv : incomingDyadicMass a ^ ((4 : ℝ) / 1024) =
        (2 : ℝ) ^ (-(a : ℝ) / 256) := by
      unfold incomingDyadicMass
      rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
      congr 1
      ring
    rw [hv, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    have hsmallk' : (2 : ℝ) ^ (-(m : ℝ)) ≤
        (2 : ℝ) ^ (-(30 : ℝ) + -(a : ℝ) / 256) := by
      convert hsmallk using 1
      ring
    exact le_min hsmallτ hsmallk'
  have hεinv : (CurrentAdditive.conditioningEpsilon (incomingDyadicMass a) τ) ^
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
  have hvpow : incomingDyadicMass a ^ (-(2 / (1024 : ℝ))) ≤ (2 : ℝ) ^ (u : ℝ) := by
    have hv : incomingDyadicMass a ^ (-(2 / (1024 : ℝ))) =
        (2 : ℝ) ^ ((a : ℝ) / 512) := by
      unfold incomingDyadicMass
      rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
      congr 1
      ring
    rw [hv]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hau
  have hinner : (1024 : ℝ) *
      (CurrentAdditive.conditioningEpsilon (incomingDyadicMass a) τ) ^ (-(2 : ℝ)) *
      incomingDyadicMass a ^ (-(2 / (1024 : ℝ))) ≤
      (2 : ℝ) ^ ((10 + 2 * m + u : ℕ) : ℝ) := by
    have hεpos : 0 < CurrentAdditive.conditioningEpsilon (incomingDyadicMass a) τ :=
      lt_of_lt_of_le hsmall hε
    have hnonneg : 0 ≤ (CurrentAdditive.conditioningEpsilon (incomingDyadicMass a) τ) ^
        (-(2 : ℝ)) := (Real.rpow_pos_of_pos hεpos _).le
    have hvnonneg : 0 ≤ incomingDyadicMass a ^ (-(2 / (1024 : ℝ))) :=
      (Real.rpow_pos_of_pos (incomingDyadicMass_pos a) _).le
    calc
      _ ≤ (1024 : ℝ) * (2 : ℝ) ^ (2 * (m : ℝ)) *
          incomingDyadicMass a ^ (-(2 / (1024 : ℝ))) := by
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
      (CurrentAdditive.conditioningEpsilon (incomingDyadicMass a) τ) ^ (-(2 : ℝ)) *
      incomingDyadicMass a ^ (-(2 / (1024 : ℝ)))⌉₊ ≤ 2 ^ (10 + 2 * m + u) := by
    apply (Nat.ceil_le).2
    simpa only [Nat.cast_pow, Nat.cast_ofNat, Real.rpow_natCast] using hinner
  unfold CurrentAdditive.conditioningExceptionCount
  calc
    8 * ⌈(1024 : ℝ) *
        (CurrentAdditive.conditioningEpsilon (incomingDyadicMass a) τ) ^ (-(2 : ℝ)) *
        incomingDyadicMass a ^ (-(2 / (1024 : ℝ)))⌉₊ ≤ 8 * 2 ^ (10 + 2 * m + u) :=
      Nat.mul_le_mul_left _ hceil
    _ = 2 ^ (13 + 2 * m + u) := by
      rw [show 8 = 2 ^ 3 by norm_num, ← pow_add]
      congr 1
      omega
private theorem incoming_theta_real_dyadic (L : ℕ) :
    (θ L : ℝ) = incomingDyadicMass (9 + 6 * L) := by
  unfold θ incomingDyadicMass
  simp only [Rat.cast_div, Rat.cast_one, Rat.cast_mul, Rat.cast_natCast]
  rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_natCast]
  rw [one_div]
  congr 1
  norm_cast
  rw [Q_eq_pow, pow_add, pow_mul]
  norm_num

private theorem incoming_theta_quarter_real_dyadic (L : ℕ) :
    ((θ L / 4 : ℚ) : ℝ) = incomingDyadicMass (11 + 6 * L) := by
  rw [Rat.cast_div, Rat.cast_ofNat, incoming_theta_real_dyadic]
  unfold incomingDyadicMass
  rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2),
    Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
  rw [Real.rpow_natCast, Real.rpow_natCast]
  rw [div_eq_inv_mul, ← mul_inv_rev]
  congr 1
  rw [pow_add, pow_add]
  norm_num
  ring

/-- The actual dyadic density groups all fit inside the public selector
coordinate reserve, including the smallest group tolerance. -/
theorem incoming_exception_theta_quarter_all_groups
    (L : ℕ) (hL : 2004 ≤ L) (j : Fin (2*L+2)) :
    CurrentAdditive.conditioningExceptionCountR 1024
      ((θ L : ℝ)/4) (((1/2 : ℝ)^j.val)/2) ≤ s L*q₂ L := by
  let a := 11 + 6*L
  let t := j.val+1
  let b := (L+3)/4
  let m := max t (30 + (a+255)/256)
  let u := (a+511)/512
  have hτ : (2 : ℝ)^(-(t : ℝ)) ≤ ((1/2 : ℝ)^j.val)/2 := by
    dsimp [t]
    rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_natCast]
    have hpow : ((1/2 : ℝ)^j.val) = ((2 : ℝ)^j.val)⁻¹ := by
      rw [one_div, inv_pow]
    rw [hpow, pow_succ, mul_inv_rev]
    simp [div_eq_mul_inv, mul_comm]
  have hj : t ≤ 2*L+2 := by dsimp [t]; omega
  have hother : 30 + (a+255)/256 ≤ 2*L+2 := by
    have hd : 256 * ((a+255)/256) ≤ a+255 := Nat.mul_div_le _ _
    dsimp [a] at hd ⊢
    omega
  have hm : m ≤ 2*L+2 := max_le hj hother
  have hb : L ≤ 4*b := by dsimp [b]; omega
  have hd : 512*u ≤ a+511 := Nat.mul_div_le _ _
  have hu : 17+u ≤ b := by
    dsimp [a] at hd
    omega
  have hexp : 13+2*m+u ≤ 4*L+b := by omega
  have hbound := incoming_dyadic_exception_upper_at_tolerance a t
    (((1/2 : ℝ)^j.val)/2) hτ
  have ha : ((θ L : ℝ)/4) = incomingDyadicMass a := by
    dsimp [a]
    have hh := incoming_theta_quarter_real_dyadic L
    simpa only [Rat.cast_div, Rat.cast_ofNat] using hh
  have hcount : CurrentAdditive.conditioningExceptionCountR 1024
      ((θ L : ℝ)/4) (((1/2 : ℝ)^j.val)/2) ≤
      2^(13+2*m+u) := by
    rw [ha]
    simpa [CurrentAdditive.conditioningExceptionCountR,
      CurrentAdditive.conditioningExceptionCount,
      CurrentAdditive.conditioningEpsilonR,
      CurrentAdditive.conditioningEpsilon] using hbound
  calc
    _ ≤ 2^(13+2*m+u) := hcount
    _ ≤ 2^(4*L+b) := Nat.pow_le_pow_right (by decide) hexp
    _ = s L*q₂ L := by
      rw [show s L = 2^b by rfl, q₂_eq_pow, ← pow_add]
      congr 1
      omega

#print axioms incoming_exception_theta_quarter_all_groups

end CurrentAdditive.DeterministicParameters
