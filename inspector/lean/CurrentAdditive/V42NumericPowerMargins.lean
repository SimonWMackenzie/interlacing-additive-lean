import CurrentAdditive.V42ExceptionBudget


/-! Exact quantity-to-middle-column estimates in v42 eq:width-margins.
The real recipe is proved first; dyadic source parameters are specialized
separately. The exceptional count below is the actual natural ceiling count,
not the larger dyadic implementation budget. -/
namespace CurrentAdditive.V42NumericMargins
open scoped BigOperators
set_option maxHeartbeats 3000000
set_option maxRecDepth 32768

private theorem neg_nat_rpow (s : ℝ) (hs : 0<s) (n : ℕ) :
    s^(-(n:ℝ))=1/s^n := by
  rw [Real.rpow_neg hs.le,Real.rpow_natCast,one_div]

theorem rpow_div_nat (s p : ℝ) (hs : 0<s) (n : ℕ) :
    s^p/s^n=s^(p-(n:ℝ)) := by
  rw [Real.rpow_sub hs,Real.rpow_natCast]

/-- Substitute rho <= s^-4 into a monomial, without rounding a real exponent. -/
private theorem monomial_bound (s ρ : ℝ) (hs : 1 ≤ s) (hρ : 0 ≤ ρ)
    (hsmall : ρ ≤ s^(-(4:ℝ))) (a N : ℕ) :
    s^a*ρ^N  ≤  s^((a:ℝ)-4*(N:ℝ)) := by
  have hsp : 0<s := lt_of_lt_of_le (by norm_num) hs
  calc
    _  ≤  s^a*(s^(-(4:ℝ)))^N :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hρ hsmall N) (by positivity)
    _ = s^((a:ℝ)-4*(N:ℝ)) := by
      rw [←Real.rpow_natCast s a,←Real.rpow_mul_natCast hsp.le,
        ←Real.rpow_add hsp]
      congr 1
      ring

theorem source_eta (s : ℝ) (hs : 0<s) : s*(1/s^2)=s^(-(1:ℝ)) := by
  rw [Real.rpow_neg_one]
  field_simp

theorem edge_width (s ρ n m Δ : ℝ) (hs : 0<s) (hρ : 0<ρ)
    (hΔ : 0 ≤ Δ) (hn : n ≤ 1/ρ) (hm : 2*m ≤ Δ*n) :
    4*s*m/(s^2/ρ)  ≤  2*Δ/s := by
  have hnρ : n*ρ ≤ 1 := (le_div_iff₀ hρ).1 hn
  have hmρ := mul_le_mul_of_nonneg_right hm hρ.le
  have hΔn := mul_le_mul_of_nonneg_left hnρ hΔ
  have hfinal : 2*m*ρ ≤ Δ := by nlinarith
  calc
    _ = (2/s)*(2*m*ρ) := by field_simp; ring
    _  ≤  (2/s)*Δ := mul_le_mul_of_nonneg_left hfinal (by positivity)
    _ = _ := by ring

theorem small_mass (s ρ : ℝ) (hs : 1 ≤ s) (hρ : 0 ≤ ρ)
    (hsmall : ρ ≤ s^(-(4:ℝ))) : s^2*ρ ≤ s^(-(2:ℝ)) := by
  simpa only [Nat.cast_ofNat,Nat.cast_one,pow_one,show (2:ℝ)-4*1 = -2 by norm_num] using
    monomial_bound s ρ hs hρ hsmall 2 1

theorem collision (s ρ : ℝ) (hs : 0<s) (hρ : 0<ρ)
    (hsmall : ρ ≤ s^(-(4:ℝ))) : s*(s-2)/(s^2/ρ) ≤ s^(-(4:ℝ)) := by
  have hq : 0<s^2/ρ := by positivity
  apply le_trans (b:=ρ) _ hsmall
  apply (div_le_iff₀ hq).2
  have he : ρ*(s^2/ρ)=s^2 := by field_simp
  rw [he]
  nlinarith

private theorem q2x_eq (s ρ : ℝ) (hρ : ρ ≠ 0) :
    (s^2/ρ)*ρ^8=s^2*ρ^7 := by field_simp

private theorem w2x_eta_eq (s ρ : ℝ) (hs : s ≠ 0) :
    (s^8)^2*ρ^8/(1/s^2)=s^18*ρ^8 := by field_simp

private theorem w2q2x_eq (s ρ : ℝ) (hρ : ρ ≠ 0) :
    (s^8)^2*(s^2/ρ)*ρ^8=s^18*ρ^7 := by field_simp

private theorem wq2x_eta_eq (s ρ : ℝ) (hs : s ≠ 0) (hρ : ρ ≠ 0) :
    s^8*(s^2/ρ)*ρ^8/(1/s^2)=s^12*ρ^7 := by field_simp

theorem max_width_x (s ρ : ℝ) (hs : 1 ≤ s) (hρ : 0<ρ)
    (hsmall : ρ ≤ s^(-(4:ℝ))) :
    max ((s^2/ρ)*ρ^8) (max (s*ρ^8) (s^8*ρ^8)) ≤ s^(-(24:ℝ)) := by
  apply max_le
  · rw [q2x_eq s ρ hρ.ne']
    exact (monomial_bound s ρ hs hρ.le hsmall 2 7).trans
      (Real.rpow_le_rpow_of_exponent_le hs (by norm_num))
  · apply max_le
    · have h := monomial_bound s ρ hs hρ.le hsmall 1 8
      simp only [pow_one] at h
      exact h.trans (Real.rpow_le_rpow_of_exponent_le hs (by norm_num))
    · simpa only [Nat.cast_ofNat,show (8:ℝ)-4*8 = -24 by norm_num] using
        monomial_bound s ρ hs hρ.le hsmall 8 8

theorem w2x_over_eta (s ρ : ℝ) (hs : 1 ≤ s) (hρ : 0 ≤ ρ)
    (hsmall : ρ ≤ s^(-(4:ℝ))) : (s^8)^2*ρ^8/(1/s^2) ≤ s^(-(14:ℝ)) := by
  have hsp : 0<s := lt_of_lt_of_le (by norm_num) hs
  rw [w2x_eta_eq s ρ hsp.ne']
  simpa only [Nat.cast_ofNat,show (18:ℝ)-4*8 = -14 by norm_num] using
    monomial_bound s ρ hs hρ hsmall 18 8

theorem w2q2x (s ρ : ℝ) (hs : 1 ≤ s) (hρ : 0<ρ)
    (hsmall : ρ ≤ s^(-(4:ℝ))) : (s^8)^2*(s^2/ρ)*ρ^8 ≤ s^(-(10:ℝ)) := by
  rw [w2q2x_eq s ρ hρ.ne']
  simpa only [Nat.cast_ofNat,show (18:ℝ)-4*7 = -10 by norm_num] using
    monomial_bound s ρ hs hρ.le hsmall 18 7

theorem wq2x_over_eta (s ρ : ℝ) (hs : 1 ≤ s) (hρ : 0<ρ)
    (hsmall : ρ ≤ s^(-(4:ℝ))) : s^8*(s^2/ρ)*ρ^8/(1/s^2) ≤ s^(-(16:ℝ)) := by
  have hsp : 0<s := lt_of_lt_of_le (by norm_num) hs
  rw [wq2x_eta_eq s ρ hsp.ne' hρ.ne']
  simpa only [Nat.cast_ofNat,show (12:ℝ)-4*7 = -16 by norm_num] using
    monomial_bound s ρ hs hρ.le hsmall 12 7

theorem flag_ratio_identity (s C : ℝ) (hs : 0<s) :
    C*s^(-(128:ℝ))/(1/(512*s^24))=512*C*s^(-(104:ℝ)) := by
  have h128 : s^(-(128:ℝ))=1/s^128 := by simpa using neg_nat_rpow s hs 128
  have h104 : s^(-(104:ℝ))=1/s^104 := by simpa using neg_nat_rpow s hs 104
  rw [h128,h104]
  field_simp

#print axioms source_eta
#print axioms edge_width
#print axioms small_mass
#print axioms collision
#print axioms max_width_x
#print axioms w2x_over_eta
#print axioms w2q2x
#print axioms wq2x_over_eta
#print axioms flag_ratio_identity
end CurrentAdditive.V42NumericMargins




