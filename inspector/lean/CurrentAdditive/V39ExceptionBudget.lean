import CurrentAdditive.V38Moments
import CurrentAdditive.V38Cutoff

/-!
The selected v39 exception count is bounded by the literal integer public
budget. This uses its current factor 2^20, not the older factor 1024.
Source: retained-tuples.tex `det:conditioning` and parameters.tex opening.
-/

namespace CurrentAdditive.V39ExceptionBudget

open V38Schedule

noncomputable def dyadic (b : ℕ) : ℝ := (2 : ℝ)^(-(b : ℝ))

theorem dyadic_pos (b : ℕ) : 0 < dyadic b := by unfold dyadic; positivity

theorem dyadic_le_one (b : ℕ) : dyadic b ≤ 1 := by
  unfold dyadic
  exact Real.rpow_le_one_of_one_le_of_nonpos (by norm_num)
    (neg_nonpos.mpr (Nat.cast_nonneg b))

theorem dyadic_epsilon (b : ℕ) :
    V38Moments.epsilon (dyadic b) 1 = (2 : ℝ)^(-(30 : ℝ)-(b : ℝ)/256) := by
  have hv : (dyadic b)^((1 : ℝ)/256)=(2 : ℝ)^(-(b : ℝ)/256) := by
    unfold dyadic
    rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    congr 1
    ring
  have hvle : (dyadic b)^((1 : ℝ)/256) ≤ 1 :=
    Real.rpow_le_one (dyadic_pos b).le (dyadic_le_one b) (by norm_num)
  have hc : (2 : ℝ)^(-30 : ℤ) ≤ 1 := by norm_num
  have hc0 : (0 : ℝ) ≤ (2 : ℝ)^(-30 : ℤ) := by positivity
  have hmin : (2 : ℝ)^(-30 : ℤ)*(dyadic b)^((1 : ℝ)/256) ≤ 1 := by
    nlinarith [mul_le_mul_of_nonneg_left hvle hc0]
  unfold V38Moments.epsilon
  rw [min_eq_right hmin,hv]
  rw [show (2 : ℝ)^(-30 : ℤ)=(2 : ℝ)^(-(30 : ℝ)) by norm_num [Real.rpow_neg]]
  rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
  congr 1
  ring

theorem dyadic_exception_inner (b : ℕ) :
    (2 : ℝ)^(20 : ℕ)*(V38Moments.epsilon (dyadic b) 1)^(-(2 : ℝ))*
      (dyadic b)^(-(1 : ℝ)/512) =
        (2 : ℝ)^((80 : ℝ)+5*(b : ℝ)/512) := by
  rw [dyadic_epsilon]
  have hv : (dyadic b)^(-(1 : ℝ)/512)=(2 : ℝ)^((b : ℝ)/512) := by
    unfold dyadic
    rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    congr 1
    ring
  have he : ((2 : ℝ)^(-(30 : ℝ)-(b : ℝ)/256))^(-(2 : ℝ))=
      (2 : ℝ)^(60+(b : ℝ)/128) := by
    rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    congr 1
    ring
  rw [hv,he,← Real.rpow_natCast (2 : ℝ) (20 : ℕ),
    ← Real.rpow_add (by norm_num : (0 : ℝ) < 2),
    ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
  congr 1
  ring

theorem dyadic_exception_upper (b : ℕ) :
    V38Moments.exceptionCount (dyadic b) 1 ≤ 2^(83+(5*b+511)/512) := by
  let t := (5*b+511)/512
  have ht : 5*(b : ℝ)/512 ≤ (t : ℝ) := by
    have hh : 5*b ≤ 512*t := by omega
    have hhR : (5 : ℝ)*b ≤ 512*(t : ℝ) := by exact_mod_cast hh
    linarith
  have hinner : (2 : ℝ)^(80+5*(b : ℝ)/512) ≤
      (2 : ℝ)^((80+t : ℕ) : ℝ) := by
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    push_cast
    linarith
  have hceil : ⌈(2 : ℝ)^(80+5*(b : ℝ)/512)⌉₊ ≤ 2^(80+t) := by
    apply Nat.ceil_le.mpr
    simpa only [Real.rpow_natCast,Nat.cast_pow,Nat.cast_ofNat] using hinner
  unfold V38Moments.exceptionCount
  rw [dyadic_exception_inner]
  calc
    8*⌈(2 : ℝ)^(80+5*(b : ℝ)/512)⌉₊ ≤ 8*2^(80+t) := Nat.mul_le_mul_left _ hceil
    _ = 2^(83+t) := by
      rw [show 8=2^3 by norm_num,← pow_add]
      congr 1
      omega

/-- Exact bridge from the current real conditioning count to the public
integer ebar used by the checker. It includes every dyadic exponent. -/
theorem exception_le_ebar (b : ℕ) :
    V38Moments.exceptionCount (dyadic b) 1 ≤ ebar b 1 := by
  rw [V38Cutoff.ebar_unit,← pow_add]
  apply (dyadic_exception_upper b).trans
  apply Nat.pow_le_pow_right (by decide : 0 < 2)
  have ht : b ≤ 64*((b+63)/64) := by omega
  have hu : (5*b+511)/512 ≤ (b+63)/64 := by omega
  omega

theorem generated_x_eq_dyadic (L : ℕ) :
    ((generatedX L : ℚ) : ℝ)=dyadic (8*L) := by
  unfold generatedX generatedN dyadic
  rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2),Real.rpow_natCast]
  push_cast
  rw [← pow_mul]
  norm_num [mul_comm,one_div]

theorem generated_exception_le_ebar (L : ℕ) :
    V38Moments.exceptionCount ((generatedX L : ℚ) : ℝ) 1 ≤ ebar (8*L) 1 := by
  rw [generated_x_eq_dyadic]
  exact exception_le_ebar (8*L)

#print axioms dyadic_pos
#print axioms dyadic_le_one
#print axioms dyadic_epsilon
#print axioms dyadic_exception_inner
#print axioms dyadic_exception_upper
#print axioms exception_le_ebar
#print axioms generated_x_eq_dyadic
#print axioms generated_exception_le_ebar

end CurrentAdditive.V39ExceptionBudget
