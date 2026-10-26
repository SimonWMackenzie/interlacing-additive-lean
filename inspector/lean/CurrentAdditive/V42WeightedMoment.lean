import CurrentAdditive.V39GeneralMoment

/-! Weighted finite-law moments for v42 `lem:conditioning-moment`.
The bound is proved from one-coordinate Hoeffding bounds, genuine independent
product laws, and bounded-wise event-law equality. -/

namespace V42WeightedMoment

open Paper2 Paper2.FiniteLaw CurrentAdditive.EvenMoment V38GeneralMoment
open scoped BigOperators

set_option maxHeartbeats 1000000
set_option maxRecDepth 8192

variable {Ω : Type*} [Fintype Ω]

theorem jointLawAgreement_mul (ν : FiniteLaw Ω) {m R : ℕ}
    (X : Fin m → Ω → ℝ) (a : Fin m → ℝ)
    (hjoint : JointLawAgreement ν X R) :
    JointLawAgreement ν (fun i ω => a i * X i ω) R := by
  intro s hs E
  exact hjoint s hs (fun y => E (fun i => a i * y i))

theorem iid_weighted_centered_mgf (ν : FiniteLaw Ω) (m : ℕ)
    (a : Fin m → ℝ) (ha0 : ∀ i, 0 ≤ a i) (ha1 : ∀ i, a i ≤ 1)
    (X : Fin m → Ω → ℝ) (hcenter : ∀ i, ex ν (X i) = 0)
    (hbound : ∀ i ω, |X i ω| ≤ 1) (t : ℝ) :
    ex (ν.iid m) (fun ws => Real.exp (t * ∑ i, a i * X i (ws i))) ≤
      Real.exp ((∑ i, a i) * t^2/2) := by
  classical
  rw [iid_exp_sum_indexed ν m (fun i ω => a i * X i ω) t]
  have hp : (∏ i : Fin m, ex ν (fun ω => Real.exp (t * (a i * X i ω)))) ≤
      ∏ i : Fin m, Real.exp ((a i * t)^2/2) := by
    apply Finset.prod_le_prod
    · intro i _
      unfold ex
      exact Finset.sum_nonneg fun ω _ => mul_nonneg (ν.nonneg ω) (Real.exp_pos _).le
    · intro i _
      have hh := bounded_centered_mgf ν (X i) (hcenter i) (hbound i) (a i*t)
      have heq : (fun ω => Real.exp (t*(a i*X i ω))) =
          (fun ω => Real.exp ((a i*t)*X i ω)) := by
        funext ω
        congr 1
        ring
      rw [heq]
      exact hh
  calc
    _ ≤ ∏ i : Fin m, Real.exp ((a i*t)^2/2) := hp
    _ = Real.exp (∑ i, (a i*t)^2/2) := (Real.exp_sum _ _).symm
    _ ≤ Real.exp ((∑ i, a i)*t^2/2) := by
      apply Real.exp_le_exp.mpr
      rw [Finset.sum_mul, Finset.sum_div]
      apply Finset.sum_le_sum
      intro i _
      have ha : (a i)^2 ≤ a i := by nlinarith [ha0 i, ha1 i]
      nlinarith [mul_nonneg (sub_nonneg.mpr ha) (sq_nonneg t)]

private theorem factorial_even_le_pair_pow (r : ℕ) (hr : 0 < r) :
    Nat.factorial (2 * r) ≤ (r * (r + 1)) ^ r := by
  have hfac : Nat.factorial (2 * r) =
      ∏ i ∈ Finset.range r, (i + 1) * (2 * r - i) := by
    rw [Nat.factorial_eq_prod_range_add_one,
      show 2 * r = r + r by omega, Finset.prod_range_add]
    have hreflect : (∏ i ∈ Finset.range r, (r + i + 1)) =
        ∏ i ∈ Finset.range r, (2 * r - i) := by
      rw [← Finset.prod_range_reflect (fun i => r + i + 1) r]
      apply Finset.prod_congr rfl
      intro i hi
      have hii := Finset.mem_range.mp hi
      omega
    rw [hreflect, ← Finset.prod_mul_distrib]
    simp only [two_mul]
  rw [hfac]
  calc
    _ ≤ ∏ _i ∈ Finset.range r, (r * (r + 1)) := by
      apply Finset.prod_le_prod
      · intro i hi; omega
      · intro i hi
        have hii := Finset.mem_range.mp hi
        have h1 : (r - 1 - i) + i = r - 1 := by omega
        have h2 : (r - i) + i = r := by omega
        have h3 : (2 * r - i) + i = 2 * r := by omega
        have hp : 0 ≤ (r - 1 - i) * (r - i) := Nat.zero_le _
        nlinarith
    _ = _ := by simp [Finset.prod_const]

theorem iid_weighted_even_moment_ge_three
    (ν : FiniteLaw Ω) (m r : ℕ) (hr : 3 ≤ r)
    (a : Fin m → ℝ) (ha0 : ∀ i, 0 ≤ a i) (ha1 : ∀ i, a i ≤ 1)
    (hW : 0 < ∑ i, a i)
    (X : Fin m → Ω → ℝ) (hcenter : ∀ i, ex ν (X i) = 0)
    (hbound : ∀ i ω, |X i ω| ≤ 1) :
    ex (ν.iid m) (fun ws => |∑ i, a i * X i (ws i)|^(2*r)) ≤
      (((r : ℝ)^2)*(∑ i, a i))^r := by
  classical
  let W : ℝ := ∑ i, a i
  let S : (Fin m → Ω) → ℝ := fun ws => ∑ i, a i * X i (ws i)
  change ex (ν.iid m) (fun ws => |S ws|^(2*r)) ≤ (((r : ℝ)^2)*W)^r
  have hWpos : 0 < W := hW
  have hrpos : (0 : ℝ) < r := Nat.cast_pos.mpr (by omega)
  let t : ℝ := Real.sqrt (2*(r : ℝ)/W)
  have htarg : 0 < 2*(r : ℝ)/W := by positivity
  have ht : 0 < t := Real.sqrt_pos.2 htarg
  have ht2 : t^2 = 2*(r : ℝ)/W := Real.sq_sqrt htarg.le
  have hmt : W*t^2/2 = (r : ℝ) := by rw [ht2]; field_simp
  have hplus : ex (ν.iid m) (fun ws => Real.exp (t*S ws)) ≤
      Real.exp (r : ℝ) := by
    have hh := iid_weighted_centered_mgf ν m a ha0 ha1 X hcenter hbound t
    change ex (ν.iid m) (fun ws => Real.exp (t*S ws)) ≤ Real.exp (W*t^2/2) at hh
    simpa only [hmt] using hh
  have hminus : ex (ν.iid m) (fun ws => Real.exp (-t*S ws)) ≤
      Real.exp (r : ℝ) := by
    have hh := iid_weighted_centered_mgf ν m a ha0 ha1 X hcenter hbound (-t)
    change ex (ν.iid m) (fun ws => Real.exp (-t*S ws)) ≤ Real.exp (W*(-t)^2/2) at hh
    simpa only [neg_sq, hmt] using hh
  have hraw := moment_le_of_two_sided_mgf (ν.iid m) S (2*r)
    (by simp : Even (2*r)) t (Real.exp (r : ℝ)) ht hplus hminus
  have hfac : (Nat.factorial (2*r) : ℝ) ≤ ((r : ℝ)*(r+1))^r := by
    exact_mod_cast factorial_even_le_pair_pow r (by omega)
  have hexp : Real.exp (r : ℝ) ≤ (3 : ℝ)^r := by
    rw [show (r : ℝ) = (r : ℕ)*(1 : ℝ) by simp, Real.exp_nat_mul]
    exact pow_le_pow_left₀ (Real.exp_pos _).le Real.exp_one_lt_three.le _
  have h15 : (2 : ℝ) ≤ (3/2 : ℝ)^r := by
    calc
      (2 : ℝ) ≤ (3/2 : ℝ)^3 := by norm_num
      _ ≤ (3/2 : ℝ)^r := pow_le_pow_right₀ (by norm_num) hr
  have hrR : (3 : ℝ) ≤ r := by exact_mod_cast hr
  have hpoly : (9/2 : ℝ)*(r : ℝ)*(r+1) ≤ 2*(r : ℝ)^3 := by
    have hp := mul_nonneg
      (mul_nonneg (le_of_lt hrpos) (by linarith : 0 ≤ (r : ℝ)-3))
      (by linarith : 0 ≤ 2*(r : ℝ)+3/2)
    nlinarith
  have hfacexp : 2*(Nat.factorial (2*r) : ℝ)*Real.exp (r : ℝ) ≤
      (2*(r : ℝ)^3)^r := by
    calc
      _ ≤ 2*((r : ℝ)*(r+1))^r*(3 : ℝ)^r := by gcongr
      _ = 2*(3*(r : ℝ)*(r+1))^r := by
        calc
          _ = 2*(((r : ℝ)*(r+1))^r*(3 : ℝ)^r) := by ring
          _ = 2*(((r : ℝ)*(r+1))*3)^r := by simp only [mul_pow]
          _ = 2*(3*(r : ℝ)*(r+1))^r := by congr 1; congr 1; ring
      _ ≤ (3/2 : ℝ)^r*(3*(r : ℝ)*(r+1))^r := by
        apply mul_le_mul_of_nonneg_right h15
        positivity
      _ = ((9/2 : ℝ)*(r : ℝ)*(r+1))^r := by
        rw [← mul_pow]; congr 1; ring
      _ ≤ (2*(r : ℝ)^3)^r := by gcongr
  have htpow : 0 < t^(2*r) := pow_pos ht _
  have htprod : t^2 * ((r : ℝ)^2*W) = 2*(r : ℝ)^3 := by
    rw [ht2]; field_simp
  have hpowequal : t^(2*r) * ((r : ℝ)^2*W)^r = (2*(r : ℝ)^3)^r := by
    calc
      _ = (t^2)^r * ((r : ℝ)^2*W)^r := by rw [← pow_mul]
      _ = (t^2*((r : ℝ)^2*W))^r := (mul_pow _ _ _).symm
      _ = _ := by rw [htprod]
  calc
    _ ≤ 2*(Nat.factorial (2*r) : ℝ)*Real.exp (r : ℝ)/t^(2*r) := hraw
    _ ≤ (2*(r : ℝ)^3)^r/t^(2*r) := div_le_div_of_nonneg_right hfacexp htpow.le
    _ = ((r : ℝ)^2*W)^r := by
      apply (div_eq_iff htpow.ne').2
      rw [← hpowequal]
      ring

theorem bounded_wise_even_moment_ge_three
    (ν : FiniteLaw Ω) (m r : ℕ) (hr : 3 ≤ r)
    (a : Fin m → ℝ) (ha0 : ∀ i, 0 ≤ a i) (ha1 : ∀ i, a i ≤ 1)
    (hW : 0 < ∑ i, a i)
    (X : Fin m → Ω → ℝ) (hcenter : ∀ i, ex ν (X i) = 0)
    (hbound : ∀ i ω, |X i ω| ≤ 1)
    (hjoint : JointLawAgreement ν X (2*r)) :
    ex ν (fun ω => |∑ i, a i * X i ω|^(2*r)) ≤
      (((r : ℝ)^2)*(∑ i, a i))^r := by
  have hraw := bounded_wise_raw_moment_eq_iid ν (fun i ω => a i * X i ω)
    (jointLawAgreement_mul ν X a hjoint)
  have habs (x : ℝ) : |x|^(2*r) = x^(2*r) :=
    (show Even (2*r) by simp).pow_abs x
  calc
    _ = ex ν (fun ω => (∑ i, a i * X i ω)^(2*r)) := by simp_rw [habs]
    _ = ex (ν.iid m) (fun ws => (∑ i, a i * X i (ws i))^(2*r)) := hraw
    _ = ex (ν.iid m) (fun ws => |∑ i, a i * X i (ws i)|^(2*r)) := by simp_rw [habs]
    _ ≤ _ := iid_weighted_even_moment_ge_three ν m r hr a ha0 ha1 hW X hcenter hbound

theorem bounded_wise_moment_256
    (ν : FiniteLaw Ω) (m : ℕ) (a : Fin m → ℝ)
    (ha0 : ∀ i, 0 ≤ a i) (ha1 : ∀ i, a i ≤ 1) (hW : 0 < ∑ i, a i)
    (X : Fin m → Ω → ℝ) (hcenter : ∀ i, ex ν (X i) = 0)
    (hbound : ∀ i ω, |X i ω| ≤ 1)
    (hjoint : JointLawAgreement ν X 256) :
    ex ν (fun ω => |∑ i, a i * X i ω|^256) ≤
      ((2 : ℝ)^14*(∑ i, a i))^128 := by
  simpa only [show 2*128 = 256 by rfl,
    show ((128 : ℕ) : ℝ)^2 = (2 : ℝ)^14 by norm_num] using
      bounded_wise_even_moment_ge_three ν m 128 (by omega) a ha0 ha1 hW X hcenter hbound hjoint

#print axioms bounded_wise_moment_256
#print axioms bounded_wise_even_moment_ge_three
#print axioms iid_weighted_centered_mgf

end V42WeightedMoment
