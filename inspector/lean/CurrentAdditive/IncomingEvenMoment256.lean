import CurrentAdditive.EvenMoment

/-! Appendix I `det:incoming`: the independent comparison bound at the
manuscript's moment order 256. -/

namespace CurrentAdditive.EvenMoment

open Paper2

variable {Ω : Type*} [Fintype Ω]

private theorem factorial_256_bound :
    Nat.factorial 256 ≤ (128 * 129) ^ 128 := by
  have hfac : Nat.factorial 256 =
      (∏ i ∈ Finset.range 128, (i + 1) * (256 - i)) := by
    rw [Nat.factorial_eq_prod_range_add_one,
      show 256 = 128 + 128 by omega, Finset.prod_range_add]
    have hreflect : (∏ i ∈ Finset.range 128, (128 + i + 1)) =
        ∏ i ∈ Finset.range 128, (256 - i) := by
      rw [← Finset.prod_range_reflect (fun i => 128 + i + 1) 128]
      apply Finset.prod_congr rfl
      intro i hi
      have hii := Finset.mem_range.mp hi
      omega
    rw [hreflect, ← Finset.prod_mul_distrib]
  rw [hfac]
  calc
    _ ≤ ∏ _i ∈ Finset.range 128, (128 * 129) := by
      apply Finset.prod_le_prod
      · intro i hi
        omega
      · intro i hi
        have hii := Finset.mem_range.mp hi
        have h1 : (127 - i) + i = 127 := by omega
        have h2 : (128 - i) + i = 128 := by omega
        have h3 : (256 - i) + i = 256 := by omega
        have hp : 0 ≤ (127 - i) * (128 - i) := Nat.zero_le _
        nlinarith
    _ = _ := by simp [Finset.prod_const]

private theorem factorial_exp_256_bound :
    (Nat.factorial 256 : ℝ) * Real.exp 128 ≤ (256 : ℝ) ^ 256 := by
  have hfac : (Nat.factorial 256 : ℝ) ≤ (16512 : ℝ) ^ 128 := by
    exact_mod_cast factorial_256_bound
  have hexp : Real.exp 128 ≤ (3 : ℝ) ^ 128 := by
    rw [show (128 : ℝ) = (128 : ℕ) * (1 : ℝ) by norm_num,
      Real.exp_nat_mul]
    exact pow_le_pow_left₀ (Real.exp_pos _).le Real.exp_one_lt_three.le _
  calc
    (Nat.factorial 256 : ℝ) * Real.exp 128 ≤
        (16512 : ℝ) ^ 128 * (3 : ℝ) ^ 128 := by gcongr
    _ = (49536 : ℝ) ^ 128 := by rw [← mul_pow]; norm_num
    _ ≤ (65536 : ℝ) ^ 128 := by gcongr; norm_num
    _ = (256 : ℝ) ^ 256 := by
      rw [show (65536 : ℝ) = (256 : ℝ) ^ 2 by norm_num, ← pow_mul]

/-- For independent, potentially different Boolean tests, the exact 256th
centered moment is at most `2*(64m)^128`. -/
theorem iid_centered_indicator_moment_256 (ν : FiniteLaw Ω) (m : ℕ)
    (F : Fin m → Ω → Bool) :
    ex (ν.iid m) (fun ws => |∑ i : Fin m,
      ((if F i (ws i) then (1 : ℝ) else 0) -
        ν.prob (fun ω => F i ω))| ^ 256) ≤
      2 * ((64 : ℝ) * m) ^ 128 := by
  classical
  let S : (Fin m → Ω) → ℝ := fun ws => ∑ i : Fin m,
    ((if F i (ws i) then (1 : ℝ) else 0) - ν.prob (fun ω => F i ω))
  change ex (ν.iid m) (fun ws => |S ws| ^ 256) ≤ _
  by_cases hm : m = 0
  · subst m
    simp [S, ex, FiniteLaw.iid]
  have hmpos : 0 < (m : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hm)
  let t : ℝ := 32 / Real.sqrt m
  have hsqrt : 0 < Real.sqrt (m : ℝ) := Real.sqrt_pos.2 hmpos
  have ht : 0 < t := by dsimp [t]; positivity
  have hmt : (m : ℝ) * t ^ 2 / 8 = 128 := by
    dsimp [t]
    rw [div_pow, Real.sq_sqrt hmpos.le]
    field_simp
    ring
  have hplus : ex (ν.iid m) (fun ws => Real.exp (t * S ws)) ≤
      Real.exp 128 := by
    simpa [S, hmt] using iid_centered_indicator_mgf ν m F t
  have hminus : ex (ν.iid m) (fun ws => Real.exp (-t * S ws)) ≤
      Real.exp 128 := by
    simpa [S, neg_sq, hmt] using iid_centered_indicator_mgf ν m F (-t)
  have hraw := moment_le_of_two_sided_mgf (ν.iid m) S 256
    (by norm_num : Even 256) t (Real.exp 128) ht hplus hminus
  have ht256 : 0 < t ^ 256 := pow_pos ht _
  have htprod : t ^ 2 * (m : ℝ) = (32 : ℝ) ^ 2 := by
    nlinarith [hmt]
  have hpowequal : t ^ 256 * (m : ℝ) ^ 128 =
      (32 : ℝ) ^ 256 := by
    calc
      _ = (t ^ 2) ^ 128 * (m : ℝ) ^ 128 := by
        rw [← pow_mul, show 2 * 128 = 256 by norm_num]
      _ = (t ^ 2 * (m : ℝ)) ^ 128 := by simp only [mul_pow]
      _ = ((32 : ℝ) ^ 2) ^ 128 := by rw [htprod]
      _ = (32 : ℝ) ^ 256 := by rw [← pow_mul]
  calc
    ex (ν.iid m) (fun ws => |S ws| ^ 256) ≤
        2 * (Nat.factorial 256 : ℝ) * Real.exp 128 / t ^ 256 := hraw
    _ ≤ 2 * (256 : ℝ) ^ 256 / t ^ 256 := by
      apply (div_le_div_iff_of_pos_right ht256).2
      nlinarith [factorial_exp_256_bound]
    _ = 2 * ((64 : ℝ) * m) ^ 128 := by
      apply (div_eq_iff ht256.ne').2
      have hpow : (256 : ℝ) ^ 256 =
          (32 : ℝ) ^ 256 * (64 : ℝ) ^ 128 := by
        rw [show (256 : ℝ) = 32 * 8 by norm_num, mul_pow,
          show (8 : ℝ) ^ 256 = (64 : ℝ) ^ 128 by
            rw [show (64 : ℝ) = (8 : ℝ) ^ 2 by norm_num, ← pow_mul]]
      rw [hpow, ← hpowequal]
      rw [mul_pow]
      ring

#print axioms iid_centered_indicator_moment_256

end CurrentAdditive.EvenMoment
