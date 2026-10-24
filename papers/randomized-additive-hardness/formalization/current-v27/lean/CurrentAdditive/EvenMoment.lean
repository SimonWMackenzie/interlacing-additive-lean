import Paper2.YaoSelectorEventsConcentration

/-!
Private development for the missing `det:even-moment` premise in v27.
This file is separate from the frozen, independently reviewed Hölder/count file.
-/

namespace CurrentAdditive.EvenMoment

open scoped BigOperators

variable {Ω : Type*} [Fintype Ω]

noncomputable def ex (ν : Paper2.FiniteLaw Ω) (X : Ω → ℝ) : ℝ :=
  ∑ ω, ν.weight ω * X ω

/-- The elementary exponential-series estimate, with both signs so it works
for every real input at an even natural order. -/
private theorem even_pow_le_two_exps (R : ℕ) (hR : Even R) (x : ℝ) :
    x ^ R ≤ (R.factorial : ℝ) * (Real.exp x + Real.exp (-x)) := by
  have hseries := Real.pow_div_factorial_le_exp |x| (abs_nonneg x) R
  have hfact : (0 : ℝ) < R.factorial := by positivity
  have habs : |x| ^ R = x ^ R := hR.pow_abs x
  have hbound : x ^ R ≤ (R.factorial : ℝ) * Real.exp |x| := by
    rw [← habs]
    simpa [mul_comm] using (div_le_iff₀ hfact).mp hseries
  by_cases hx : 0 ≤ x
  · rw [abs_of_nonneg hx] at hbound
    exact hbound.trans (by
      have he : 0 ≤ Real.exp (-x) := (Real.exp_pos _).le
      nlinarith)
  · rw [abs_of_neg (lt_of_not_ge hx)] at hbound
    exact hbound.trans (by
      have he : 0 ≤ Real.exp x := (Real.exp_pos _).le
      nlinarith)

/-- A finite-law high moment from two-sided exponential-moment bounds.
This is proved pointwise from the exponential series and finite summation. -/
theorem moment_le_of_two_sided_mgf (ν : Paper2.FiniteLaw Ω)
    (S : Ω → ℝ) (R : ℕ) (hR : Even R) (t B : ℝ) (ht : 0 < t)
    (hplus : ex ν (fun ω => Real.exp (t * S ω)) ≤ B)
    (hminus : ex ν (fun ω => Real.exp (-t * S ω)) ≤ B) :
    ex ν (fun ω => |S ω| ^ R) ≤
      2 * (R.factorial : ℝ) * B / t ^ R := by
  have htR : 0 < t ^ R := pow_pos ht _
  have hterm (ω : Ω) :
      t ^ R * (ν.weight ω * |S ω| ^ R) ≤
        (R.factorial : ℝ) * ν.weight ω *
          (Real.exp (t * S ω) + Real.exp (-t * S ω)) := by
    have h := even_pow_le_two_exps R hR (t * S ω)
    have habs : |t * S ω| ^ R = t ^ R * |S ω| ^ R := by
      rw [abs_mul, abs_of_nonneg ht.le, mul_pow]
    rw [← hR.pow_abs (t * S ω), habs] at h
    have hneg : -(t * S ω) = -t * S ω := by ring
    rw [hneg] at h
    calc
      t ^ R * (ν.weight ω * |S ω| ^ R) =
          ν.weight ω * (t ^ R * |S ω| ^ R) := by ring
      _ ≤ ν.weight ω *
          ((R.factorial : ℝ) *
            (Real.exp (t * S ω) + Real.exp (-t * S ω))) :=
        mul_le_mul_of_nonneg_left h (ν.nonneg ω)
      _ = _ := by ring
  have hsum : t ^ R * ex ν (fun ω => |S ω| ^ R) ≤
      (R.factorial : ℝ) *
        (ex ν (fun ω => Real.exp (t * S ω)) +
          ex ν (fun ω => Real.exp (-t * S ω))) := by
    calc
      t ^ R * ex ν (fun ω => |S ω| ^ R) =
          ∑ ω, t ^ R * (ν.weight ω * |S ω| ^ R) := by
        unfold ex
        rw [Finset.mul_sum]
      _ ≤ ∑ ω, (R.factorial : ℝ) * ν.weight ω *
          (Real.exp (t * S ω) + Real.exp (-t * S ω)) :=
        Finset.sum_le_sum (fun ω _ => hterm ω)
      _ = (R.factorial : ℝ) *
          (ex ν (fun ω => Real.exp (t * S ω)) +
            ex ν (fun ω => Real.exp (-t * S ω))) := by
        unfold ex
        simp only [mul_add, Finset.mul_sum, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro ω _
        ring
  have hbound : t ^ R * ex ν (fun ω => |S ω| ^ R) ≤
      2 * (R.factorial : ℝ) * B := by
    calc
      _ ≤ (R.factorial : ℝ) *
          (ex ν (fun ω => Real.exp (t * S ω)) +
            ex ν (fun ω => Real.exp (-t * S ω))) := hsum
      _ ≤ _ := by
        have hf : (0 : ℝ) ≤ R.factorial := by positivity
        nlinarith [mul_le_mul_of_nonneg_left (add_le_add hplus hminus) hf]
  exact (le_div_iff₀ htR).2 (by nlinarith [hbound])

/-- The exponential moment of a sum of functions of separate product-law
coordinates is the product of their individual exponential moments. -/
theorem iid_exp_sum_indexed (ν : Paper2.FiniteLaw Ω) (m : ℕ)
    (f : Fin m → Ω → ℝ) (t : ℝ) :
    ex (ν.iid m) (fun ws => Real.exp (t * ∑ i, f i (ws i))) =
      ∏ i : Fin m, ex ν (fun ω => Real.exp (t * f i ω)) := by
  classical
  unfold ex
  simp_rw [Finset.mul_sum, Real.exp_sum, Paper2.FiniteLaw.iid,
    ← Finset.prod_mul_distrib]
  have h := Finset.sum_prod_piFinset (ι := Fin m) (Finset.univ : Finset Ω)
    (fun i ω => ν.weight ω * Real.exp (t * f i ω))
  simpa using h

/-- Hoeffding's exponential-moment estimate for an indexed family of
centered indicators on independent coordinates. -/
theorem iid_centered_indicator_mgf (ν : Paper2.FiniteLaw Ω) (m : ℕ)
    (F : Fin m → Ω → Bool) (t : ℝ) :
    ex (ν.iid m) (fun ws => Real.exp (t * ∑ i : Fin m,
      ((if F i (ws i) then (1 : ℝ) else 0) - ν.prob (fun ω => F i ω)))) ≤
      Real.exp ((m : ℝ) * t ^ 2 / 8) := by
  classical
  let f : Fin m → Ω → ℝ := fun i ω =>
    (if F i ω then (1 : ℝ) else 0) - ν.prob (fun ω => F i ω)
  change ex (ν.iid m) (fun ws => Real.exp (t * ∑ i, f i (ws i))) ≤ _
  rw [iid_exp_sum_indexed]
  have hprod : (∏ i : Fin m, ex ν (fun ω => Real.exp (t * f i ω))) ≤
      ∏ _i : Fin m, Real.exp (t ^ 2 / 8) := by
    apply Finset.prod_le_prod
    · intro i _
      exact Finset.sum_nonneg (fun ω _ => mul_nonneg (ν.nonneg ω) (Real.exp_pos _).le)
    · intro i _
      convert ν.indicator_mgf_le (fun ω => F i ω) t using 1
      unfold ex f
      apply Finset.sum_congr rfl
      intro ω _
      cases h : F i ω <;> simp [h]
  calc
    _ ≤ ∏ _i : Fin m, Real.exp (t ^ 2 / 8) := hprod
    _ = Real.exp ((m : ℝ) * t ^ 2 / 8) := by
      simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      rw [← Real.exp_nat_mul]
      congr 1
      ring

private theorem factorial_1024_bound : Nat.factorial 1024 ≤ (512 * 513) ^ 512 := by
  have hfac : Nat.factorial 1024 =
      (∏ i ∈ Finset.range 512, (i + 1) * (1024 - i)) := by
    rw [Nat.factorial_eq_prod_range_add_one,
      show 1024 = 512 + 512 by omega, Finset.prod_range_add]
    have hreflect : (∏ i ∈ Finset.range 512, (512 + i + 1)) =
        ∏ i ∈ Finset.range 512, (1024 - i) := by
      rw [← Finset.prod_range_reflect (fun i => 512 + i + 1) 512]
      apply Finset.prod_congr rfl
      intro i hi
      have hii := Finset.mem_range.mp hi
      omega
    rw [hreflect, ← Finset.prod_mul_distrib]
  rw [hfac]
  calc
    _ ≤ ∏ _i ∈ Finset.range 512, (512 * 513) := by
      apply Finset.prod_le_prod
      · intro i hi
        omega
      · intro i hi
        have hii := Finset.mem_range.mp hi
        have h1 : (511 - i) + i = 511 := by omega
        have h2 : (512 - i) + i = 512 := by omega
        have h3 : (1024 - i) + i = 1024 := by omega
        have hp : 0 ≤ (511 - i) * (512 - i) := Nat.zero_le _
        nlinarith
    _ = _ := by simp [Finset.prod_const]

private theorem factorial_exp_1024_bound :
    (Nat.factorial 1024 : ℝ) * Real.exp 512 ≤ (1024 : ℝ) ^ 1024 := by
  have hfac : (Nat.factorial 1024 : ℝ) ≤ (262656 : ℝ) ^ 512 := by
    exact_mod_cast factorial_1024_bound
  have hexp : Real.exp 512 ≤ (3 : ℝ) ^ 512 := by
    rw [show (512 : ℝ) = (512 : ℕ) * (1 : ℝ) by norm_num,
      Real.exp_nat_mul]
    exact pow_le_pow_left₀ (Real.exp_pos _).le Real.exp_one_lt_three.le _
  calc
    (Nat.factorial 1024 : ℝ) * Real.exp 512 ≤
        (262656 : ℝ) ^ 512 * (3 : ℝ) ^ 512 := by gcongr
    _ = (787968 : ℝ) ^ 512 := by rw [← mul_pow]; norm_num
    _ ≤ (1048576 : ℝ) ^ 512 := by gcongr; norm_num
    _ = (1024 : ℝ) ^ 1024 := by
      rw [show (1048576 : ℝ) = (1024 : ℝ) ^ 2 by norm_num, ← pow_mul]

/-- The concrete 1024th-moment inequality used in Appendix H, for
independent (but not necessarily identically distributed) Boolean tests. -/
theorem iid_centered_indicator_moment_1024 (ν : Paper2.FiniteLaw Ω) (m : ℕ)
    (F : Fin m → Ω → Bool) :
    ex (ν.iid m) (fun ws => |∑ i : Fin m,
      ((if F i (ws i) then (1 : ℝ) else 0) - ν.prob (fun ω => F i ω))| ^ 1024) ≤
      2 * (((1024 : ℝ) * m) / 4) ^ 512 := by
  classical
  let S : (Fin m → Ω) → ℝ := fun ws => ∑ i : Fin m,
    ((if F i (ws i) then (1 : ℝ) else 0) - ν.prob (fun ω => F i ω))
  change ex (ν.iid m) (fun ws => |S ws| ^ 1024) ≤ _
  by_cases hm : m = 0
  · subst m
    simp [S, ex, Paper2.FiniteLaw.iid]
  have hmpos : 0 < (m : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hm)
  let t : ℝ := 64 / Real.sqrt m
  have hsqrt : 0 < Real.sqrt (m : ℝ) := Real.sqrt_pos.2 hmpos
  have ht : 0 < t := by dsimp [t]; positivity
  have hmt : (m : ℝ) * t ^ 2 / 8 = 512 := by
    dsimp [t]
    rw [div_pow, Real.sq_sqrt hmpos.le]
    field_simp
    ring
  have hplus : ex (ν.iid m) (fun ws => Real.exp (t * S ws)) ≤
      Real.exp 512 := by
    simpa [S, hmt] using iid_centered_indicator_mgf ν m F t
  have hminus : ex (ν.iid m) (fun ws => Real.exp (-t * S ws)) ≤
      Real.exp 512 := by
    simpa [S, neg_sq, hmt] using iid_centered_indicator_mgf ν m F (-t)
  have hraw := moment_le_of_two_sided_mgf (ν.iid m) S 1024
    (by norm_num : Even 1024) t (Real.exp 512) ht hplus hminus
  have ht1024 : 0 < t ^ 1024 := pow_pos ht _
  have htprod : t ^ 2 * (256 * (m : ℝ)) = (1024 : ℝ) ^ 2 := by
    nlinarith [hmt]
  have hpowequal : t ^ 1024 * (256 * (m : ℝ)) ^ 512 =
      (1024 : ℝ) ^ 1024 := by
    calc
      _ = (t ^ 2) ^ 512 * (256 * (m : ℝ)) ^ 512 := by
        rw [← pow_mul, show 2 * 512 = 1024 by norm_num]
      _ = (t ^ 2 * (256 * (m : ℝ))) ^ 512 := by simp only [mul_pow]
      _ = ((1024 : ℝ) ^ 2) ^ 512 := by rw [htprod]
      _ = (1024 : ℝ) ^ 1024 := by rw [← pow_mul]
  calc
    ex (ν.iid m) (fun ws => |S ws| ^ 1024) ≤
        2 * (Nat.factorial 1024 : ℝ) * Real.exp 512 / t ^ 1024 := hraw
    _ ≤ 2 * (1024 : ℝ) ^ 1024 / t ^ 1024 := by
      apply (div_le_div_iff_of_pos_right ht1024).2
      nlinarith [factorial_exp_1024_bound]
    _ = 2 * (((1024 : ℝ) * m) / 4) ^ 512 := by
      rw [show ((1024 : ℝ) * m) / 4 = 256 * m by ring]
      apply (div_eq_iff ht1024.ne').2
      rw [← hpowequal]
      ring


end CurrentAdditive.EvenMoment

#print axioms CurrentAdditive.EvenMoment.iid_exp_sum_indexed
#print axioms CurrentAdditive.EvenMoment.iid_centered_indicator_mgf
#print axioms CurrentAdditive.EvenMoment.iid_centered_indicator_moment_1024
