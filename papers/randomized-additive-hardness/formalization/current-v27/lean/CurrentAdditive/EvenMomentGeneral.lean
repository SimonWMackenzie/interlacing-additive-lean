import CurrentAdditive.EvenMoment

/-!
The all-even-order version of Appendix H's `det:even-moment` product-law bound.
This extends the frozen order-1024 proof without changing it.
-/

namespace CurrentAdditive.EvenMomentGeneral

open scoped BigOperators
open CurrentAdditive.EvenMoment

variable {Ω : Type*} [Fintype Ω]

/-- Pair the first and last factors in `(2n)!`. Each pair has product at
most `n(n+1)`. -/
private theorem factorial_even_le_pair_pow (n : ℕ) (hn : 0 < n) :
    Nat.factorial (2 * n) ≤ (n * (n + 1)) ^ n := by
  have hfac : Nat.factorial (2 * n) =
      ∏ i ∈ Finset.range n, (i + 1) * (2 * n - i) := by
    rw [Nat.factorial_eq_prod_range_add_one,
      show 2 * n = n + n by omega, Finset.prod_range_add]
    have hreflect : (∏ i ∈ Finset.range n, (n + i + 1)) =
        ∏ i ∈ Finset.range n, (2 * n - i) := by
      rw [← Finset.prod_range_reflect (fun i => n + i + 1) n]
      apply Finset.prod_congr rfl
      intro i hi
      have hii := Finset.mem_range.mp hi
      omega
    rw [hreflect, ← Finset.prod_mul_distrib]
    simp only [two_mul]
  rw [hfac]
  calc
    _ ≤ ∏ _i ∈ Finset.range n, (n * (n + 1)) := by
      apply Finset.prod_le_prod
      · intro i hi
        omega
      · intro i hi
        have hii := Finset.mem_range.mp hi
        have h1 : (n - 1 - i) + i = n - 1 := by omega
        have h2 : (n - i) + i = n := by omega
        have h3 : (2 * n - i) + i = 2 * n := by omega
        have hp : 0 ≤ (n - 1 - i) * (n - i) := Nat.zero_le _
        nlinarith
    _ = _ := by simp [Finset.prod_const]

/-- The exponential-series extraction cost is absorbed by the desired
moment constant at every even order at least eight. -/
private theorem factorial_exp_even_le_pow (n : ℕ) (hn : 4 ≤ n) :
    (Nat.factorial (2 * n) : ℝ) * Real.exp (n : ℝ) ≤
      ((2 * n : ℕ) : ℝ) ^ (2 * n) := by
  have hfac : (Nat.factorial (2 * n) : ℝ) ≤
      ((n : ℝ) * (n + 1)) ^ n := by
    exact_mod_cast factorial_even_le_pair_pow n (by omega)
  have hexp : Real.exp (n : ℝ) ≤ (3 : ℝ) ^ n := by
    rw [show (n : ℝ) = (n : ℕ) * (1 : ℝ) by simp, Real.exp_nat_mul]
    exact pow_le_pow_left₀ (Real.exp_pos _).le Real.exp_one_lt_three.le _
  have hnreal : (4 : ℝ) ≤ n := by exact_mod_cast hn
  have hfactor : 3 * (n : ℝ) * (n + 1) ≤ (2 * (n : ℝ)) ^ 2 := by
    nlinarith [mul_nonneg (show 0 ≤ (n : ℝ) by positivity)
      (show 0 ≤ (n : ℝ) - 3 by linarith)]
  calc
    (Nat.factorial (2 * n) : ℝ) * Real.exp (n : ℝ) ≤
        ((n : ℝ) * (n + 1)) ^ n * (3 : ℝ) ^ n := by gcongr
    _ = (3 * (n : ℝ) * (n + 1)) ^ n := by rw [← mul_pow]; ring
    _ ≤ ((2 * (n : ℝ)) ^ 2) ^ n := by gcongr
    _ = ((2 * n : ℕ) : ℝ) ^ (2 * n) := by
      rw [← pow_mul]
      norm_cast

/-- The exact Appendix H moment constant at an arbitrary even order `2n≥8`,
for indexed Boolean tests on an independent product law. -/
theorem iid_centered_indicator_moment_two_mul (ν : Paper2.FiniteLaw Ω)
    (m n : ℕ) (hn : 4 ≤ n) (F : Fin m → Ω → Bool) :
    ex (ν.iid m) (fun ws => |∑ i : Fin m,
      ((if F i (ws i) then (1 : ℝ) else 0) - ν.prob (fun ω => F i ω))| ^ (2 * n)) ≤
      2 * (((((2 * n : ℕ) : ℝ) * m) / 4)) ^ n := by
  classical
  let S : (Fin m → Ω) → ℝ := fun ws => ∑ i : Fin m,
    ((if F i (ws i) then (1 : ℝ) else 0) - ν.prob (fun ω => F i ω))
  change ex (ν.iid m) (fun ws => |S ws| ^ (2 * n)) ≤ _
  by_cases hm : m = 0
  · subst m
    have hn0 : n ≠ 0 := by omega
    simp [S, ex, Paper2.FiniteLaw.iid, hn0]
  have hmpos : 0 < (m : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hm)
  have hnpos : 0 < (n : ℝ) := Nat.cast_pos.mpr (by omega)
  let t : ℝ := Real.sqrt (8 * (n : ℝ) / (m : ℝ))
  have htarg : 0 < 8 * (n : ℝ) / (m : ℝ) := by positivity
  have ht : 0 < t := by dsimp [t]; exact Real.sqrt_pos.2 htarg
  have ht2 : t ^ 2 = 8 * (n : ℝ) / (m : ℝ) := by
    dsimp [t]
    exact Real.sq_sqrt htarg.le
  have hmt : (m : ℝ) * t ^ 2 / 8 = (n : ℝ) := by
    rw [ht2]
    field_simp
  have hplus : ex (ν.iid m) (fun ws => Real.exp (t * S ws)) ≤
      Real.exp (n : ℝ) := by
    simpa [S, hmt] using iid_centered_indicator_mgf ν m F t
  have hminus : ex (ν.iid m) (fun ws => Real.exp (-t * S ws)) ≤
      Real.exp (n : ℝ) := by
    simpa [S, neg_sq, hmt] using iid_centered_indicator_mgf ν m F (-t)
  have hraw := moment_le_of_two_sided_mgf (ν.iid m) S (2 * n)
    (by simp : Even (2 * n)) t (Real.exp (n : ℝ)) ht hplus hminus
  have htpow : 0 < t ^ (2 * n) := pow_pos ht _
  let base : ℝ := (((2 * n : ℕ) : ℝ) * m) / 4
  have htprod : t ^ 2 * base = (((2 * n : ℕ) : ℝ)) ^ 2 := by
    dsimp [base]
    rw [ht2]
    push_cast
    field_simp
    ring
  have hpowequal : t ^ (2 * n) * base ^ n =
      (((2 * n : ℕ) : ℝ)) ^ (2 * n) := by
    calc
      _ = (t ^ 2) ^ n * base ^ n := by rw [← pow_mul]
      _ = (t ^ 2 * base) ^ n := by simp only [mul_pow]
      _ = ((((2 * n : ℕ) : ℝ)) ^ 2) ^ n := by rw [htprod]
      _ = (((2 * n : ℕ) : ℝ)) ^ (2 * n) := by rw [← pow_mul]
  calc
    ex (ν.iid m) (fun ws => |S ws| ^ (2 * n)) ≤
        2 * (Nat.factorial (2 * n) : ℝ) * Real.exp (n : ℝ) /
          t ^ (2 * n) := hraw
    _ ≤ 2 * (((2 * n : ℕ) : ℝ)) ^ (2 * n) / t ^ (2 * n) := by
      apply (div_le_div_iff_of_pos_right htpow).2
      nlinarith [factorial_exp_even_le_pow n hn]
    _ = 2 * base ^ n := by
      apply (div_eq_iff htpow.ne').2
      rw [← hpowequal]
      ring

/-- The manuscript's all-even-order product-law inequality with a natural
half-order exponent. -/
theorem iid_centered_indicator_moment_even (ν : Paper2.FiniteLaw Ω)
    (m R : ℕ) (hEven : Even R) (hR : 8 ≤ R)
    (F : Fin m → Ω → Bool) :
    ex (ν.iid m) (fun ws => |∑ i : Fin m,
      ((if F i (ws i) then (1 : ℝ) else 0) - ν.prob (fun ω => F i ω))| ^ R) ≤
      2 * (((R : ℝ) * m) / 4) ^ (R / 2) := by
  obtain ⟨n, hn⟩ := hEven
  have hRn : R = 2 * n := by omega
  have hn4 : 4 ≤ n := by omega
  rw [hRn, show (2 * n) / 2 = n by omega]
  exact iid_centered_indicator_moment_two_mul ν m n hn4 F

/-- The same theorem in the real-exponent form used by the manuscript's
Hölder and exceptional-coordinate count. -/
theorem iid_centered_indicator_moment_even_real (ν : Paper2.FiniteLaw Ω)
    (m R : ℕ) (hEven : Even R) (hR : 8 ≤ R)
    (F : Fin m → Ω → Bool) :
    ex (ν.iid m) (fun ws => |∑ i : Fin m,
      ((if F i (ws i) then (1 : ℝ) else 0) - ν.prob (fun ω => F i ω))| ^ R) ≤
      2 * (((R : ℝ) * m) / 4) ^ ((R : ℝ) / 2) := by
  have hpow : ((R : ℝ) / 2) = ((R / 2 : ℕ) : ℝ) := by
    obtain ⟨n, hn⟩ := hEven
    have hRn : R = 2 * n := by omega
    rw [hRn, show (2 * n) / 2 = n by omega]
    push_cast
    ring
  rw [hpow, Real.rpow_natCast]
  exact iid_centered_indicator_moment_even ν m R hEven hR F

#print axioms iid_centered_indicator_moment_two_mul
#print axioms iid_centered_indicator_moment_even
#print axioms iid_centered_indicator_moment_even_real

end CurrentAdditive.EvenMomentGeneral
