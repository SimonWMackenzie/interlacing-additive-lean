import CurrentAdditive.DeterministicParameters
import CurrentAdditive.IntegerPowerTests

/-!
Analytic bridge under construction: identify the existing real-valued
`conditioningExceptionCount` with the integer-power computation from v35.
No declaration here is meant to be admitted before it compiles without holes.
-/

namespace CurrentAdditive.PublicScheduleExactCount

private noncomputable def v (b : ℕ) : ℝ := (2 : ℝ) ^ (-(b : ℝ))
private noncomputable def alpha (b : ℕ) : ℝ := (2 : ℝ) ^ (-(30 : ℝ) - (b : ℝ) / 256)

private theorem v_pos (b : ℕ) : 0 < v b := by unfold v; positivity
private theorem alpha_pos (b : ℕ) : 0 < alpha b := by unfold alpha; positivity

private theorem dyadic_epsilon (b : ℕ) (τ : ℝ) :
    CurrentAdditive.conditioningEpsilon (v b) τ = min τ (alpha b) := by
  have hv : (v b) ^ ((4 : ℝ) / 1024) =
      (2 : ℝ) ^ (-(b : ℝ) / 256) := by
    unfold v
    rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    congr 1
    ring
  have hc : (2 : ℝ) ^ (-(20 : ℝ)) / 1024 =
      (2 : ℝ) ^ (-(30 : ℝ)) := by
    norm_num [Real.rpow_neg, Real.rpow_natCast]
  unfold CurrentAdditive.conditioningEpsilon alpha
  rw [hc, hv, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
  congr 1
  ring

private theorem v_inv (b : ℕ) :
    (v b) ^ (-(1 : ℝ)) = (2 : ℝ) ^ (b : ℝ) := by
  unfold v
  rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
  congr 1
  ring

private theorem alpha_inv_1024 (b : ℕ) :
    (alpha b) ^ (-(1024 : ℝ)) =
      (2 : ℝ) ^ ((30720 : ℝ) + 4 * (b : ℝ)) := by
  unfold alpha
  rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
  congr 1
  ring

private theorem base_pow_512 :
    (1024 : ℝ) ^ 512 = (2 : ℝ) ^ (5120 : ℕ) := by
  rw [show (1024 : ℝ) = 2 ^ (10 : ℕ) by norm_num, ← pow_mul]

private theorem inner_pow_512 (v ε : ℝ) (hv : 0 < v) (hε : 0 < ε) :
    ((1024 : ℝ) * ε ^ (-(2 : ℝ)) * v ^ (-(2 / (1024 : ℝ)))) ^ 512 =
      (1024 : ℝ) ^ 512 * ε ^ (-(1024 : ℝ)) * v ^ (-(1 : ℝ)) := by
  have hεpow : (ε ^ (-(2 : ℝ))) ^ 512 = ε ^ (-(1024 : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hε.le]
    congr 1
    ring
  have hvpow : (v ^ (-(2 / (1024 : ℝ)))) ^ 512 = v ^ (-(1 : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hv.le]
    congr 1
    ring
  rw [mul_pow, mul_pow, hεpow, hvpow]

private noncomputable def inner (b : ℕ) (τ : ℝ) : ℝ :=
  1024 * (CurrentAdditive.conditioningEpsilon (v b) τ) ^ (-(2 : ℝ)) *
    (v b) ^ (-(2 / (1024 : ℝ)))

private theorem inner_pos (b : ℕ) (τ : ℝ) (hτ : 0 < τ) :
    0 < inner b τ := by
  unfold inner
  have hε := CurrentAdditive.conditioningEpsilon_pos (v_pos b) hτ
  exact mul_pos (mul_pos (by norm_num) (Real.rpow_pos_of_pos hε _))
    (Real.rpow_pos_of_pos (v_pos b) _)

private theorem inner_dyadic_pow_512 (b : ℕ) (τ : ℝ) (hτ : 0 < τ) :
    (inner b τ) ^ 512 =
      (2 : ℝ) ^ ((5120 : ℝ) + (b : ℝ)) *
        (min τ (alpha b)) ^ (-(1024 : ℝ)) := by
  have hε := CurrentAdditive.conditioningEpsilon_pos (v_pos b) hτ
  unfold inner
  rw [inner_pow_512 _ _ (v_pos b) hε, base_pow_512,
    v_inv, dyadic_epsilon]
  calc
    (2 : ℝ) ^ 5120 * (min τ (alpha b)) ^ (-(1024 : ℝ)) *
        (2 : ℝ) ^ (b : ℝ) =
      ((2 : ℝ) ^ 5120 * (2 : ℝ) ^ (b : ℝ)) *
        (min τ (alpha b)) ^ (-(1024 : ℝ)) := by ring
    _ = (2 : ℝ) ^ ((5120 : ℝ) + (b : ℝ)) *
          (min τ (alpha b)) ^ (-(1024 : ℝ)) := by
      simp only [← Real.rpow_natCast]
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      norm_num

private theorem alpha_term (b : ℕ) :
    (2 : ℝ) ^ ((5120 : ℝ) + (b : ℝ)) *
      (alpha b) ^ (-(1024 : ℝ)) =
      (2 : ℝ) ^ ((35840 : ℝ) + 5 * (b : ℝ)) := by
  rw [alpha_inv_1024, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
  congr 1
  ring

private theorem inner_dyadic_pow_max (b : ℕ) (τ : ℝ) (hτ : 0 < τ) :
    (inner b τ) ^ 512 =
      max ((2 : ℝ) ^ ((5120 : ℝ) + (b : ℝ)) *
          τ ^ (-(1024 : ℝ)))
        ((2 : ℝ) ^ ((35840 : ℝ) + 5 * (b : ℝ))) := by
  rw [inner_dyadic_pow_512 b τ hτ]
  rcases le_total τ (alpha b) with h | h
  · rw [min_eq_left h]
    have hpow := Real.rpow_le_rpow_of_nonpos hτ h
      (by norm_num : -(1024 : ℝ) ≤ 0)
    have hbase : 0 ≤ (2 : ℝ) ^ ((5120 : ℝ) + (b : ℝ)) := by positivity
    have hle := mul_le_mul_of_nonneg_left hpow hbase
    have hle' : (2 : ℝ) ^ ((35840 : ℝ) + 5 * (b : ℝ)) ≤
        (2 : ℝ) ^ ((5120 : ℝ) + (b : ℝ)) * τ ^ (-(1024 : ℝ)) := by
      rw [← alpha_term b]
      exact hle
    rw [max_eq_left hle']
  · rw [min_eq_right h]
    have hpow := Real.rpow_le_rpow_of_nonpos (alpha_pos b) h
      (by norm_num : -(1024 : ℝ) ≤ 0)
    have hbase : 0 ≤ (2 : ℝ) ^ ((5120 : ℝ) + (b : ℝ)) := by positivity
    have hle := mul_le_mul_of_nonneg_left hpow hbase
    have hle' : (2 : ℝ) ^ ((5120 : ℝ) + (b : ℝ)) * τ ^ (-(1024 : ℝ)) ≤
        (2 : ℝ) ^ ((35840 : ℝ) + 5 * (b : ℝ)) := by
      rw [← alpha_term b]
      exact hle
    rw [max_eq_right hle', ← alpha_term b]

private theorem source_count_eq_ceil (b : ℕ) (τ : ℝ) :
    CurrentAdditive.conditioningExceptionCount (v b) τ =
      8 * ⌈inner b τ⌉₊ := by
  rfl

private theorem two_pow_cast_exp (a b : ℕ) :
    (2 : ℝ) ^ ((a : ℝ) + (b : ℝ)) =
      ((2 ^ (a + b) : ℕ) : ℝ) := by
  simp only [Nat.cast_pow, Nat.cast_ofNat, Nat.cast_add,
    ← Real.rpow_natCast]

private theorem tau_inv_pow (p q : ℕ) (hp : 0 < p) (hq : 0 < q) :
    (((p : ℝ) / q) ^ (-(1024 : ℝ))) =
      (q : ℝ) ^ 1024 / (p : ℝ) ^ 1024 := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  rw [Real.rpow_neg (by positivity : (0 : ℝ) ≤ (p : ℝ) / q)]
  rw [Real.div_rpow hpR.le hqR.le]
  rw [inv_div]
  congr 1 <;> exact Real.rpow_natCast _ 1024

set_option maxRecDepth 4096 in
private theorem inner_pow_integer_iff (b p q t : ℕ)
    (hp : 0 < p) (hq : 0 < q) :
    (inner b ((p : ℝ) / q)) ^ 512 ≤ (t : ℝ) ^ 512 ↔
      2 ^ (5120 + b) * q ^ 1024 ≤ p ^ 1024 * t ^ 512 ∧
      2 ^ (35840 + 5 * b) ≤ t ^ 512 := by
  have hτ : (0 : ℝ) < (p : ℝ) / q := by exact div_pos (by exact_mod_cast hp) (by exact_mod_cast hq)
  rw [inner_dyadic_pow_max b _ hτ, max_le_iff, tau_inv_pow p q hp hq]
  have hpR : (0 : ℝ) < (p : ℝ) ^ 1024 := by
    have hh : (0 : ℝ) < p := by exact_mod_cast hp
    positivity
  have hb1 : (2 : ℝ) ^ ((5120 : ℝ) + (b : ℝ)) =
      ((2 ^ (5120 + b) : ℕ) : ℝ) := two_pow_cast_exp 5120 b
  rw [hb1]
  have hb2 : (2 : ℝ) ^ ((35840 : ℝ) + 5 * (b : ℝ)) =
      ((2 ^ (35840 + 5 * b) : ℕ) : ℝ) := by
    convert two_pow_cast_exp 35840 (5 * b) using 1 <;> push_cast <;> ring
  rw [hb2]
  have hrewrite : ((2 ^ (5120 + b) : ℕ) : ℝ) *
      ((q : ℝ) ^ 1024 / (p : ℝ) ^ 1024) =
      (((2 ^ (5120 + b) : ℕ) : ℝ) * (q : ℝ) ^ 1024) /
        (p : ℝ) ^ 1024 := by ring
  rw [hrewrite]
  constructor
  · intro h
    constructor
    · have h₁ := (div_le_iff₀ hpR).mp h.1
      have hh : ((2 ^ (5120 + b) * q ^ 1024 : ℕ) : ℝ) ≤
          ((p ^ 1024 * t ^ 512 : ℕ) : ℝ) := by
        convert h₁ using 1 <;> norm_cast <;> ring
      exact Nat.cast_le.mp hh
    · have hh : ((2 ^ (35840 + 5 * b) : ℕ) : ℝ) ≤
          ((t ^ 512 : ℕ) : ℝ) := by simpa only [Nat.cast_pow] using h.2
      exact Nat.cast_le.mp hh
  · rintro ⟨h₁, h₂⟩
    constructor
    · apply (div_le_iff₀ hpR).mpr
      have hh : ((2 ^ (5120 + b) * q ^ 1024 : ℕ) : ℝ) ≤
          ((p ^ 1024 * t ^ 512 : ℕ) : ℝ) := Nat.cast_le.mpr h₁
      calc
        ((2 ^ (5120 + b) : ℕ) : ℝ) * (q : ℝ) ^ 1024 =
            ((2 ^ (5120 + b) * q ^ 1024 : ℕ) : ℝ) := by
          simp only [Nat.cast_mul, Nat.cast_pow]
        _ ≤ ((p ^ 1024 * t ^ 512 : ℕ) : ℝ) := hh
        _ = (t : ℝ) ^ 512 * (p : ℝ) ^ 1024 := by
          simp only [Nat.cast_mul, Nat.cast_pow, mul_comm]
    · have hh : ((2 ^ (35840 + 5 * b) : ℕ) : ℝ) ≤
          ((t ^ 512 : ℕ) : ℝ) := Nat.cast_le.mpr h₂
      simpa only [Nat.cast_pow] using hh

theorem source_count_test_iff (b p q t : ℕ)
    (hp : 0 < p) (hq : 0 < q) :
    CurrentAdditive.conditioningExceptionCount (v b) ((p : ℝ) / q) ≤ 8 * t ↔
      2 ^ (5120 + b) * q ^ 1024 ≤ p ^ 1024 * t ^ 512 ∧
      2 ^ (35840 + 5 * b) ≤ t ^ 512 := by
  rw [source_count_eq_ceil]
  have hmul : 8 * ⌈inner b ((p : ℝ) / q)⌉₊ ≤ 8 * t ↔
      ⌈inner b ((p : ℝ) / q)⌉₊ ≤ t := by omega
  rw [hmul, Nat.ceil_le]
  have hpow : inner b ((p : ℝ) / q) ≤ (t : ℝ) ↔
      (inner b ((p : ℝ) / q)) ^ 512 ≤ (t : ℝ) ^ 512 := by
    exact (pow_le_pow_iff_left₀
      (inner_pos b _ (div_pos (by exact_mod_cast hp) (by exact_mod_cast hq))).le
      (Nat.cast_nonneg t) (by decide)).symm
  rw [hpow, inner_pow_integer_iff b p q t hp hq]

theorem source_count_eq_integer_witness (b p q : ℕ)
    (hp : 0 < p) (hq : 0 < q) :
    CurrentAdditive.conditioningExceptionCount (v b) ((p : ℝ) / q) =
      8 * CurrentAdditive.PublicScheduleIntegerPower.firstPowerWitness b p q := by
  let w := CurrentAdditive.PublicScheduleIntegerPower.firstPowerWitness b p q
  have hiff (t : ℕ) : ⌈inner b ((p : ℝ) / q)⌉₊ ≤ t ↔ w ≤ t := by
    have hs := source_count_test_iff b p q t hp hq
    rw [source_count_eq_ceil] at hs
    have hm : 8 * ⌈inner b ((p : ℝ) / q)⌉₊ ≤ 8 * t ↔
        ⌈inner b ((p : ℝ) / q)⌉₊ ≤ t := by omega
    exact (hm.symm.trans hs).trans
      (CurrentAdditive.PublicScheduleIntegerPower.firstPowerWitness_spec b p q t hp hq).symm
  have heq : ⌈inner b ((p : ℝ) / q)⌉₊ = w :=
    le_antisymm ((hiff w).mpr le_rfl) ((hiff _).mp le_rfl)
  rw [source_count_eq_ceil, heq]

#print axioms inner_pow_512
#print axioms dyadic_epsilon
#print axioms alpha_inv_1024
#print axioms inner_dyadic_pow_512
#print axioms inner_dyadic_pow_max
#print axioms inner_pow_integer_iff
#print axioms source_count_test_iff
#print axioms source_count_eq_integer_witness

end CurrentAdditive.PublicScheduleExactCount
