import Paper2.YaoEvents
import Mathlib.Analysis.MeanInequalities

/-!
# The large projection in the alternating lower bound

Frozen source: v12 Section 7, `yao:projection-product` and
`yao:large-projection`. We use the exponential tangent inequality, an
equivalent arithmetic--geometric-mean argument, to keep the strict numerical
surplus explicit without introducing real powers with fractional exponents.
-/

namespace Paper2.YaoLowerBound

open scoped BigOperators

/-- A product at least `3/2` forces a sum exceeding the number of terms
by more than `1/4`. The strict surplus follows from `exp(1/4) <= 4/3`.
This is the exponential-tangent form of the AM--GM step. -/
theorem sum_gt_card_add_quarter {q : ℕ} (y : Fin q → ℝ)
    (hy : ∀ g, 0 ≤ y g) (hprod : (3 / 2 : ℝ) ≤ ∏ g, y g) :
    (q : ℝ) + 1 / 4 < ∑ g, y g := by
  have htangent : (∏ g, y g) ≤ Real.exp (∑ g, (y g - 1)) := by
    rw [Real.exp_sum]
    exact Finset.prod_le_prod (fun g _ => hy g)
      (fun g _ => by simpa using Real.add_one_le_exp (y g - 1))
  have hquarter : Real.exp (1 / 4 : ℝ) ≤ 4 / 3 := by
    convert Real.exp_bound_div_one_sub_of_interval
      (x := (1 / 4 : ℝ)) (by norm_num) (by norm_num) using 1
    norm_num
  by_contra h
  have hsum : (∑ g, (y g - 1)) ≤ (1 / 4 : ℝ) := by
    simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, mul_one]
    linarith
  have hupper := Real.exp_le_exp.mpr hsum
  linarith

/-- Average the preceding strict inequality across a nonempty row set.
One coordinate retains the strict surplus; no integrality is used here. -/
theorem exists_large_scaled_coordinate {K q : ℕ} (hK : 0 < K) (hq : 0 < q)
    (y : Fin K → Fin q → ℝ) (hy : ∀ i g, 0 ≤ y i g)
    (hprod : ∀ i, (3 / 2 : ℝ) ≤ ∏ g, y i g) :
    ∃ g, (K : ℝ) + (K : ℝ) / (4 * q) < ∑ i, y i g := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hKne : (Finset.univ : Finset (Fin K)).Nonempty :=
    ⟨⟨0, hK⟩, Finset.mem_univ _⟩
  have hrows : (K : ℝ) * ((q : ℝ) + 1 / 4) < ∑ i, ∑ g, y i g := by
    have hs := Finset.sum_lt_sum_of_nonempty hKne
      (fun i _ => sum_gt_card_add_quarter (y i) (hy i) (hprod i))
    simpa [mul_add] using hs
  by_contra h
  push Not at h
  have hcols : (∑ g, ∑ i, y i g) ≤
      (q : ℝ) * ((K : ℝ) + (K : ℝ) / (4 * q)) := by
    simpa [mul_add] using Finset.sum_le_sum (s := (Finset.univ : Finset (Fin q)))
      (fun g _ => h g)
  rw [Finset.sum_comm] at hcols
  have heq : (q : ℝ) * ((K : ℝ) + (K : ℝ) / (4 * q)) =
      (K : ℝ) * ((q : ℝ) + 1 / 4) := by
    field_simp
  rw [heq] at hcols
  linarith

/-- The source's `S=2^(s-1)` and `q=s/2` turn its product threshold into
the constant `3/2` after scaling every factor by four. -/
theorem scaled_product_threshold (s q : ℕ) (hs : 1 ≤ s) (hsq : s = 2 * q) :
    (4 : ℝ) ^ q * (3 / (4 * (2 : ℝ) ^ (s - 1))) = 3 / 2 := by
  have he : (4 : ℝ) ^ q = (2 : ℝ) ^ (s - 1) * 2 := by
    calc
      (4 : ℝ) ^ q = ((2 : ℝ) ^ 2) ^ q := by norm_num
      _ = (2 : ℝ) ^ (2 * q) := (pow_mul _ _ _).symm
      _ = (2 : ℝ) ^ s := by rw [hsq]
      _ = (2 : ℝ) ^ ((s - 1) + 1) := by rw [Nat.sub_add_cancel hs]
      _ = (2 : ℝ) ^ (s - 1) * 2 := by rw [pow_succ]
  rw [he]
  have hp : (2 : ℝ) ^ (s - 1) ≠ 0 := pow_ne_zero _ (by norm_num)
  field_simp
  ring

/-- The strict numerical surplus in `yao:large-projection`, for arbitrary
nonnegative integer projection sizes satisfying the product lower bound. -/
theorem exists_large_projection_real (t b : ℕ) (ht : 1 ≤ t)
    (x : Fin (2 ^ t * 2 ^ t) → Fin (2 ^ (t - 1)) → ℕ)
    (hprod : ∀ i, (3 : ℝ) / (4 * (2 : ℝ) ^ (2 ^ t - 1)) ≤
      ∏ g, (x i g : ℝ) / (2 : ℝ) ^ b) :
    ∃ g, (2 : ℝ) ^ t * (2 : ℝ) ^ t * (2 : ℝ) ^ b / 4 +
      (2 : ℝ) ^ t * (2 : ℝ) ^ b / 8 < (∑ i, x i g : ℕ) := by
  let s : ℕ := 2 ^ t
  let q : ℕ := 2 ^ (t - 1)
  let H : ℝ := 2 ^ b
  have hs : 1 ≤ s := Nat.one_le_pow _ _ (by omega)
  have hq : 0 < q := pow_pos (by omega) _
  have hsq : s = 2 * q := by
    dsimp [s, q]
    conv_lhs => rw [← Nat.sub_add_cancel ht]
    rw [pow_succ, Nat.mul_comm]
  have hH : 0 < H := pow_pos (by norm_num) _
  have hsqR : (s : ℝ) = 2 * (q : ℝ) := by exact_mod_cast hsq
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hp (i : Fin (s * s)) : (3 / 2 : ℝ) ≤
      ∏ g : Fin q, 4 * ((x i g : ℝ) / H) := by
    rw [Finset.prod_mul_distrib]
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rw [← scaled_product_threshold s q hs hsq]
    exact mul_le_mul_of_nonneg_left (hprod i) (by positivity)
  obtain ⟨g, hg⟩ := exists_large_scaled_coordinate
    (K := s * s) (q := q) (by positivity) hq
    (fun i g => 4 * ((x i g : ℝ) / H)) (by intros; positivity) hp
  have hgsum : ((s * s : ℕ) : ℝ) + ((s * s : ℕ) : ℝ) / (4 * (q : ℝ)) <
      4 * ((∑ i, x i g : ℕ) : ℝ) / H := by
    simpa only [← Finset.mul_sum, ← Finset.sum_div, ← Nat.cast_sum, mul_div_assoc] using hg
  have heq : ((s * s : ℕ) : ℝ) + ((s * s : ℕ) : ℝ) / (4 * (q : ℝ)) =
      (s : ℝ) * (s : ℝ) + (s : ℝ) / 2 := by
    push_cast
    field_simp
    nlinarith
  rw [heq] at hgsum
  have hmul := (lt_div_iff₀ hH).mp hgsum
  refine ⟨g, ?_⟩
  change (2 : ℝ) ^ t * (2 : ℝ) ^ t * H / 4 +
    (2 : ℝ) ^ t * H / 8 < ((∑ i, x i g : ℕ) : ℝ)
  have hsR : (s : ℝ) = (2 : ℝ) ^ t := by simp [s]
  rw [hsR] at hmul
  nlinarith

/-- The exact integer threshold required by the payload event. -/
theorem exists_large_projection (t b : ℕ) (ht : 4 ≤ t)
    (x : Fin (2 ^ t * 2 ^ t) → Fin (2 ^ (t - 1)) → ℕ)
    (hprod : ∀ i, (3 : ℝ) / (4 * (2 : ℝ) ^ (2 ^ t - 1)) ≤
      ∏ g, (x i g : ℝ) / (2 : ℝ) ^ b) :
    ∃ g, Paper2.Yao.payloadMinimum b t ≤ ∑ i, x i g := by
  obtain ⟨g, hg⟩ := exists_large_projection_real t b (by omega) x hprod
  refine ⟨g, ?_⟩
  rw [Paper2.Yao.payloadMinimum_source b t ht]
  have hfirst : (((2 ^ (2 * t) * 2 ^ b) / 4 : ℕ) : ℝ) ≤
      (2 : ℝ) ^ t * (2 : ℝ) ^ t * (2 : ℝ) ^ b / 4 := by
    have h : (((2 ^ (2 * t) * 2 ^ b) / 4 : ℕ) : ℝ) ≤
        ((2 ^ (2 * t) * 2 ^ b : ℕ) : ℝ) / (4 : ℝ) := Nat.cast_div_le
    simpa [Nat.cast_mul, Nat.cast_pow, two_mul, pow_add] using h
  have hsecond : (((2 ^ t * 2 ^ b) / 8 : ℕ) : ℝ) ≤
      (2 : ℝ) ^ t * (2 : ℝ) ^ b / 8 := by
    have h : (((2 ^ t * 2 ^ b) / 8 : ℕ) : ℝ) ≤
        ((2 ^ t * 2 ^ b : ℕ) : ℝ) / (8 : ℝ) := Nat.cast_div_le
    simpa using h
  have hlt : (((2 ^ (2 * t) * 2 ^ b) / 4 + (2 ^ t * 2 ^ b) / 8 : ℕ) : ℝ) <
      ((∑ i, x i g : ℕ) : ℝ) := by
    rw [Nat.cast_add]
    linarith
  exact Nat.succ_le_of_lt (by exact_mod_cast hlt)

end Paper2.YaoLowerBound
