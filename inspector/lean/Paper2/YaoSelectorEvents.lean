import Paper2.YaoEvents

/-!
# Independent selector samples and all product-set tests

Frozen Paper 2 v12, T29(i), `yao:rectangle-event` and `yao:counts`.
All selector labels, including repeats, are counted separately. The family
of tested product sets includes empty factors and is independent of the
sample, so its simultaneous event permits a later adversarial choice.
-/

namespace Paper2.Yao

open scoped BigOperators

noncomputable def selectorLaw (q H : ℕ) [NeZero H] : FiniteLaw (Fin q → Fin H) :=
  FiniteLaw.pi (fun _ : Fin q => FiniteLaw.uniform (Fin H))

def selectorRectangle {q H : ℕ} (J : Fin q → Finset (Fin H)) (c : Fin q → Fin H) : Prop :=
  ∀ g, c g ∈ J g

noncomputable def selectorVolume {q H : ℕ} (J : Fin q → Finset (Fin H)) : ℝ :=
  ∏ g, (J g).card / (H : ℝ)

noncomputable def selectorEmpirical {q H : ℕ} (samples : ℕ)
    (C : Fin samples → (Fin q → Fin H)) (J : Fin q → Finset (Fin H)) : ℝ := by
  classical
  exact ((Finset.univ.filter (fun z => selectorRectangle J (C z))).card : ℝ) / samples

/-- The pointwise good event used by the NO-instance extraction. -/
def selectorGood (q H S samples : ℕ) (C : Fin samples → (Fin q → Fin H)) : Prop :=
  ∀ J : Fin q → Finset (Fin H),
    selectorEmpirical samples C J ≤ selectorVolume J + 1 / (4 * (S : ℝ))

def selectorSampleCount (q H S lambda : ℕ) : ℕ := 8 * S ^ 2 * (q * H + lambda)

theorem selector_rectangle_probability (q H : ℕ) [NeZero H]
    (J : Fin q → Finset (Fin H)) :
    (selectorLaw q H).prob (selectorRectangle J) = selectorVolume J := by
  unfold selectorLaw selectorRectangle
  rw [FiniteLaw.pi_prob_coordinatewise]
  apply Finset.prod_congr rfl
  intro g _
  simpa only [Fintype.card_fin] using FiniteLaw.uniform_prob_finset (J g)

theorem selector_test_count (q H : ℕ) :
    Fintype.card (Fin q → Finset (Fin H)) = 2 ^ (q * H) := by
  rw [Fintype.card_fun, Fintype.card_finset, Fintype.card_fin, Fintype.card_fin,
    ← pow_mul, Nat.mul_comm]

theorem selectorSampleCount_positive (q H S lambda : ℕ)
    (hS : 0 < S) (hlambda : 0 < lambda) : 0 < selectorSampleCount q H S lambda := by
  unfold selectorSampleCount
  positivity

/-- A retained label set lies inside the rectangle formed by any factors
that contain its sampled coordinates. This is the literal label count. -/
theorem selectorEmpirical_of_containment {q H samples : ℕ}
    (C : Fin samples → (Fin q → Fin H)) (J : Fin q → Finset (Fin H))
    (Z : Finset (Fin samples)) (hZ : ∀ z ∈ Z, selectorRectangle J (C z)) :
    (Z.card : ℝ) / samples ≤ selectorEmpirical samples C J := by
  classical
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg samples)
  apply Nat.cast_le.mpr
  exact Finset.card_le_card (by
    intro z hz
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ z, hZ z hz⟩)

/-- This is the projection product bound used after choosing a largest
early-strategy class. Only the sample good event is used; no independence
is assumed of the retained class or its factors. -/
theorem selectorGood_large_class {q H S samples : ℕ}
    (C : Fin samples → (Fin q → Fin H)) (hgood : selectorGood q H S samples C)
    (hsamples : 0 < samples) (hS : 0 < S)
    (Z : Finset (Fin samples)) (hsize : samples ≤ S * Z.card)
    (J : Fin q → Finset (Fin H)) (hZ : ∀ z ∈ Z, selectorRectangle J (C z)) :
    3 / (4 * (S : ℝ)) ≤ selectorVolume J := by
  have hn : (0 : ℝ) < samples := Nat.cast_pos.mpr hsamples
  have hs : (0 : ℝ) < S := Nat.cast_pos.mpr hS
  have hcount : (samples : ℝ) ≤ S * Z.card := by exact_mod_cast hsize
  have hfrac : 1 / (S : ℝ) ≤ (Z.card : ℝ) / samples := by
    apply (div_le_div_iff₀ hs hn).mpr
    simpa only [one_mul, mul_one, mul_comm] using hcount
  have hb := (hfrac.trans (selectorEmpirical_of_containment C J Z hZ)).trans (hgood J)
  field_simp at hb ⊢
  nlinarith

/-- The chosen sample count makes the Hoeffding exponent exactly the
number of rectangle-description bits plus the failure parameter. -/
theorem selector_sample_exponent (q H S lambda : ℕ) (hS : 0 < S) :
    -2 * (selectorSampleCount q H S lambda : ℝ) * (1 / (4 * (S : ℝ))) ^ 2 =
      -((q * H + lambda : ℕ) : ℝ) := by
  have hs : (S : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hS)
  unfold selectorSampleCount
  push_cast
  field_simp
  ring

/-- The elementary numerical last step of the rectangle union bound.
It only uses `2 ≤ exp 1`, not a numerical approximation to logarithms. -/
theorem selector_exp_union_bound (k lambda : ℕ) :
    (2 : ℝ) ^ k * Real.exp (-((k + lambda : ℕ) : ℝ)) ≤ (1 / 2 : ℝ) ^ lambda := by
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by
    convert Real.add_one_le_exp (1 : ℝ) using 1
    norm_num
  have he : Real.exp (-1) ≤ (1 / 2 : ℝ) := by
    rw [Real.exp_neg]
    simpa only [one_div] using one_div_le_one_div_of_le (by norm_num) htwo
  have hp : Real.exp (-((k + lambda : ℕ) : ℝ)) = (Real.exp (-1)) ^ (k + lambda) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rw [hp]
  apply (mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (Real.exp_nonneg _) he _) (by positivity)).trans
  exact dyadic_capacity_deficit k (k + lambda) lambda le_rfl

end Paper2.Yao
