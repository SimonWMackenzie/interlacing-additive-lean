import Paper2.FiniteSampling

/-!
The concentration step of v27 `det:near-full`: a retained event on which
the missed-event count vanishes has small mass once its centered second
moment is at most its mean.  The separate pairwise-independence calculation
for the actual generated source is still needed to supply that moment bound.
-/

namespace CurrentAdditive.PairwiseMissedEvents

open Paper2
attribute [local instance] Classical.propDecidable

variable {Ω : Type*} [Fintype Ω]

noncomputable def expectation (ν : FiniteLaw Ω) (X : Ω → ℝ) : ℝ :=
  ∑ ω, ν.weight ω * X ω

private theorem expectation_add (ν : FiniteLaw Ω) (X Y : Ω → ℝ) :
    expectation ν (fun ω => X ω + Y ω) =
      expectation ν X + expectation ν Y := by
  unfold expectation
  simp_rw [mul_add]
  exact Finset.sum_add_distrib

private theorem expectation_sub (ν : FiniteLaw Ω) (X Y : Ω → ℝ) :
    expectation ν (fun ω => X ω - Y ω) =
      expectation ν X - expectation ν Y := by
  unfold expectation
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib]

private theorem expectation_const (ν : FiniteLaw Ω) (c : ℝ) :
    expectation ν (fun _ => c) = c := by
  unfold expectation
  rw [← Finset.sum_mul, ν.total, one_mul]

private theorem expectation_mul_const (ν : FiniteLaw Ω) (X : Ω → ℝ)
    (c : ℝ) : expectation ν (fun ω => X ω * c) =
      expectation ν X * c := by
  unfold expectation
  calc
    (∑ ω, ν.weight ω * (X ω * c)) =
        ∑ ω, (ν.weight ω * X ω) * c := by
          apply Finset.sum_congr rfl
          intro ω _
          ring
    _ = _ := by rw [Finset.sum_mul]

private theorem expectation_sum {ι : Type*} [Fintype ι]
    (ν : FiniteLaw Ω) (X : ι → Ω → ℝ) :
    expectation ν (fun ω => ∑ i, X i ω) =
      ∑ i, expectation ν (X i) := by
  unfold expectation
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]

private theorem indicator_mean (ν : FiniteLaw Ω) (E : Ω → Prop) :
    expectation ν (fun ω => if E ω then 1 else 0) = ν.prob E := by
  classical
  unfold expectation FiniteLaw.prob
  apply Finset.sum_congr rfl
  intro ω _
  by_cases h : E ω <;> simp [h]

private theorem indicator_product_mean (ν : FiniteLaw Ω)
    (E F : Ω → Prop) :
    expectation ν (fun ω =>
      (if E ω then 1 else 0) * (if F ω then 1 else 0)) =
      ν.prob (fun ω => E ω ∧ F ω) := by
  classical
  unfold expectation FiniteLaw.prob
  apply Finset.sum_congr rfl
  intro ω _
  by_cases he : E ω <;> by_cases hf : F ω <;> simp [he, hf]

private theorem centered_indicator_diag (ν : FiniteLaw Ω)
    (E : Ω → Prop) :
    expectation ν (fun ω =>
      ((if E ω then (1 : ℝ) else 0) - ν.prob E) ^ 2) ≤ ν.prob E := by
  classical
  let p := ν.prob E
  have hfun (ω : Ω) :
      ((if E ω then (1 : ℝ) else 0) - p) ^ 2 =
        (if E ω then (1 : ℝ) else 0) -
          (if E ω then (1 : ℝ) else 0) * (2 * p) + p ^ 2 := by
    by_cases h : E ω <;> simp [h] <;> ring
  calc
    expectation ν (fun ω =>
        ((if E ω then (1 : ℝ) else 0) - ν.prob E) ^ 2) =
        expectation ν (fun ω =>
          (if E ω then (1 : ℝ) else 0) -
            (if E ω then (1 : ℝ) else 0) * (2 * p) + p ^ 2) := by
          congr 1; funext ω; exact hfun ω
    _ = p - 2 * p * p + p ^ 2 := by
      rw [expectation_add, expectation_sub,
        expectation_mul_const, expectation_const, indicator_mean]
      simp only [p]
      ring
    _ ≤ p := by
      have hp := ν.prob_nonneg E
      nlinarith [sq_nonneg p]

private theorem centered_indicator_cross (ν : FiniteLaw Ω)
    (E F : Ω → Prop)
    (hpair : ν.prob (fun ω => E ω ∧ F ω) =
      ν.prob E * ν.prob F) :
    expectation ν (fun ω =>
      ((if E ω then (1 : ℝ) else 0) - ν.prob E) *
        ((if F ω then (1 : ℝ) else 0) - ν.prob F)) = 0 := by
  classical
  let p := ν.prob E
  let q := ν.prob F
  have hfun (ω : Ω) :
      ((if E ω then (1 : ℝ) else 0) - p) *
        ((if F ω then (1 : ℝ) else 0) - q) =
      (if E ω then (1 : ℝ) else 0) * (if F ω then 1 else 0) -
        (if E ω then (1 : ℝ) else 0) * q -
        (if F ω then (1 : ℝ) else 0) * p + p * q := by ring
  calc
    expectation ν (fun ω =>
        ((if E ω then (1 : ℝ) else 0) - ν.prob E) *
          ((if F ω then (1 : ℝ) else 0) - ν.prob F)) =
      expectation ν (fun ω =>
        (if E ω then (1 : ℝ) else 0) * (if F ω then 1 else 0) -
          (if E ω then (1 : ℝ) else 0) * q -
          (if F ω then (1 : ℝ) else 0) * p + p * q) := by
        congr 1; funext ω; exact hfun ω
    _ = ν.prob (fun ω => E ω ∧ F ω) - p * q - q * p + p * q := by
      rw [expectation_add, expectation_sub, expectation_sub,
        expectation_mul_const, expectation_mul_const, expectation_const,
        indicator_product_mean, indicator_mean, indicator_mean]
    _ = 0 := by rw [hpair]; ring

/-- The elementary zero-event bound used after the pairwise variance
calculation.  This is a direct weighted-sum argument, not a concentration
axiom or a statement that an arbitrarily retained set is independent. -/
theorem avoid_mass_le_inv_mean (ν : FiniteLaw Ω)
    (A : Ω → Prop) (X : Ω → ℝ) (M : ℝ)
    (hM : 0 < M) (hzero : ∀ ω, A ω → X ω = 0)
    (hvariance : expectation ν (fun ω => (X ω - M) ^ 2) ≤ M) :
    ν.prob A ≤ 1 / M := by
  classical
  have hpoint : M ^ 2 * ν.prob A ≤
      expectation ν (fun ω => (X ω - M) ^ 2) := by
    unfold FiniteLaw.prob expectation
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro ω _
    by_cases hA : A ω
    · simp only [hA, ↓reduceIte, hzero ω hA, zero_sub]
      nlinarith
    · simp only [hA, ↓reduceIte, mul_zero]
      exact mul_nonneg (ν.nonneg ω) (sq_nonneg _)
  have hmul : ν.prob A * M ≤ 1 := by
    have hh := hpoint.trans hvariance
    have hmul' : M * (ν.prob A * M) ≤ M * 1 := by
      nlinarith
    exact (mul_le_mul_iff_of_pos_left hM).mp hmul'
  exact (le_div_iff₀ hM).2 hmul

/-- Pairwise independence of the actual missed events gives the precise
second-moment inequality used by `det:near-full`.  No whole-word product law
and no independence after retention are assumed. -/
theorem avoid_mass_le_of_pairwise (ν : FiniteLaw Ω) (m : ℕ)
    (F : Fin m → Ω → Prop) (A : Ω → Prop)
    (hpair : ∀ i j : Fin m, i ≠ j →
      ν.prob (fun ω => F i ω ∧ F j ω) =
        ν.prob (F i) * ν.prob (F j))
    (hA : ∀ ω, A ω → ∀ i, ¬ F i ω)
    (hM : 0 < ∑ i : Fin m, ν.prob (F i)) :
    ν.prob A ≤ 1 / (∑ i : Fin m, ν.prob (F i)) := by
  classical
  let p : Fin m → ℝ := fun i => ν.prob (F i)
  let X : Fin m → Ω → ℝ := fun i ω =>
    (if F i ω then 1 else 0) - p i
  let Z : Ω → ℝ := fun ω => ∑ i : Fin m,
    (if F i ω then (1 : ℝ) else 0)
  let M : ℝ := ∑ i : Fin m, p i
  have hzero : ∀ ω, A ω → Z ω = 0 := by
    intro ω hω
    simp [Z, hA ω hω]
  have hsum (ω : Ω) : Z ω - M = ∑ i : Fin m, X i ω := by
    simp only [Z, M, X, ← Finset.sum_sub_distrib]
  have hdiag : ∀ i : Fin m,
      expectation ν (fun ω => (X i ω) ^ 2) ≤ p i := by
    intro i
    exact centered_indicator_diag ν (F i)
  have hcross : ∀ i j : Fin m, i ≠ j →
      expectation ν (fun ω => X i ω * X j ω) = 0 := by
    intro i j hij
    exact centered_indicator_cross ν (F i) (F j) (hpair i j hij)
  have hsquare (ω : Ω) :
      (∑ i : Fin m, X i ω) ^ 2 =
        ∑ i : Fin m, ∑ j : Fin m, X i ω * X j ω := by
    rw [pow_two, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
  have hcollapse :
      (∑ i : Fin m, ∑ j : Fin m,
        expectation ν (fun ω => X i ω * X j ω)) =
      ∑ i : Fin m, expectation ν (fun ω => (X i ω) ^ 2) := by
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_eq_single i]
    · congr 1
      funext ω
      ring
    · intro j _ hij
      exact hcross i j (Ne.symm hij)
    · intro hi
      exact False.elim (hi (Finset.mem_univ i))
  have hvariance : expectation ν (fun ω => (Z ω - M) ^ 2) ≤ M := by
    calc
      expectation ν (fun ω => (Z ω - M) ^ 2) =
          expectation ν (fun ω => (∑ i : Fin m, X i ω) ^ 2) := by
            congr 1; funext ω; rw [hsum]
      _ = expectation ν (fun ω =>
          ∑ i : Fin m, ∑ j : Fin m, X i ω * X j ω) := by
            congr 1; funext ω; exact hsquare ω
      _ = ∑ i : Fin m, ∑ j : Fin m,
          expectation ν (fun ω => X i ω * X j ω) := by
            rw [expectation_sum]
            apply Finset.sum_congr rfl
            intro i _
            rw [expectation_sum]
      _ = ∑ i : Fin m, expectation ν (fun ω => (X i ω) ^ 2) := hcollapse
      _ ≤ ∑ i : Fin m, p i := by
        apply Finset.sum_le_sum
        intro i _
        exact hdiag i
  exact avoid_mass_le_inv_mean ν A Z M hM hzero hvariance

end CurrentAdditive.PairwiseMissedEvents

#print axioms CurrentAdditive.PairwiseMissedEvents.avoid_mass_le_inv_mean
#print axioms CurrentAdditive.PairwiseMissedEvents.avoid_mass_le_of_pairwise
