import Paper2.RationalTupleTransport

/-!
Private finite total-variation bridge for Appendix H, lines 323--331.
An eventwise probability discrepancy `≤ ε` implies a `≤ 2ε`
expectation discrepancy for any real test function bounded by one.
-/

namespace CurrentAdditive.FourthMoment.TVBridge

open Paper2
open scoped BigOperators

variable {A : Type*} [Fintype A]

noncomputable def expect (μ : FiniteLaw A) (f : A → ℝ) : ℝ :=
  ∑ a, μ.weight a * f a

theorem expect_difference_eq (μ ν : FiniteLaw A) (f : A → ℝ) :
    expect μ f - expect ν f =
      ∑ a, (μ.weight a - ν.weight a) * f a := by
  simp only [expect, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro a _
  ring

/-- A bounded test function has expectation discrepancy at most twice the
eventwise total-variation cap. The factor two covers signed test functions. -/
theorem expect_abs_sub_le_two (μ ν : FiniteLaw A) (f : A → ℝ) (ε : ℝ)
    (hTV : ∀ E : A → Prop, |μ.prob E - ν.prob E| ≤ ε)
    (hf : ∀ a, |f a| ≤ 1) :
    |expect μ f - expect ν f| ≤ 2 * ε := by
  classical
  let d : A → ℝ := fun a => μ.weight a - ν.weight a
  let P : A → Prop := fun a => 0 ≤ d a
  let Q : A → Prop := fun a => ¬ P a
  have hp : (∑ a, if P a then d a else 0) ≤ ε := by
    have h := (abs_le.mp (hTV P)).2
    have he : μ.prob P - ν.prob P = ∑ a, if P a then d a else 0 := by
      unfold FiniteLaw.prob
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro a _
      by_cases ha : P a <;> simp [ha, d]
    linarith
  have hq : (∑ a, if Q a then -d a else 0) ≤ ε := by
    have h := (abs_le.mp (hTV Q)).1
    have he : ν.prob Q - μ.prob Q = ∑ a, if Q a then -d a else 0 := by
      unfold FiniteLaw.prob
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro a _
      by_cases ha : Q a <;> simp [ha, d] <;> ring
    linarith
  have hbound : |∑ a, d a * f a| ≤ ∑ a, |d a| := by
    calc
      _ ≤ ∑ a, |d a * f a| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ a, |d a| := by
        apply Finset.sum_le_sum
        intro a _
        rw [abs_mul]
        exact mul_le_of_le_one_right (abs_nonneg _) (hf a)
  have hsplit : (∑ a, |d a|) =
      (∑ a, if P a then d a else 0) +
      (∑ a, if Q a then -d a else 0) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro a _
    by_cases ha : P a
    · have hd : 0 ≤ d a := ha
      have hqa : ¬ Q a := by simpa [Q] using ha
      simp only [if_pos ha, if_neg hqa, add_zero]
      exact abs_of_nonneg hd
    · have hd : d a < 0 := lt_of_not_ge ha
      have hqa : Q a := ha
      simp only [if_neg ha, if_pos hqa, zero_add]
      exact abs_of_neg hd
  rw [expect_difference_eq]
  exact hbound.trans (by rw [hsplit]; linarith)

#print axioms expect_abs_sub_le_two

end CurrentAdditive.FourthMoment.TVBridge
