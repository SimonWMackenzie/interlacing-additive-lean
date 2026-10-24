import Mathlib

/-!
# Finite sampling for Paper 2

Source: v12, Section 2, Theorem `thm:compression`, the two probability
paragraphs.  These are probability lemmas, not a formalization of the
communication-theoretic hypotheses or the reduction.

The law below is an actual normalized, nonnegative finite law.  Product
weights implement independent draws.  No union-bound or conditional-error
conclusion is a field of the law or an assumed certificate.
-/

namespace Paper2

open scoped BigOperators

/-- A finite probability law. Zero-weight points are allowed. -/
structure FiniteLaw (α : Type*) [Fintype α] where
  weight : α → ℝ
  nonneg : ∀ a, 0 ≤ weight a
  total : ∑ a, weight a = 1

namespace FiniteLaw

variable {α β : Type*} [Fintype α] [Fintype β]

/-- Probability of an event; arbitrary predicates are allowed. -/
noncomputable def prob (μ : FiniteLaw α) (E : α → Prop) : ℝ := by
  classical
  exact ∑ a, if E a then μ.weight a else 0

theorem prob_nonneg (μ : FiniteLaw α) (E : α → Prop) : 0 ≤ μ.prob E := by
  classical
  exact Finset.sum_nonneg fun a _ => by split_ifs <;> simp_all [μ.nonneg]

@[simp] theorem prob_true (μ : FiniteLaw α) : μ.prob (fun _ => True) = 1 := by
  simp [prob, μ.total]

@[simp] theorem prob_false (μ : FiniteLaw α) : μ.prob (fun _ => False) = 0 := by
  simp [prob]

theorem prob_mono (μ : FiniteLaw α) {E F : α → Prop}
    (h : ∀ a, E a → F a) : μ.prob E ≤ μ.prob F := by
  classical
  apply Finset.sum_le_sum
  intro a _
  by_cases hE : E a
  · simp [hE, h a hE]
  · simp only [hE, ↓reduceIte]
    split_ifs <;> simp_all [μ.nonneg]

theorem prob_le_one (μ : FiniteLaw α) (E : α → Prop) : μ.prob E ≤ 1 := by
  simpa using μ.prob_mono (E := E) (F := fun _ => True) (fun _ _ => trivial)

/-- Normalization excludes an empty sample space. -/
theorem nonempty (μ : FiniteLaw α) : Nonempty α := by
  by_contra h
  haveI : IsEmpty α := not_nonempty_iff.mp h
  have := μ.total
  simp at this

/-- The law of an indexed list of `m` independent draws. -/
noncomputable def iid (μ : FiniteLaw α) (m : ℕ) : FiniteLaw (Fin m → α) where
  weight x := ∏ i, μ.weight (x i)
  nonneg x := Finset.prod_nonneg fun i _ => μ.nonneg (x i)
  total := by
    classical
    have h := Finset.sum_prod_piFinset (ι := Fin m) (Finset.univ : Finset α)
      (fun _ a => μ.weight a)
    simpa [μ.total] using h

/-- Exact product law for all samples belonging to one domain, including
`m = 0`. Indexed repetitions are not identified. -/
theorem iid_prob_all (μ : FiniteLaw α) (m : ℕ) (E : α → Prop) :
    (μ.iid m).prob (fun x => ∀ i, E (x i)) = (μ.prob E) ^ m := by
  classical
  have hprod (x : Fin m → α) :
      (if ∀ i, E (x i) then ∏ i, μ.weight (x i) else 0) =
        ∏ i, if E (x i) then μ.weight (x i) else 0 := by
    by_cases hx : ∀ i, E (x i)
    · simp [hx]
    · obtain ⟨i, hi⟩ := not_forall.mp hx
      simp only [hx, ↓reduceIte]
      symm
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      simp [hi]
  simp only [prob, iid]
  simp_rw [hprod]
  have h := Finset.sum_prod_piFinset (ι := Fin m) (Finset.univ : Finset α)
    (fun _ a => if E a then μ.weight a else 0)
  simpa using h

/-- Finite union bound proved directly from nonnegative weights. -/
theorem prob_exists_le_sum (μ : FiniteLaw α) {ι : Type*}
    (s : Finset ι) (E : ι → α → Prop) :
    μ.prob (fun a => ∃ i ∈ s, E i a) ≤ ∑ i ∈ s, μ.prob (E i) := by
  classical
  unfold prob
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro a _
  by_cases h : ∃ i ∈ s, E i a
  · obtain ⟨i, hi, hE⟩ := h
    simp only [show (∃ i ∈ s, E i a) from ⟨i, hi, hE⟩, ↓reduceIte]
    have hle := Finset.single_le_sum
      (f := fun j => if E j a then μ.weight a else 0)
      (fun j (_ : j ∈ s) => by dsimp; split_ifs <;> simp_all [μ.nonneg]) hi
    simpa [hE] using hle
  · simp only [h, ↓reduceIte]
    exact Finset.sum_nonneg fun i _ => by split_ifs <;> simp_all

/-- The sampling union bound, uniform over every domain in the family.
The family is chosen before the sample. -/
theorem iid_prob_some_domain_le (μ : FiniteLaw α) (m : ℕ)
    {ι : Type*} (s : Finset ι) (E : ι → α → Prop) (q : ℝ)
    (hE : ∀ i ∈ s, μ.prob (E i) ≤ q) :
    (μ.iid m).prob (fun x => ∃ i ∈ s, ∀ j, E i (x j)) ≤
      (s.card : ℝ) * q ^ m := by
  calc
    _ ≤ ∑ i ∈ s, (μ.iid m).prob (fun x => ∀ j, E i (x j)) :=
      (μ.iid m).prob_exists_le_sum s _
    _ = ∑ i ∈ s, (μ.prob (E i)) ^ m := by
      apply Finset.sum_congr rfl
      intro i _
      exact iid_prob_all μ m (E i)
    _ ≤ ∑ _i ∈ s, q ^ m := by
      exact Finset.sum_le_sum fun i hi => pow_le_pow_left₀ (μ.prob_nonneg _) (hE i hi) m
    _ = (s.card : ℝ) * q ^ m := by simp

theorem iid_prob_some_domain_le_of_card (μ : FiniteLaw α) (m : ℕ)
    {ι : Type*} (s : Finset ι) (E : ι → α → Prop) (q : ℝ) (K : ℕ)
    (hq : 0 ≤ q) (hcard : s.card ≤ K)
    (hE : ∀ i ∈ s, μ.prob (E i) ≤ q) :
    (μ.iid m).prob (fun x => ∃ i ∈ s, ∀ j, E i (x j)) ≤
      (K : ℝ) * q ^ m := by
  apply (iid_prob_some_domain_le μ m s E q hE).trans
  exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hcard) (pow_nonneg hq m)

/-- Independent first and second sample spaces. -/
noncomputable def prod (μ : FiniteLaw α) (ν : FiniteLaw β) : FiniteLaw (α × β) where
  weight x := μ.weight x.1 * ν.weight x.2
  nonneg x := mul_nonneg (μ.nonneg _) (ν.nonneg _)
  total := by
    simp only [Fintype.sum_prod_type, ← Finset.mul_sum, ν.total, mul_one, μ.total]

/-- Sum over first-stage outcomes of the second-stage event probability. -/
theorem prod_prob (μ : FiniteLaw α) (ν : FiniteLaw β) (E : α → β → Prop) :
    (μ.prod ν).prob (fun x => E x.1 x.2) =
      ∑ a, μ.weight a * ν.prob (E a) := by
  classical
  simp only [prob, prod, Fintype.sum_prod_type, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  split_ifs <;> simp

/-- Two-stage error accounting. The first-stage good event may depend
arbitrarily on its outcome. The second event may depend on that entire
outcome; only a pointwise bound for good outcomes is assumed. In particular,
no independence between the good event and the final failure is assumed. -/
theorem two_stage_failure_le (μ : FiniteLaw α) (ν : FiniteLaw β)
    (Good : α → Prop) (Bad : α → β → Prop) (ε₁ ε₂ : ℝ)
    (hfirst : μ.prob (fun a => ¬ Good a) ≤ ε₁)
    (hsecond : ∀ a, Good a → ν.prob (Bad a) ≤ ε₂)
    (hε₂ : 0 ≤ ε₂) :
    (μ.prod ν).prob (fun x => Bad x.1 x.2) ≤ ε₁ + ε₂ := by
  classical
  rw [prod_prob]
  calc
    _ ≤ ∑ a, ((if ¬ Good a then μ.weight a else 0) + μ.weight a * ε₂) := by
      apply Finset.sum_le_sum
      intro a _
      by_cases ha : Good a
      · simp only [ha, not_true_eq_false, ↓reduceIte, zero_add]
        exact mul_le_mul_of_nonneg_left (hsecond a ha) (μ.nonneg a)
      · simp only [ha, not_false_eq_true, ↓reduceIte]
        have hle : μ.weight a * ν.prob (Bad a) ≤ μ.weight a := by
          simpa using mul_le_mul_of_nonneg_left (ν.prob_le_one _) (μ.nonneg a)
        exact hle.trans (le_add_of_nonneg_right (mul_nonneg (μ.nonneg a) hε₂))
    _ = μ.prob (fun a => ¬ Good a) + ε₂ := by
      rw [Finset.sum_add_distrib, ← Finset.sum_mul, μ.total, one_mul]
      unfold prob
      congr 1
      apply Finset.sum_congr rfl
      intro a _
      by_cases ha : Good a <;> simp [ha]
    _ ≤ ε₁ + ε₂ := by linarith

/-- Complete two-stage domain-sampling inequality. First-stage domains are
fixed before sampling. The second catalogue and its events may depend on
the entire first outcome, but its cardinality and mass bounds must hold on
every good first outcome. Final failure is allowed to happen arbitrarily
on a bad first outcome. -/
theorem two_stage_iid_domains_le (μ : FiniteLaw α) (ν : FiniteLaw β)
    (m n : ℕ) {ι κ : Type*}
    (s : Finset ι) (E : ι → α → Prop)
    (t : (Fin m → α) → Finset κ)
    (F : (Fin m → α) → κ → β → Prop)
    (Bad : (Fin m → α) → (Fin n → β) → Prop)
    (q₁ q₂ : ℝ) (K₁ K₂ : ℕ)
    (hq₁ : 0 ≤ q₁) (hq₂ : 0 ≤ q₂)
    (hcard₁ : s.card ≤ K₁) (hmass₁ : ∀ i ∈ s, μ.prob (E i) ≤ q₁)
    (hcard₂ : ∀ x, (¬ ∃ i ∈ s, ∀ j, E i (x j)) → (t x).card ≤ K₂)
    (hmass₂ : ∀ x, (¬ ∃ i ∈ s, ∀ j, E i (x j)) →
      ∀ i ∈ t x, ν.prob (F x i) ≤ q₂)
    (hcover : ∀ x, (¬ ∃ i ∈ s, ∀ j, E i (x j)) →
      ∀ y, Bad x y → ∃ i ∈ t x, ∀ j, F x i (y j)) :
    ((μ.iid m).prod (ν.iid n)).prob (fun z => Bad z.1 z.2) ≤
      (K₁ : ℝ) * q₁ ^ m + (K₂ : ℝ) * q₂ ^ n := by
  classical
  apply two_stage_failure_le (μ.iid m) (ν.iid n)
    (fun x => ¬ ∃ i ∈ s, ∀ j, E i (x j)) Bad
  · simpa only [not_not] using
      iid_prob_some_domain_le_of_card μ m s E q₁ K₁ hq₁ hcard₁ hmass₁
  · intro x hx
    apply ((ν.iid n).prob_mono (hcover x hx)).trans
    exact iid_prob_some_domain_le_of_card ν n (t x) (F x) q₂ K₂ hq₂
      (hcard₂ x hx) (hmass₂ x hx)
  · exact mul_nonneg (Nat.cast_nonneg K₂) (pow_nonneg hq₂ n)

end FiniteLaw

end Paper2
