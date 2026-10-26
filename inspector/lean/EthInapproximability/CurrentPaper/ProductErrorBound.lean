import Mathlib

/-!
# Multiplication of finite relative-error bounds

Source: the locked current paper, Appendix A, Lemma `paper-product-extraction`,
part (3). This arithmetic lemma controls the realization ratios of independent
indexed families. It does not assert that any particular family is balanced.

The upper relative error dominates both signs, even when the error parameter
is larger than one. Zero baseline factors and the empty product are included.
-/

namespace EthInapproximability.CurrentPaper.ProductErrorBound

open scoped BigOperators

/-- Coordinatewise relative error gives the corresponding product upper bound. -/
theorem prod_le_of_relative_error {ι : Type*} (s : Finset ι) (p b : ι → ℝ)
    {ε : ℝ} (_hε : 0 ≤ ε) (hp : ∀ i ∈ s, 0 ≤ p i)
    (_hb : ∀ i ∈ s, 0 ≤ b i)
    (herr : ∀ i ∈ s, |p i - b i| ≤ ε * b i) :
    (∏ i ∈ s, p i) ≤ (1 + ε) ^ s.card * (∏ i ∈ s, b i) := by
  calc
    (∏ i ∈ s, p i) ≤ ∏ i ∈ s, ((1 + ε) * b i) := by
      apply Finset.prod_le_prod hp
      intro i hi
      have h := (abs_le.mp (herr i hi)).2
      nlinarith
    _ = (1 + ε) ^ s.card * (∏ i ∈ s, b i) := by
      rw [Finset.prod_mul_distrib, Finset.prod_const]

/-- Relative errors multiply with error at most `(1 + ε)^|s| - 1`.
The estimate includes both the upper and lower deviation. -/
theorem abs_prod_sub_prod_le {ι : Type*} (s : Finset ι) (p b : ι → ℝ)
    {ε : ℝ} (hε : 0 ≤ ε) (hp : ∀ i ∈ s, 0 ≤ p i)
    (hb : ∀ i ∈ s, 0 ≤ b i)
    (herr : ∀ i ∈ s, |p i - b i| ≤ ε * b i) :
    |(∏ i ∈ s, p i) - (∏ i ∈ s, b i)| ≤
      ((1 + ε) ^ s.card - 1) * (∏ i ∈ s, b i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    have hpa : 0 ≤ p a := hp a (Finset.mem_insert_self _ _)
    have hba : 0 ≤ b a := hb a (Finset.mem_insert_self _ _)
    have hea := herr a (Finset.mem_insert_self _ _)
    have hps : ∀ i ∈ s, 0 ≤ p i := fun i hi => hp i (Finset.mem_insert_of_mem hi)
    have hbs : ∀ i ∈ s, 0 ≤ b i := fun i hi => hb i (Finset.mem_insert_of_mem hi)
    have hes : ∀ i ∈ s, |p i - b i| ≤ ε * b i :=
      fun i hi => herr i (Finset.mem_insert_of_mem hi)
    have hih := ih hps hbs hes
    have hB : 0 ≤ ∏ i ∈ s, b i := Finset.prod_nonneg hbs
    have hpow : 0 ≤ (1 + ε) ^ s.card - 1 := by
      have : (1 : ℝ) ≤ (1 + ε) ^ s.card :=
        one_le_pow₀ (show (1 : ℝ) ≤ 1 + ε by linarith)
      linarith
    have hpaUpper : p a ≤ (1 + ε) * b a := by
      have := (abs_le.mp hea).2
      nlinarith
    simp only [Finset.prod_insert ha, Finset.card_insert_of_notMem ha]
    calc
      |p a * (∏ i ∈ s, p i) - b a * (∏ i ∈ s, b i)| =
          |p a * ((∏ i ∈ s, p i) - (∏ i ∈ s, b i)) +
            (p a - b a) * (∏ i ∈ s, b i)| := by congr 1; ring
      _ ≤ |p a * ((∏ i ∈ s, p i) - (∏ i ∈ s, b i))| +
          |(p a - b a) * (∏ i ∈ s, b i)| := abs_add_le _ _
      _ = p a * |(∏ i ∈ s, p i) - (∏ i ∈ s, b i)| +
          |p a - b a| * (∏ i ∈ s, b i) := by
        rw [abs_mul, abs_mul, abs_of_nonneg hpa, abs_of_nonneg hB]
      _ ≤ p a * (((1 + ε) ^ s.card - 1) * (∏ i ∈ s, b i)) +
          (ε * b a) * (∏ i ∈ s, b i) := by
        exact add_le_add (mul_le_mul_of_nonneg_left hih hpa)
          (mul_le_mul_of_nonneg_right hea hB)
      _ ≤ ((1 + ε) * b a) *
            (((1 + ε) ^ s.card - 1) * (∏ i ∈ s, b i)) +
          (ε * b a) * (∏ i ∈ s, b i) := by
        exact add_le_add
          (mul_le_mul_of_nonneg_right hpaUpper (mul_nonneg hpow hB)) le_rfl
      _ = ((1 + ε) ^ (s.card + 1) - 1) *
          (b a * (∏ i ∈ s, b i)) := by rw [pow_succ]; ring

/-- An upper bound on the number of affected factors suffices. -/
theorem abs_prod_sub_prod_le_of_card_le {ι : Type*} (s : Finset ι) (p b : ι → ℝ)
    {ε : ℝ} {t : ℕ} (hε : 0 ≤ ε) (hcard : s.card ≤ t)
    (hp : ∀ i ∈ s, 0 ≤ p i) (hb : ∀ i ∈ s, 0 ≤ b i)
    (herr : ∀ i ∈ s, |p i - b i| ≤ ε * b i) :
    |(∏ i ∈ s, p i) - (∏ i ∈ s, b i)| ≤
      ((1 + ε) ^ t - 1) * (∏ i ∈ s, b i) := by
  exact (abs_prod_sub_prod_le s p b hε hp hb herr).trans
    (mul_le_mul_of_nonneg_right
      (sub_le_sub_right (pow_le_pow_right₀ (by linarith : (1 : ℝ) ≤ 1 + ε) hcard) 1)
      (Finset.prod_nonneg hb))

/-- The same bound on the full finite index type. -/
theorem abs_prod_sub_prod_le_univ {ι : Type*} [Fintype ι] (p b : ι → ℝ)
    {ε : ℝ} (hε : 0 ≤ ε) (hp : ∀ i, 0 ≤ p i)
    (hb : ∀ i, 0 ≤ b i) (herr : ∀ i, |p i - b i| ≤ ε * b i) :
    |(∏ i, p i) - (∏ i, b i)| ≤
      ((1 + ε) ^ Fintype.card ι - 1) * (∏ i, b i) := by
  simpa using abs_prod_sub_prod_le Finset.univ p b hε
    (fun i _ => hp i) (fun i _ => hb i) (fun i _ => herr i)

/-- Regression: the estimate permits a zero baseline factor. -/
theorem zero_baseline_regression :
    |(∏ i : Fin 2, (![0, (3 : ℝ)] : Fin 2 → ℝ) i) -
      (∏ i : Fin 2, (![0, (2 : ℝ)] : Fin 2 → ℝ) i)| ≤
      ((1 + (1 / 2 : ℝ)) ^ 2 - 1) *
        (∏ i : Fin 2, (![0, (2 : ℝ)] : Fin 2 → ℝ) i) := by
  convert abs_prod_sub_prod_le_univ
    (![0, (3 : ℝ)] : Fin 2 → ℝ) (![0, (2 : ℝ)] : Fin 2 → ℝ)
    (ε := 1 / 2) (by norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num) using 1

end EthInapproximability.CurrentPaper.ProductErrorBound
