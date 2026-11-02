import Paper2.FiniteSampling
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Probability.ProbabilityMassFunction.Integrals

/-!
# Finite-law concentration for the Yao selector event

Source: v12, Appendix B, `yao:rectangle-event`.  The normalized finite law is
converted to an actual probability mass function only for Mathlib's proved
Hoeffding lemma.  Independence is implemented by the product weights in
`FiniteLaw.iid`; the exponential-moment factorization and tail estimate below
are finite-sum identities and inequalities.
-/

namespace Paper2.FiniteLaw

open scoped BigOperators
open MeasureTheory ProbabilityTheory

variable {α : Type*} [Fintype α]

open Classical in
/-- The centered indicator of any event has the usual Hoeffding exponential
moment bound.  This is proved from a normalized finite law, not assumed. -/
theorem indicator_mgf_le (μ : FiniteLaw α) (E : α → Prop) (t : ℝ) :
    (∑ a, μ.weight a * Real.exp (t * ((if E a then 1 else 0) - μ.prob E))) ≤
      Real.exp (t ^ 2 / 8) := by
  classical
  letI : MeasurableSpace α := ⊤
  letI : MeasurableSingletonClass α := ⟨fun _ => trivial⟩
  let P : PMF α := PMF.ofFintype (fun a => ENNReal.ofReal (μ.weight a)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun a _ => μ.nonneg a), μ.total]
    simp)
  let X : α → ℝ := fun a => if E a then 1 else 0
  have hmean : (∫ a, X a ∂P.toMeasure) = μ.prob E := by
    rw [PMF.integral_eq_sum]
    simp only [P, PMF.ofFintype_apply, ENNReal.toReal_ofReal (μ.nonneg _), smul_eq_mul]
    unfold X prob
    apply Finset.sum_congr rfl
    intro a _
    split_ifs <;> simp
  have hbound : ∀ᵐ a ∂P.toMeasure, X a ∈ Set.Icc (0 : ℝ) 1 := by
    apply Filter.Eventually.of_forall
    intro a
    simp only [X, Set.mem_Icc]
    split_ifs <;> norm_num
  have hsub := hasSubgaussianMGF_of_mem_Icc
    (μ := P.toMeasure) (X := X) (by exact Measurable.aemeasurable (by intro s hs; trivial)) hbound
  have hm := hsub.mgf_le t
  rw [hmean] at hm
  have hm' : (∑ a, μ.weight a * Real.exp (t * ((if E a then 1 else 0) - μ.prob E))) ≤
      Real.exp (((2 : ℝ) ^ 2)⁻¹ * t ^ 2 / 2) := by
    simpa [mgf, PMF.integral_eq_sum, P, X, μ.nonneg, smul_eq_mul] using hm
  convert hm' using 1
  congr 1
  ring

/-- Exact exponential-moment factorization for the concrete IID finite law. -/
theorem iid_exp_sum (μ : FiniteLaw α) (N : ℕ) (f : α → ℝ) (t : ℝ) :
    (∑ ws, (μ.iid N).weight ws * Real.exp (t * ∑ i, f (ws i))) =
      (∑ a, μ.weight a * Real.exp (t * f a)) ^ N := by
  classical
  simp_rw [Finset.mul_sum, Real.exp_sum, iid, ← Finset.prod_mul_distrib]
  have h := Finset.sum_prod_piFinset (ι := Fin N) (Finset.univ : Finset α)
    (fun _ a => μ.weight a * Real.exp (t * f a))
  simpa using h

/-- Chernoff's elementary weighted Markov step on a finite probability law. -/
theorem prob_mul_exp_le (μ : FiniteLaw α) (E : α → Prop) (f : α → ℝ)
    (t b : ℝ) (ht : 0 ≤ t) (hE : ∀ a, E a → b ≤ f a) :
    μ.prob E * Real.exp (t * b) ≤ ∑ a, μ.weight a * Real.exp (t * f a) := by
  classical
  rw [prob, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro a _
  by_cases ha : E a
  · simp only [ha, ↓reduceIte]
    exact mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (hE a ha) ht)) (μ.nonneg a)
  · simp only [ha, ↓reduceIte, zero_mul]
    exact mul_nonneg (μ.nonneg a) (Real.exp_pos _).le

open Classical in
/-- Hoeffding's inequality for the empirical frequency of any event under
independent draws from a normalized finite law. -/
theorem iid_empirical_sum_upper_tail (μ : FiniteLaw α) (E : α → Prop)
    (N : ℕ) (hN : 0 < N) (ε : ℝ) (hε : 0 < ε) :
    (μ.iid N).prob
        (fun ws => μ.prob E + ε < (∑ i : Fin N, if E (ws i) then (1 : ℝ) else 0) / N) ≤
      Real.exp (-2 * N * ε ^ 2) := by
  classical
  let f : α → ℝ := fun a => (if E a then 1 else 0) - μ.prob E
  let Bad : (Fin N → α) → Prop :=
    fun ws => μ.prob E + ε < (∑ i : Fin N, if E (ws i) then (1 : ℝ) else 0) / N
  have hNreal : 0 < (N : ℝ) := Nat.cast_pos.mpr hN
  have hbad : ∀ ws, Bad ws → (N : ℝ) * ε ≤ ∑ i, f (ws i) := by
    intro ws hws
    have ht := (lt_div_iff₀ hNreal).mp hws
    simp only [f, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    nlinarith
  have hm := (μ.iid N).prob_mul_exp_le Bad (fun ws => ∑ i, f (ws i))
    (4 * ε) ((N : ℝ) * ε) (by positivity) hbad
  rw [iid_exp_sum] at hm
  have hpow : (∑ a, μ.weight a * Real.exp ((4 * ε) * f a)) ^ N ≤
      Real.exp ((4 * ε) ^ 2 / 8) ^ N := by
    apply pow_le_pow_left₀
    · exact Finset.sum_nonneg fun a _ => mul_nonneg (μ.nonneg a) (Real.exp_pos _).le
    · exact μ.indicator_mgf_le E (4 * ε)
  have hbound := hm.trans hpow
  rw [← Real.exp_nat_mul] at hbound
  have hdiv := (le_div_iff₀ (Real.exp_pos ((4 * ε) * ((N : ℝ) * ε)))).mpr hbound
  rw [← Real.exp_sub] at hdiv
  convert hdiv using 1
  congr 1
  ring

open Classical in
/-- Cardinality formulation: repeated samples retain their distinct labels. -/
theorem iid_empirical_upper_tail (μ : FiniteLaw α) (E : α → Prop)
    (N : ℕ) (hN : 0 < N) (ε : ℝ) (hε : 0 < ε) :
    (μ.iid N).prob (fun ws => μ.prob E + ε <
      (Fintype.card {i : Fin N // E (ws i)} : ℝ) / N) ≤
      Real.exp (-2 * N * ε ^ 2) := by
  classical
  simpa [Fintype.card_subtype, Finset.sum_boole] using
    μ.iid_empirical_sum_upper_tail E N hN ε hε

end Paper2.FiniteLaw
