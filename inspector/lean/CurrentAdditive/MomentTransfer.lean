import CurrentAdditive.ConditioningMoments

/-! Private v27 proof packet: bounded-wise transfer of centered Boolean moments. -/

namespace CurrentAdditive

open Paper2
open scoped BigOperators

variable {Ω : Type*} [Fintype Ω] {m : ℕ}

/-- Agreement of the joint law of the Boolean tests on every coordinate set
of size at most `R`, against independent draws from the original one-point
law. The tests may have different marginals. -/
def IndicatorJointAgreement (ν : FiniteLaw Ω) (F : Fin m → Ω → Bool)
    (R : ℕ) : Prop :=
  ∀ (s : Finset (Fin m)), s.card ≤ R → ∀ E : (s → Bool) → Prop,
    ν.prob (fun ω => E (fun i : s => F i ω)) =
      (ν.iid m).prob (fun ws => E (fun i : s => F i (ws i)))

/-- Expand the integral of a finite-valued statistic over its value fibres. -/
private theorem expectation_comp_eq_sum
    {D C : Type*} [Fintype D] [Fintype C]
    (rho : FiniteLaw D) (z : D → C) (h : C → ℝ) :
    expectation rho (fun a => h (z a)) =
      ∑ v : C, h v * rho.prob (fun a => z a = v) := by
  classical
  unfold expectation FiniteLaw.prob
  calc
    (∑ a, rho.weight a * h (z a)) =
        ∑ a, ∑ v : C, if z a = v then rho.weight a * h v else 0 := by
      apply Finset.sum_congr rfl
      intro a _
      simp
    _ = ∑ v : C, ∑ a, if z a = v then rho.weight a * h v else 0 :=
      Finset.sum_comm
    _ = ∑ v : C, h v * ∑ a, if z a = v then rho.weight a else 0 := by
      apply Finset.sum_congr rfl
      intro v _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      split_ifs <;> ring

/-- The integral of any finite-valued statistic is determined by its law. -/
private theorem expectation_comp_eq_of_prob_eq
    {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]
    (μ : FiniteLaw A) (ξ : FiniteLaw B)
    (f : A → C) (g : B → C)
    (hlaw : ∀ E : C → Prop, μ.prob (fun a => E (f a)) =
      ξ.prob (fun b => E (g b))) (h : C → ℝ) :
    expectation μ (fun a => h (f a)) =
      expectation ξ (fun b => h (g b)) := by
  rw [expectation_comp_eq_sum μ f h, expectation_comp_eq_sum ξ g h]
  apply Finset.sum_congr rfl
  intro v _
  rw [hlaw (fun w => w = v)]

private theorem indicator_joint_expectation
    (ν : FiniteLaw Ω) (F : Fin m → Ω → Bool) (R : ℕ)
    (h : IndicatorJointAgreement ν F R) (s : Finset (Fin m))
    (hs : s.card ≤ R) (G : (s → Bool) → ℝ) :
    expectation ν (fun ω => G (fun i : s => F i ω)) =
      expectation (ν.iid m) (fun ws => G (fun i : s => F i (ws i))) := by
  exact expectation_comp_eq_of_prob_eq ν (ν.iid m)
    (fun ω (i : s) => F i ω) (fun ws (i : s) => F i (ws i)) (h s hs) G

/-- Every ordered product of `R` centered indicators only depends on at most
`R` distinct test coordinates. -/
private theorem centered_indicator_product_eq_proxy
    (ν : FiniteLaw Ω) (F : Fin m → Ω → Bool) (R : ℕ)
    (h : IndicatorJointAgreement ν F R) (k : Fin R → Fin m) :
    expectation ν (fun ω => ∏ j : Fin R,
      ((if F (k j) ω then (1 : ℝ) else 0) -
        ν.prob (fun ω' => F (k j) ω'))) =
    expectation (ν.iid m) (fun ws => ∏ j : Fin R,
      ((if F (k j) (ws (k j)) then (1 : ℝ) else 0) -
        ν.prob (fun ω' => F (k j) ω'))) := by
  classical
  let s : Finset (Fin m) := Finset.univ.image k
  have hmem (j : Fin R) : k j ∈ s :=
    Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩
  have hs : s.card ≤ R := by
    simpa [s] using (Finset.card_image_le (s := Finset.univ) (f := k))
  let G : (s → Bool) → ℝ := fun b => ∏ j : Fin R,
    ((if b ⟨k j, hmem j⟩ then (1 : ℝ) else 0) -
      ν.prob (fun ω' => F (k j) ω'))
  simpa only [G] using indicator_joint_expectation ν F R h s hs G

/-- Exact `R`th centered moment transfer from bounded-wise joint-law
agreement to a full independent product. Repeated indices in a monomial
are supported on their distinct-index image, whose size is at most `R`. -/
theorem centered_indicator_raw_moment_eq_proxy
    (ν : FiniteLaw Ω) (F : Fin m → Ω → Bool) (R : ℕ)
    (h : IndicatorJointAgreement ν F R) :
    expectation ν (fun ω =>
      (∑ i : Fin m, ((if F i ω then (1 : ℝ) else 0) -
        ν.prob (fun ω' => F i ω')))^R) =
    expectation (ν.iid m) (fun ws =>
      (∑ i : Fin m, ((if F i (ws i) then (1 : ℝ) else 0) -
        ν.prob (fun ω' => F i ω')))^R) := by
  classical
  have hactual (ω : Ω) :
      (∑ i : Fin m, ((if F i ω then (1 : ℝ) else 0) -
        ν.prob (fun ω' => F i ω')))^R =
      ∑ k : Fin R → Fin m, ∏ j : Fin R,
        ((if F (k j) ω then (1 : ℝ) else 0) -
          ν.prob (fun ω' => F (k j) ω')) := by
    exact Fintype.sum_pow _ _
  have hproxy (ws : Fin m → Ω) :
      (∑ i : Fin m, ((if F i (ws i) then (1 : ℝ) else 0) -
        ν.prob (fun ω' => F i ω')))^R =
      ∑ k : Fin R → Fin m, ∏ j : Fin R,
        ((if F (k j) (ws (k j)) then (1 : ℝ) else 0) -
          ν.prob (fun ω' => F (k j) ω')) := by
    exact Fintype.sum_pow _ _
  simp_rw [hactual, hproxy]
  rw [expectation_sum, expectation_sum]
  apply Finset.sum_congr rfl
  intro k _
  exact centered_indicator_product_eq_proxy ν F R h k

/-- At even integer order, absolute powers are ordinary powers, so the
transfer gives exactly the moment used in the conditioning argument. -/
theorem centered_indicator_even_moment_eq_proxy
    (ν : FiniteLaw Ω) (F : Fin m → Ω → Bool) (R : ℕ)
    (hR : Even R) (h : IndicatorJointAgreement ν F R) :
    expectation ν (fun ω =>
      |∑ i : Fin m, ((if F i ω then (1 : ℝ) else 0) -
        ν.prob (fun ω' => F i ω'))|^R) =
    expectation (ν.iid m) (fun ws =>
      |∑ i : Fin m, ((if F i (ws i) then (1 : ℝ) else 0) -
        ν.prob (fun ω' => F i ω'))|^R) := by
  have habs (x : ℝ) : |x| ^ R = x ^ R := hR.pow_abs x
  simp_rw [habs]
  exact centered_indicator_raw_moment_eq_proxy ν F R h

#print axioms centered_indicator_raw_moment_eq_proxy
#print axioms centered_indicator_even_moment_eq_proxy

end CurrentAdditive
