import CurrentAdditive.FourthMoment

/-! Generic finite-product cross moments for arbitrary real scalar tests.
The derivations generalize the admitted Boolean product calculations; centering
is the actual single-coordinate expectation equation. -/
namespace GeneralCross
open Paper2 CurrentAdditive.FourthMoment
open scoped BigOperators
variable {A I : Type*} [Fintype A] [Fintype I] [DecidableEq I]

theorem pi_centered_quad_zero_of_unique
    (μ : I → FiniteLaw A) (F : I → A → ℝ)
    (hcenter : ∀ i, expect (μ i) (F i) = 0) (i j k l : I)
    (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l) :
    expect (FiniteLaw.pi μ) (fun x =>
      F j (x j) * F k (x k) *
        F l (x l) * F i (x i)) = 0 := by
  classical
  let idx : Fin 4 → I := ![i,j,k,l]
  let f : Fin 4 → A → ℝ := fun t => F (idx t)
  have huniq : ∀ t ∈ (Finset.univ : Finset (Fin 4)), idx t = idx 0 → t = 0 := by
    intro t _ ht
    fin_cases t
    · rfl
    · have hji : j = i := by simpa [idx] using ht
      exact False.elim (hij hji.symm)
    · have hki : k = i := by simpa [idx] using ht
      exact False.elim (hik hki.symm)
    · have hli : l = i := by simpa [idx] using ht
      exact False.elim (hil hli.symm)
  have hzero : expect (μ (idx 0)) (f 0) = 0 := by
    simpa [f, idx] using hcenter i
  have h := expect_pi_indexed_prod_zero_unique μ Finset.univ idx f 0
    (Finset.mem_univ _) huniq hzero
  have hfun : (fun x : I → A =>
      F j (x j) * F k (x k) *
        F l (x l) * F i (x i)) =
      (fun x => ∏ t : Fin 4, f t (x (idx t))) := by
    funext x
    simp [f, idx, Fin.prod_univ_succ]
    ring
  rw [hfun]
  exact h

theorem pi_cross31 (μ : I → FiniteLaw A) (F : I → A → ℝ)
    (hcenter : ∀ i, expect (μ i) (F i) = 0) (s : Finset I) (i : I)
    (hi : i ∉ s) :
    expect (FiniteLaw.pi μ) (fun x =>
      (sumCentered (fun j x => F j (x j)) s x)^3 *
        F i (x i)) = 0 := by
  classical
  let X : I → (I → A) → ℝ := fun j x => F j (x j)
  have hpoint (x : I → A) :
      (sumCentered X s x)^3 * X i x =
        ∑ j ∈ s, ∑ k ∈ s, ∑ l ∈ s,
          X l x * X k x * X j x * X i x := by
    simp only [sumCentered]
    calc
      (∑ j ∈ s, X j x)^3 * X i x =
          (∑ j ∈ s, X j x) * (∑ k ∈ s, X k x) *
            (∑ l ∈ s, X l x) * X i x := by ring
      _ = _ := by simp only [Finset.sum_mul, Finset.mul_sum]
  change expect (FiniteLaw.pi μ) (fun x => (sumCentered X s x)^3 * X i x) = 0
  simp_rw [hpoint, expect_sum]
  apply Finset.sum_eq_zero
  intro j hj
  apply Finset.sum_eq_zero
  intro k hk
  apply Finset.sum_eq_zero
  intro l hl
  have hij : i ≠ j := fun h => hi (h ▸ hj)
  have hik : i ≠ k := fun h => hi (h ▸ hk)
  have hil : i ≠ l := fun h => hi (h ▸ hl)
  exact pi_centered_quad_zero_of_unique μ F hcenter i l k j hil hik hij

theorem pi_cross13 (μ : I → FiniteLaw A) (F : I → A → ℝ)
    (hcenter : ∀ i, expect (μ i) (F i) = 0) (s : Finset I) (i : I)
    (hi : i ∉ s) :
    expect (FiniteLaw.pi μ) (fun x =>
      sumCentered (fun j x => F j (x j)) s x *
        (F i (x i))^3) = 0 := by
  classical
  let X : I → (I → A) → ℝ := fun j x => F j (x j)
  have hpoint (x : I → A) :
      sumCentered X s x * (X i x)^3 =
        ∑ j ∈ s, X j x * (X i x)^3 := by
    simp only [sumCentered, Finset.sum_mul]
  change expect (FiniteLaw.pi μ) (fun x => sumCentered X s x * (X i x)^3) = 0
  simp_rw [hpoint, expect_sum]
  apply Finset.sum_eq_zero
  intro j hj
  have hji : j ≠ i := fun h => hi (h.symm ▸ hj)
  have h := pi_centered_quad_zero_of_unique μ F hcenter j i i i hji hji hji
  convert h using 1
  congr 1
  funext x
  ring

/-- Full product independence of one isolated coordinate, for an arbitrary
product of scalar tests on the remaining coordinates. -/
theorem expect_pi_mul_isolated (μ : I → FiniteLaw A)
    (G : I → A → ℝ) (i : I) (g : A → ℝ)
    (hGi : ∀ b, G i b = 1) :
    expect (FiniteLaw.pi μ) (fun x => (∏ r, G r (x r)) * g (x i)) =
      expect (FiniteLaw.pi μ) (fun x => ∏ r, G r (x r)) *
        expect (μ i) g := by
  classical
  have hpoint (x : I → A) :
      (∏ r, G r (x r)) * g (x i) =
        ∏ r, G r (x r) * (if r = i then g (x r) else 1) := by
    rw [Finset.prod_mul_distrib]
    simp
  simp_rw [hpoint]
  rw [expect_pi_prod μ (fun r b => G r b * (if r = i then g b else 1))]
  rw [expect_pi_prod μ G]
  have hfactor (r : I) :
      expect (μ r) (fun b => G r b * (if r = i then g b else 1)) =
        expect (μ r) (G r) * (if r = i then expect (μ i) g else 1) := by
    by_cases h : r = i
    · subst r
      simp only [ite_true, hGi, one_mul]
      rw [show expect (μ i) (G i) = 1 by
        have hfun : G i = fun _ => 1 := funext hGi
        rw [hfun]
        exact expect_one (μ i)]
      ring
    · simp only [h, ↓reduceIte, mul_one]
  simp_rw [hfactor]
  rw [Finset.prod_mul_distrib]
  simp

theorem expect_pi_coordinate (μ : I → FiniteLaw A)
    (i : I) (g : A → ℝ) :
    expect (FiniteLaw.pi μ) (fun x => g (x i)) = expect (μ i) g := by
  classical
  let G : I → A → ℝ := fun r b => if r = i then g b else 1
  have hpoint (x : I → A) : (∏ r, G r (x r)) = g (x i) := by
    simp [G]
  have h := expect_pi_prod μ G
  simp only [hpoint] at h
  have hother (r : I) : expect (μ r) (G r) =
      if r = i then expect (μ i) g else 1 := by
    by_cases hr : r = i
    · subst r; simp [G]
    · simp [G, hr, expect_one]
  simp_rw [hother] at h
  simpa using h

theorem pi_pair_factor (μ : I → FiniteLaw A) (F : I → A → ℝ) (i j k : I)
    (hij : i ≠ j) (hik : i ≠ k) :
    expect (FiniteLaw.pi μ) (fun x =>
      F j (x j) * F k (x k) *
        (F i (x i))^2) =
      expect (FiniteLaw.pi μ) (fun x =>
        F j (x j) * F k (x k)) *
      expect (FiniteLaw.pi μ) (fun x => (F i (x i))^2) := by
  classical
  let G : I → A → ℝ := fun r b =>
    (if r = j then F j b else 1) *
      (if r = k then F k b else 1)
  have hGi (b : A) : G i b = 1 := by simp [G, hij, hik]
  have hGprod (x : I → A) : (∏ r, G r (x r)) =
      F j (x j) * F k (x k) := by
    change (∏ r, (if r = j then F j (x r) else 1) *
      (if r = k then F k (x r) else 1)) = _
    rw [Finset.prod_mul_distrib]
    simp
  have h := expect_pi_mul_isolated μ G i
    (fun b => (F i b)^2) hGi
  simp_rw [hGprod] at h
  rw [← expect_pi_coordinate μ i (fun b => (F i b)^2)] at h
  convert h using 1

theorem pi_cross22 (μ : I → FiniteLaw A) (F : I → A → ℝ) (s : Finset I) (i : I)
    (hi : i ∉ s) :
    expect (FiniteLaw.pi μ) (fun x =>
      (sumCentered (fun j x => F j (x j)) s x)^2 *
        (F i (x i))^2) =
    expect (FiniteLaw.pi μ) (fun x =>
      (sumCentered (fun j x => F j (x j)) s x)^2) *
    expect (FiniteLaw.pi μ) (fun x => (F i (x i))^2) := by
  classical
  let X : I → (I → A) → ℝ := fun j x => F j (x j)
  let ρ := FiniteLaw.pi μ
  have hsquare (x : I → A) :
      (sumCentered X s x)^2 = ∑ j ∈ s, ∑ k ∈ s, X k x * X j x := by
    simp only [sumCentered]
    calc
      (∑ j ∈ s, X j x)^2 =
          (∑ j ∈ s, X j x) * (∑ k ∈ s, X k x) := by ring
      _ = _ := by simp only [Finset.sum_mul, Finset.mul_sum]
  change expect ρ (fun x => (sumCentered X s x)^2 * (X i x)^2) =
    expect ρ (fun x => (sumCentered X s x)^2) *
      expect ρ (fun x => (X i x)^2)
  have hleft : expect ρ (fun x => (sumCentered X s x)^2 * (X i x)^2) =
      ∑ j ∈ s, ∑ k ∈ s,
        expect ρ (fun x => X k x * X j x * (X i x)^2) := by
    have hpoint (x : I → A) :
        (sumCentered X s x)^2 * (X i x)^2 =
          ∑ j ∈ s, ∑ k ∈ s, X k x * X j x * (X i x)^2 := by
      rw [hsquare]
      simp only [Finset.sum_mul]
    simp_rw [hpoint, expect_sum]
  have hright : expect ρ (fun x => (sumCentered X s x)^2) =
      ∑ j ∈ s, ∑ k ∈ s, expect ρ (fun x => X k x * X j x) := by
    simp_rw [hsquare, expect_sum]
  rw [hleft, hright]
  simp only [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro k hk
  have hik : i ≠ k := fun h => hi (h ▸ hk)
  have hij : i ≠ j := fun h => hi (h ▸ hj)
  exact pi_pair_factor μ F i k j hik hij

theorem pi_centered_pair_zero (μ : I → FiniteLaw A) (F : I → A → ℝ)
    (hcenter : ∀ i, expect (μ i) (F i) = 0) (i j : I)
    (hij : i ≠ j) :
    expect (FiniteLaw.pi μ) (fun x =>
      F j (x j) * F i (x i)) = 0 := by
  classical
  let idx : Fin 2 → I := ![i,j]
  let f : Fin 2 → A → ℝ := fun t => F (idx t)
  have huniq : ∀ t ∈ (Finset.univ : Finset (Fin 2)), idx t = idx 0 → t = 0 := by
    intro t _ ht
    fin_cases t
    · rfl
    · have hji : j = i := by simpa [idx] using ht
      exact False.elim (hij hji.symm)
  have hzero : expect (μ (idx 0)) (f 0) = 0 := by
    simpa [f, idx] using hcenter i
  have h := expect_pi_indexed_prod_zero_unique μ Finset.univ idx f 0
    (Finset.mem_univ _) huniq hzero
  have hfun : (fun x : I → A => F j (x j) * F i (x i)) =
      (fun x => ∏ t : Fin 2, f t (x (idx t))) := by
    funext x
    simp [f, idx, Fin.prod_univ_succ]
    ring
  rw [hfun]
  exact h

theorem pi_cross1 (μ : I → FiniteLaw A) (F : I → A → ℝ)
    (hcenter : ∀ i, expect (μ i) (F i) = 0) (s : Finset I) (i : I)
    (hi : i ∉ s) :
    expect (FiniteLaw.pi μ) (fun x =>
      sumCentered (fun j x => F j (x j)) s x *
        F i (x i)) = 0 := by
  classical
  let X : I → (I → A) → ℝ := fun j x => F j (x j)
  have hpoint (x : I → A) :
      sumCentered X s x * X i x = ∑ j ∈ s, X j x * X i x := by
    simp [sumCentered, Finset.sum_mul]
  change expect (FiniteLaw.pi μ) (fun x => sumCentered X s x * X i x) = 0
  simp_rw [hpoint, expect_sum]
  apply Finset.sum_eq_zero
  intro j hj
  have hij : i ≠ j := fun h => hi (h ▸ hj)
  exact pi_centered_pair_zero μ F hcenter i j hij

theorem pairCrossMoments_product (μ : I → FiniteLaw A) (F : I → A → ℝ)
    (hcenter : ∀ i, expect (μ i) (F i) = 0) :
    PairCrossMoments (FiniteLaw.pi μ)
      (fun i x => F i (x i)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro s i hi; exact pi_cross1 μ F hcenter s i hi
  · intro s i hi; exact pi_cross31 μ F hcenter s i hi
  · intro s i hi; exact pi_cross13 μ F hcenter s i hi
  · intro s i hi; exact pi_cross22 μ F s i hi


#print axioms pairCrossMoments_product
end GeneralCross
