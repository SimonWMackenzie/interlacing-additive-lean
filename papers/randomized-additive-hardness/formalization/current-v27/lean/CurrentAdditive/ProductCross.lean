import CurrentAdditive.FourthMoment

namespace CurrentAdditive.FourthMoment

open Paper2
open scoped BigOperators

variable {I : Type*} [Fintype I] [DecidableEq I]

noncomputable def boolCentered (μ : I → FiniteLaw Bool)
    (i : I) (b : Bool) : ℝ :=
  (if b then 1 else 0) - (μ i).prob (fun z => z = true)

private theorem boolCentered_mean_zero (μ : I → FiniteLaw Bool) (i : I) :
    expect (μ i) (boolCentered μ i) = 0 := by
  exact expect_centered_indicator (μ i) (fun z => z = true)

theorem pi_centered_quad_zero_of_unique
    (μ : I → FiniteLaw Bool) (i j k l : I)
    (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l) :
    expect (FiniteLaw.pi μ) (fun x =>
      boolCentered μ j (x j) * boolCentered μ k (x k) *
        boolCentered μ l (x l) * boolCentered μ i (x i)) = 0 := by
  classical
  let idx : Fin 4 → I := ![i,j,k,l]
  let f : Fin 4 → Bool → ℝ := fun t => boolCentered μ (idx t)
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
    simpa [f, idx] using boolCentered_mean_zero μ i
  have h := expect_pi_indexed_prod_zero_unique μ Finset.univ idx f 0
    (Finset.mem_univ _) huniq hzero
  have hfun : (fun x : I → Bool =>
      boolCentered μ j (x j) * boolCentered μ k (x k) *
        boolCentered μ l (x l) * boolCentered μ i (x i)) =
      (fun x => ∏ t : Fin 4, f t (x (idx t))) := by
    funext x
    simp [f, idx, Fin.prod_univ_succ]
    ring
  rw [hfun]
  exact h

theorem pi_cross31 (μ : I → FiniteLaw Bool) (s : Finset I) (i : I)
    (hi : i ∉ s) :
    expect (FiniteLaw.pi μ) (fun x =>
      (sumCentered (fun j x => boolCentered μ j (x j)) s x)^3 *
        boolCentered μ i (x i)) = 0 := by
  classical
  let X : I → (I → Bool) → ℝ := fun j x => boolCentered μ j (x j)
  have hpoint (x : I → Bool) :
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
  exact pi_centered_quad_zero_of_unique μ i l k j hil hik hij

theorem pi_cross13 (μ : I → FiniteLaw Bool) (s : Finset I) (i : I)
    (hi : i ∉ s) :
    expect (FiniteLaw.pi μ) (fun x =>
      sumCentered (fun j x => boolCentered μ j (x j)) s x *
        (boolCentered μ i (x i))^3) = 0 := by
  classical
  let X : I → (I → Bool) → ℝ := fun j x => boolCentered μ j (x j)
  have hpoint (x : I → Bool) :
      sumCentered X s x * (X i x)^3 =
        ∑ j ∈ s, X j x * (X i x)^3 := by
    simp only [sumCentered, Finset.sum_mul]
  change expect (FiniteLaw.pi μ) (fun x => sumCentered X s x * (X i x)^3) = 0
  simp_rw [hpoint, expect_sum]
  apply Finset.sum_eq_zero
  intro j hj
  have hji : j ≠ i := fun h => hi (h.symm ▸ hj)
  have h := pi_centered_quad_zero_of_unique μ j i i i hji hji hji
  convert h using 1
  congr 1
  funext x
  ring

/-- Full product independence of one isolated coordinate, for an arbitrary
product of scalar tests on the remaining coordinates. -/
theorem expect_pi_mul_isolated (μ : I → FiniteLaw Bool)
    (G : I → Bool → ℝ) (i : I) (g : Bool → ℝ)
    (hGi : ∀ b, G i b = 1) :
    expect (FiniteLaw.pi μ) (fun x => (∏ r, G r (x r)) * g (x i)) =
      expect (FiniteLaw.pi μ) (fun x => ∏ r, G r (x r)) *
        expect (μ i) g := by
  classical
  have hpoint (x : I → Bool) :
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

theorem expect_pi_coordinate (μ : I → FiniteLaw Bool)
    (i : I) (g : Bool → ℝ) :
    expect (FiniteLaw.pi μ) (fun x => g (x i)) = expect (μ i) g := by
  classical
  let G : I → Bool → ℝ := fun r b => if r = i then g b else 1
  have hpoint (x : I → Bool) : (∏ r, G r (x r)) = g (x i) := by
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

theorem pi_pair_factor (μ : I → FiniteLaw Bool) (i j k : I)
    (hij : i ≠ j) (hik : i ≠ k) :
    expect (FiniteLaw.pi μ) (fun x =>
      boolCentered μ j (x j) * boolCentered μ k (x k) *
        (boolCentered μ i (x i))^2) =
      expect (FiniteLaw.pi μ) (fun x =>
        boolCentered μ j (x j) * boolCentered μ k (x k)) *
      expect (FiniteLaw.pi μ) (fun x => (boolCentered μ i (x i))^2) := by
  classical
  let G : I → Bool → ℝ := fun r b =>
    (if r = j then boolCentered μ j b else 1) *
      (if r = k then boolCentered μ k b else 1)
  have hGi (b : Bool) : G i b = 1 := by simp [G, hij, hik]
  have hGprod (x : I → Bool) : (∏ r, G r (x r)) =
      boolCentered μ j (x j) * boolCentered μ k (x k) := by
    change (∏ r, (if r = j then boolCentered μ j (x r) else 1) *
      (if r = k then boolCentered μ k (x r) else 1)) = _
    rw [Finset.prod_mul_distrib]
    simp
  have h := expect_pi_mul_isolated μ G i
    (fun b => (boolCentered μ i b)^2) hGi
  simp_rw [hGprod] at h
  rw [← expect_pi_coordinate μ i (fun b => (boolCentered μ i b)^2)] at h
  convert h using 1

theorem pi_cross22 (μ : I → FiniteLaw Bool) (s : Finset I) (i : I)
    (hi : i ∉ s) :
    expect (FiniteLaw.pi μ) (fun x =>
      (sumCentered (fun j x => boolCentered μ j (x j)) s x)^2 *
        (boolCentered μ i (x i))^2) =
    expect (FiniteLaw.pi μ) (fun x =>
      (sumCentered (fun j x => boolCentered μ j (x j)) s x)^2) *
    expect (FiniteLaw.pi μ) (fun x => (boolCentered μ i (x i))^2) := by
  classical
  let X : I → (I → Bool) → ℝ := fun j x => boolCentered μ j (x j)
  let ρ := FiniteLaw.pi μ
  have hsquare (x : I → Bool) :
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
    have hpoint (x : I → Bool) :
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
  exact pi_pair_factor μ i k j hik hij

theorem pi_centered_pair_zero (μ : I → FiniteLaw Bool) (i j : I)
    (hij : i ≠ j) :
    expect (FiniteLaw.pi μ) (fun x =>
      boolCentered μ j (x j) * boolCentered μ i (x i)) = 0 := by
  classical
  let idx : Fin 2 → I := ![i,j]
  let f : Fin 2 → Bool → ℝ := fun t => boolCentered μ (idx t)
  have huniq : ∀ t ∈ (Finset.univ : Finset (Fin 2)), idx t = idx 0 → t = 0 := by
    intro t _ ht
    fin_cases t
    · rfl
    · have hji : j = i := by simpa [idx] using ht
      exact False.elim (hij hji.symm)
  have hzero : expect (μ (idx 0)) (f 0) = 0 := by
    simpa [f, idx] using boolCentered_mean_zero μ i
  have h := expect_pi_indexed_prod_zero_unique μ Finset.univ idx f 0
    (Finset.mem_univ _) huniq hzero
  have hfun : (fun x : I → Bool => boolCentered μ j (x j) * boolCentered μ i (x i)) =
      (fun x => ∏ t : Fin 2, f t (x (idx t))) := by
    funext x
    simp [f, idx, Fin.prod_univ_succ]
    ring
  rw [hfun]
  exact h

theorem pi_cross1 (μ : I → FiniteLaw Bool) (s : Finset I) (i : I)
    (hi : i ∉ s) :
    expect (FiniteLaw.pi μ) (fun x =>
      sumCentered (fun j x => boolCentered μ j (x j)) s x *
        boolCentered μ i (x i)) = 0 := by
  classical
  let X : I → (I → Bool) → ℝ := fun j x => boolCentered μ j (x j)
  have hpoint (x : I → Bool) :
      sumCentered X s x * X i x = ∑ j ∈ s, X j x * X i x := by
    simp [sumCentered, Finset.sum_mul]
  change expect (FiniteLaw.pi μ) (fun x => sumCentered X s x * X i x) = 0
  simp_rw [hpoint, expect_sum]
  apply Finset.sum_eq_zero
  intro j hj
  have hij : i ≠ j := fun h => hi (h ▸ hj)
  exact pi_centered_pair_zero μ i j hij

theorem pairCrossMoments_product (μ : I → FiniteLaw Bool) :
    PairCrossMoments (FiniteLaw.pi μ)
      (fun i x => boolCentered μ i (x i)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro s i hi; exact pi_cross1 μ s i hi
  · intro s i hi; exact pi_cross31 μ s i hi
  · intro s i hi; exact pi_cross13 μ s i hi
  · intro s i hi; exact pi_cross22 μ s i hi

/-- The same cross identities hold for any ambient law whose full vector of
pair indicators has the heterogeneous Bernoulli product distribution. The
premise is an exact event law, not a moment bound or independence certificate
about the source being conditioned. -/
theorem pairCrossMoments_of_indicator_law
    {Ψ : Type*} [Fintype Ψ]
    (ρ : FiniteLaw Ψ) (Z : I → Ψ → Bool)
    (μ : I → FiniteLaw Bool)
    (hprob : ∀ E : (I → Bool) → Prop,
      ρ.prob (fun ψ => E (fun i => Z i ψ)) =
        (FiniteLaw.pi μ).prob E) :
    PairCrossMoments ρ
      (fun i ψ => boolCentered μ i (Z i ψ)) := by
  let d : Ψ → I → Bool := fun ψ i => Z i ψ
  let X : I → (I → Bool) → ℝ := fun i x => boolCentered μ i (x i)
  have ht (f : (I → Bool) → ℝ) :
      expect ρ (fun ψ => f (d ψ)) = expect (FiniteLaw.pi μ) f :=
    expect_eq_of_prob_preimage ρ (FiniteLaw.pi μ) d hprob f
  have hprod := pairCrossMoments_product μ
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro s i hi
    simpa only [d, X, sumCentered] using
      (ht (fun x => sumCentered X s x * X i x)).trans (hprod.cross1 s i hi)
  · intro s i hi
    simpa only [d, X, sumCentered] using
      (ht (fun x => (sumCentered X s x)^3 * X i x)).trans
        (hprod.cross31 s i hi)
  · intro s i hi
    simpa only [d, X, sumCentered] using
      (ht (fun x => sumCentered X s x * (X i x)^3)).trans
        (hprod.cross13 s i hi)
  · intro s i hi
    have hleft := ht (fun x => (sumCentered X s x)^2 * (X i x)^2)
    have hsq := ht (fun x => (sumCentered X s x)^2)
    have hsingle := ht (fun x => (X i x)^2)
    simpa only [d, X, sumCentered] using
      hleft.trans ((hprod.cross22 s i hi).trans
        (congrArg₂ (· * ·) hsq.symm hsingle.symm))

#print axioms pi_centered_quad_zero_of_unique

end CurrentAdditive.FourthMoment
