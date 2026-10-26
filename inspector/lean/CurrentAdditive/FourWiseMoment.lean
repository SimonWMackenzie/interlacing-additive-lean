import CurrentAdditive.ProductFourth

namespace CurrentAdditive.FourthMoment

open Paper2
open scoped BigOperators

variable {Ψ I : Type*} [Fintype Ψ] [Fintype I] [DecidableEq I]

/-- Exact fourth centered moment for any finite Boolean vector whose
restrictions to at most four coordinates have the heterogeneous Bernoulli
product law. Repeated indices in an ordered quartic term cause no issue:
its support is the image of four positions. -/
theorem fourth_moment_eq_product_of_four_wise
    (ρ : FiniteLaw Ψ) (Z : I → Ψ → Bool) (μ : I → FiniteLaw Bool)
    (hjoint : ∀ (s : Finset I), s.card ≤ 4 →
      ∀ E : (s → Bool) → Prop,
        ρ.prob (fun ψ => E (fun j : s => Z j.val ψ)) =
          (FiniteLaw.pi (fun j : s => μ j.val)).prob E) :
    expect ρ (fun ψ =>
      (∑ i : I, boolCentered μ i (Z i ψ)) ^ 4) =
    expect (FiniteLaw.pi μ) (fun x =>
      (∑ i : I, boolCentered μ i (x i)) ^ 4) := by
  classical
  have hterm (k : Fin 4 → I) :
      expect ρ (fun ψ => ∏ j : Fin 4,
        boolCentered μ (k j) (Z (k j) ψ)) =
      expect (FiniteLaw.pi μ) (fun x => ∏ j : Fin 4,
        boolCentered μ (k j) (x (k j))) := by
    let s : Finset I := Finset.univ.image k
    have hcard : s.card ≤ 4 := by
      simpa [s] using (Finset.card_image_le (s := Finset.univ) (f := k))
    have hmem (j : Fin 4) : k j ∈ s :=
      Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩
    let G : (s → Bool) → ℝ := fun b => ∏ j : Fin 4,
      boolCentered μ (k j) (b ⟨k j, hmem j⟩)
    have hsource : expect ρ (fun ψ => G (fun i : s => Z i.val ψ)) =
        expect (FiniteLaw.pi (fun i : s => μ i.val)) G :=
      expect_eq_of_prob_preimage ρ
        (FiniteLaw.pi (fun i : s => μ i.val))
        (fun ψ i => Z i.val ψ) (hjoint s hcard) G
    have hproduct : expect (FiniteLaw.pi μ)
        (fun x => G (fun i : s => x i.val)) =
        expect (FiniteLaw.pi (fun i : s => μ i.val)) G :=
      expect_eq_of_prob_preimage (FiniteLaw.pi μ)
        (FiniteLaw.pi (fun i : s => μ i.val))
        (fun x i => x i.val)
        (FiniteLaw.pi_prob_restrict μ (fun i : s => i.val)
          Subtype.val_injective) G
    exact hsource.trans hproduct.symm
  have hactual (ψ : Ψ) :
      (∑ i : I, boolCentered μ i (Z i ψ)) ^ 4 =
      ∑ k : Fin 4 → I, ∏ j : Fin 4,
        boolCentered μ (k j) (Z (k j) ψ) := by
    exact Fintype.sum_pow _ _
  have hproxy (x : I → Bool) :
      (∑ i : I, boolCentered μ i (x i)) ^ 4 =
      ∑ k : Fin 4 → I, ∏ j : Fin 4,
        boolCentered μ (k j) (x (k j)) := by
    exact Fintype.sum_pow _ _
  simp_rw [hactual, hproxy]
  unfold expect
  simp only [Finset.mul_sum]
  conv_lhs => rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  simpa only [expect] using hterm k

/-- The finite-law fourth centered moment bound under four-wise Boolean
indicator independence. -/
theorem fourth_bound_of_four_wise
    (ρ : FiniteLaw Ψ) (Z : I → Ψ → Bool) (μ : I → FiniteLaw Bool)
    (hjoint : ∀ (s : Finset I), s.card ≤ 4 →
      ∀ E : (s → Bool) → Prop,
        ρ.prob (fun ψ => E (fun j : s => Z j.val ψ)) =
          (FiniteLaw.pi (fun j : s => μ j.val)).prob E) :
    expect ρ (fun ψ =>
      (∑ i : I, boolCentered μ i (Z i ψ)) ^ 4) ≤
      (Fintype.card I : ℝ) / 4 +
        3 * (Fintype.card I : ℝ) ^ 2 / 16 := by
  calc
    _ = expect (FiniteLaw.pi μ) (fun x =>
          (∑ i : I, boolCentered μ i (x i)) ^ 4) :=
      fourth_moment_eq_product_of_four_wise ρ Z μ hjoint
    _ ≤ _ := by
      simpa only [Finset.card_univ] using
        product_centered_fourth_bound μ Finset.univ

#print axioms fourth_bound_of_four_wise

end CurrentAdditive.FourthMoment
