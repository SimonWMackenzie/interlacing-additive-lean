import CurrentAdditive.ProductFourth

namespace CurrentAdditive.FourthMoment

open Paper2

variable {Ψ I : Type*} [Fintype Ψ] [Fintype I] [DecidableEq I]

/-- Push the product fourth-moment estimate through an exact law for the
whole vector of Boolean pair tests. -/
theorem fourth_bound_of_indicator_law
    (ρ : FiniteLaw Ψ) (Z : I → Ψ → Bool)
    (μ : I → FiniteLaw Bool)
    (hprob : ∀ E : (I → Bool) → Prop,
      ρ.prob (fun ψ => E (fun i => Z i ψ)) =
        (FiniteLaw.pi μ).prob E)
    (s : Finset I) :
    expect ρ (fun ψ => (∑ i ∈ s, boolCentered μ i (Z i ψ)) ^ 4) ≤
      (s.card : ℝ) / 4 + 3 * (s.card : ℝ) ^ 2 / 16 := by
  let d : Ψ → I → Bool := fun ψ i => Z i ψ
  let f : (I → Bool) → ℝ := fun x => (∑ i ∈ s, boolCentered μ i (x i)) ^ 4
  have ht : expect ρ (fun ψ => f (d ψ)) = expect (FiniteLaw.pi μ) f :=
    expect_eq_of_prob_preimage ρ (FiniteLaw.pi μ) d hprob f
  calc
    expect ρ (fun ψ => (∑ i ∈ s, boolCentered μ i (Z i ψ)) ^ 4) =
        expect (FiniteLaw.pi μ) f := ht
    _ ≤ (s.card : ℝ) / 4 + 3 * (s.card : ℝ) ^ 2 / 16 :=
      product_centered_fourth_bound μ s

#print axioms fourth_bound_of_indicator_law

end CurrentAdditive.FourthMoment
