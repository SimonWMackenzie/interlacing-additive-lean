import CurrentAdditive.ProductCross

namespace CurrentAdditive.FourthMoment

open Paper2

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- Fourth centered moment of the finite heterogeneous Bernoulli product law.
The estimate follows from the one-coordinate Bernoulli bounds and the
product-law cross identities proved above. -/
theorem product_centered_fourth_bound (μ : I → FiniteLaw Bool) (s : Finset I) :
    expect (FiniteLaw.pi μ)
      (fun x => (∑ i ∈ s, boolCentered μ i (x i)) ^ 4) ≤
      (s.card : ℝ) / 4 + 3 * (s.card : ℝ) ^ 2 / 16 := by
  let X : I → (I → Bool) → ℝ := fun i x => boolCentered μ i (x i)
  have hsecond : ∀ i, expect (FiniteLaw.pi μ) (fun x => (X i x)^2) ≤ 1/4 := by
    intro i
    calc
      expect (FiniteLaw.pi μ) (fun x => (X i x)^2) =
          expect (μ i) (fun b => (boolCentered μ i b)^2) :=
        expect_pi_coordinate μ i (fun b => (boolCentered μ i b)^2)
      _ ≤ 1/4 := by
        simpa only [boolCentered] using
          centered_indicator_second_le_quarter (μ i) (fun b => b = true)
  have hfourth : ∀ i, expect (FiniteLaw.pi μ) (fun x => (X i x)^4) ≤ 1/4 := by
    intro i
    calc
      expect (FiniteLaw.pi μ) (fun x => (X i x)^4) =
          expect (μ i) (fun b => (boolCentered μ i b)^4) :=
        expect_pi_coordinate μ i (fun b => (boolCentered μ i b)^4)
      _ ≤ 1/4 := by
        simpa only [boolCentered] using
          centered_indicator_fourth_le_quarter (μ i) (fun b => b = true)
  have hcross := pairCrossMoments_product μ
  have h := fourth_bound_of_cross_moments (FiniteLaw.pi μ) X
    hsecond hfourth hcross.cross1 hcross.cross31 hcross.cross13 hcross.cross22 s
  simpa only [X, sumCentered, Finset.sum_congr] using h.2

#print axioms product_centered_fourth_bound

end CurrentAdditive.FourthMoment
