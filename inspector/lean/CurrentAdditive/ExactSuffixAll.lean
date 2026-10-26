import CurrentAdditive.ExactSelectedLaw

/-! The exact eight-wise suffix, split at the manuscript's four short
parameter values and the checked four-wise pair-tail for all larger values. -/

namespace CurrentAdditive.ArbitraryPrefix

open Paper2

variable {X Z S : Type*} [Fintype X] [Fintype Z] [Fintype S]

theorem exact_suffix_all
    (μ : PositiveRationalLaw X) (ν : PositiveRationalLaw Z)
    (F : X → Z → Bool) (source : FiniteLaw S)
    {q b : ℕ} (decode : S → Fin q → Z)
    (hwise : IsDWise 8 source decode ν.toFiniteLaw)
    (Good : Finset (Fin q)) (hGood : 2^b+1 ≤ Good.card)
    (Rows : Fin q → Set X) (K : Set S)
    (d : ℕ) (x : ℝ) (hd : 2 ≤ d) (hx : 0 < x)
    (hscale : (2 : ℝ)^(b+1)*x ≤ 1)
    (hprofile : RestrictionProfile F μ.toFiniteLaw ν.toFiniteLaw x (d : ℤ))
    (hrow : ∀ i ∈ Good, (2 : ℝ)^(b+1)*x ≤ μ.toFiniteLaw.prob (· ∈ Rows i))
    (hK : (9/25 : ℝ)/(2 : ℝ)^b ≤ source.prob (· ∈ K)) :
    d+1 ≤ Paper2.Compression.restrictionD
      (fun a s => F a.2 (decode s a.1)) (rowRectangle Good Rows) K := by
  by_cases hb : b ≤ 3
  · interval_cases b
    · have hc : 2 ≤ Good.card := by simpa using hGood
      apply exact_suffix_zero μ ν F source decode Good hc Rows K d x
        hd hx (by simpa using hscale) hprofile
      · intro i hi
        simpa using hrow i hi
      · simpa using hK
      · intro e he P
        exact exact_selected_of_eight source ν.toFiniteLaw decode hwise
          (by omega) e he P
    · have hc : 3 ≤ Good.card := by simpa using hGood
      norm_num at hscale hrow hK
      apply exact_suffix_one μ ν F source decode Good hc Rows K d x
        hd hx hscale hprofile hrow hK
      intro e he P
      exact exact_selected_of_eight source ν.toFiniteLaw decode hwise
        (by omega) e he P
    · have hc : 5 ≤ Good.card := by simpa using hGood
      norm_num at hscale hrow hK
      apply exact_suffix_two μ ν F source decode Good hc Rows K d x
        hd hx hscale hprofile hrow hK
      intro e he P
      exact exact_selected_of_eight source ν.toFiniteLaw decode hwise
        (by omega) e he P
    · have hc : 8 ≤ Good.card := by omega
      norm_num at hscale hrow hK
      apply exact_suffix_three μ ν F source decode Good hc Rows K d x
        hd hx hscale hprofile hrow hK
      intro e he P
      exact exact_selected_of_eight source ν.toFiniteLaw decode hwise
        (by omega) e he P
  · have hb4 : 4 ≤ b := by omega
    exact exact_suffix_long_eight μ ν F source hb4 decode hwise
      Good hGood Rows K d x hd hx hscale hprofile hrow hK

#print axioms CurrentAdditive.ArbitraryPrefix.exact_suffix_all

end CurrentAdditive.ArbitraryPrefix
