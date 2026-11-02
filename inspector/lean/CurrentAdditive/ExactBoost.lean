import CurrentAdditive.ExactSuffixAll

/-! Appendix H `det:exact`: the actual cost minimizer, arbitrary-speaker
fixed-depth prefix, and complete exact eight-wise suffix contradiction. -/

namespace CurrentAdditive.ArbitraryPrefix

open Paper2

variable {X Z S : Type*} [Fintype X] [Fintype Z] [Fintype S]

theorem exactboost
    (μ : PositiveRationalLaw X) (ν : PositiveRationalLaw Z)
    (F : X → Z → Bool) (source : FiniteLaw S)
    {q : ℕ} (decode : S → Fin q → Z)
    (hwise : IsDWise 8 source decode ν.toFiniteLaw)
    (Good : Finset (Fin q)) (Rows : Fin q → Set X) (K : Set S)
    (d a : ℕ) (x : ℝ)
    (ha : 1 ≤ a) (hd : 2 ≤ d) (hx : 0 < x)
    (hscale : (2 : ℝ)^a * x ≤ 1)
    (hprofile : RestrictionProfile F μ.toFiniteLaw ν.toFiniteLaw x (d : ℤ))
    (hcount : 2^(a-1)+1 ≤ Good.card)
    (hrow : ∀ i ∈ Good, (2 : ℝ)^a*x ≤ μ.toFiniteLaw.prob (· ∈ Rows i))
    (hK : (9/25 : ℝ) ≤ source.prob (· ∈ K)) :
    d+a ≤ Paper2.Compression.restrictionD
      (fun a s => F a.2 (decode s a.1)) (rowRectangle Good Rows) K := by
  let G : (Fin q × X) → S → Bool := fun a s => F a.2 (decode s a.1)
  let D := Paper2.Compression.restrictionD G (rowRectangle Good Rows) K
  by_contra hn
  change ¬ (d+a ≤ D) at hn
  have hD : D ≤ d+a-1 := by omega
  obtain ⟨A, B, Good', Rows', K', P', hab, hcount', hrow', hcol',
    hGoodsub, hRowssub, hKsub, hcost, heval⟩ :=
    exact_prefix_state μ.toFiniteLaw source G Good Rows K d a x
      ha hx hcount hrow hK hD
  have hscale' : (2 : ℝ)^(B+1) * x ≤ 1 := by
    have hp : (2 : ℝ)^(B+1) ≤ (2 : ℝ)^a :=
      pow_le_pow_right₀ (by norm_num) (by omega)
    exact (mul_le_mul_of_nonneg_right hp hx.le).trans hscale
  have hlower := exact_suffix_all μ ν F source decode hwise
    Good' hcount' Rows' K' d x hd hx hscale' hprofile hrow' hcol'
  have hupper : Paper2.Compression.restrictionD G
      (rowRectangle Good' Rows') K' ≤ d :=
    residual_restriction_upper G Good' Rows' K' P' d hcost heval
  change d+1 ≤ Paper2.Compression.restrictionD G
    (rowRectangle Good' Rows') K' at hlower
  omega

#print axioms CurrentAdditive.ArbitraryPrefix.exactboost

end CurrentAdditive.ArbitraryPrefix
