import CurrentAdditive.V39SuffixShort
import CurrentAdditive.V38ExactSuffixLong
import CurrentAdditive.V38Fin2PrefixGeneric

/-! Selected v39 `det:exact`, with the current two-threshold restriction
profile.  Its suffix proof uses the current pair/triple base results and
original-law eight-wise independence; no third profile rung is assumed. -/

namespace CurrentAdditive.V38Fin2Exact

open Paper2 CurrentAdditive.ArbitraryPrefix

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
    (hprofile : V38RestrictionProfiles.TwoThresholdProfile F
      μ.toFiniteLaw ν.toFiniteLaw x (d : ℤ))
    (hrow : ∀ i ∈ Good, (2 : ℝ)^(b+1)*x ≤ μ.toFiniteLaw.prob (· ∈ Rows i))
    (hK : (9/25 : ℝ)/(2 : ℝ)^b ≤ source.prob (· ∈ K)) :
    d+1 ≤ Compression.restrictionD
      (fun a s => F a.2 (decode s a.1)) (rowRectangle Good Rows) K := by
  by_cases hb : b ≤ 4
  · exact V38RareBoost.exact_suffix_short_two_threshold μ.toFiniteLaw ν F
      source hb decode hwise Good hGood Rows K d x hd hx hprofile hrow hK
  · exact V38RareBoost.exact_suffix_long_eight μ ν F source (by omega)
      decode hwise Good hGood Rows K d x hd hx hscale hprofile hrow hK

theorem exactboost
    (μ : PositiveRationalLaw X) (ν : PositiveRationalLaw Z)
    (F : X → Z → Bool) (source : FiniteLaw S)
    {q : ℕ} (decode : S → Fin q → Z)
    (hwise : IsDWise 8 source decode ν.toFiniteLaw)
    (Good : Finset (Fin q)) (Rows : Fin q → Set X) (K : Set S)
    (d a : ℕ) (x : ℝ)
    (ha : 1 ≤ a) (hd : 2 ≤ d) (hx : 0 < x)
    (hscale : (2 : ℝ)^a*x ≤ 1)
    (hprofile : V38RestrictionProfiles.TwoThresholdProfile F
      μ.toFiniteLaw ν.toFiniteLaw x (d : ℤ))
    (hcount : 2^(a-1)+1 ≤ Good.card)
    (hrow : ∀ i ∈ Good, (2 : ℝ)^a*x ≤ μ.toFiniteLaw.prob (· ∈ Rows i))
    (hK : (9/25 : ℝ) ≤ source.prob (· ∈ K)) :
    d+a ≤ Compression.restrictionD
      (fun a s => F a.2 (decode s a.1)) (rowRectangle Good Rows) K := by
  let G : (Fin q × X) → S → Bool := fun a s => F a.2 (decode s a.1)
  let D := Compression.restrictionD G (rowRectangle Good Rows) K
  by_contra hn
  change ¬ (d+a ≤ D) at hn
  have hD : D ≤ d+a-1 := by omega
  obtain ⟨A, B, Good', Rows', K', P', hab, hcount', hrow', hcol',
    hGoodsub, hRowssub, hKsub, hcost, heval⟩ :=
    exact_prefix_state μ.toFiniteLaw source G Good Rows K d a x
      ha hx hcount hrow hK hD
  have hscale' : (2 : ℝ)^(B+1)*x ≤ 1 := by
    have hp : (2 : ℝ)^(B+1) ≤ (2 : ℝ)^a :=
      pow_le_pow_right₀ (by norm_num) (by omega)
    exact (mul_le_mul_of_nonneg_right hp hx.le).trans hscale
  have hlower := exact_suffix_all μ ν F source decode hwise
    Good' hcount' Rows' K' d x hd hx hscale' hprofile hrow' hcol'
  have hupper : Compression.restrictionD G
      (rowRectangle Good' Rows') K' ≤ d :=
    residual_restriction_upper G Good' Rows' K' P' d hcost heval
  change d+1 ≤ Compression.restrictionD G
    (rowRectangle Good' Rows') K' at hlower
  omega

theorem exactBlockBound_of_twoThreshold
    (μ : PositiveRationalLaw X) (ν : PositiveRationalLaw Z)
    (F : X → Z → Bool) (source : FiniteLaw S)
    {q : ℕ} (decode : S → Fin q → Z)
    (hwise : IsDWise 8 source decode ν.toFiniteLaw)
    (d : ℕ) (x : ℝ) (hd : 2 ≤ d) (hx : 0 < x)
    (hprofile : V38RestrictionProfiles.TwoThresholdProfile F
      μ.toFiniteLaw ν.toFiniteLaw x (d : ℤ)) :
    V38Fin2Prefix.ExactBlockBound μ F source decode d x := by
  intro a Good Rows K ha hscale hcount hrow hK
  exact exactboost μ ν F source decode hwise Good Rows K d a x ha hd hx
    hscale hprofile hcount hrow hK

#print axioms exact_suffix_all
#print axioms exactboost
#print axioms exactBlockBound_of_twoThreshold

end CurrentAdditive.V38Fin2Exact
