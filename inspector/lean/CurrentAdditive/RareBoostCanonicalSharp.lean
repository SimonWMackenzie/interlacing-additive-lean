import CurrentAdditive.RareBoostCanonical

/-! Literal `det:suffix` and `det:rareboost` interfaces: the short-case
numerical TV cap is deduced from the manuscript's displayed epsilon cap. -/

namespace CurrentAdditive.ArbitraryPrefix

open Paper2

variable {X Z S : Type*} [Fintype X] [Fintype Z] [Fintype S]

private theorem epsilon_short_of_cap (v ε : ℝ)
    (hv : 0 < v) (hv1 : v ≤ 1)
    (hεcap : ε ≤ (2 : ℝ)^(-20 : ℤ) / 1024 * v^((1 : ℝ)/256)) :
    ε ≤ 1/1000 := by
  have hpow : v^((1 : ℝ)/256) ≤ 1 :=
    Real.rpow_le_one hv.le hv1 (by norm_num)
  have hconst : (0 : ℝ) ≤ (2 : ℝ)^(-20 : ℤ) / 1024 := by positivity
  have hmul := mul_le_mul_of_nonneg_left hpow hconst
  have hnum : (2 : ℝ)^(-20 : ℤ) / 1024 ≤ 1/1000 := by norm_num
  nlinarith

theorem rare_suffix_canonical_sharp
    (μ : PositiveRationalLaw X) (ν : PositiveRationalLaw Z)
    (F : X → Z → Bool) (source : FiniteLaw S)
    {q b : ℕ} (decode : S → Fin q → Z)
    (hwise : IsDWise (8*1024) source decode ν.toFiniteLaw)
    (Good E : Finset (Fin q)) (hGood : 2^b + 1 ≤ Good.card)
    (hOutside : ∀ i ∈ Good, i ∉ E)
    (Rows : Fin q → Set X) (Y K : Set S)
    (d : ℕ) (x v ε : ℝ)
    (hd : 2 ≤ d) (hx : 0 < x)
    (hscale : (2 : ℝ)^(b+1) * x ≤ 1)
    (hprofile : RestrictionProfile F μ.toFiniteLaw ν.toFiniteLaw x (d : ℤ))
    (hrow : ∀ i ∈ Good, (2 : ℝ)^(b+1) * x ≤ μ.toFiniteLaw.prob (· ∈ Rows i))
    (hv : 0 < v) (hv1 : v ≤ 1)
    (hY : v ≤ source.prob (· ∈ Y)) (hK : K ⊆ Y)
    (hcond : 1 / (2 : ℝ)^(b+1) ≤ source.prob (· ∈ K) / source.prob (· ∈ Y))
    (hεpos : 0 < ε)
    (hεcap : ε ≤ (2 : ℝ)^(-20 : ℤ) / 1024 * v^((1 : ℝ)/256))
    (hTV : ∀ J : Finset (Fin q), J ⊆ Finset.univ \ E → J.card ≤ 8 →
      CurrentAdditive.projectionTV
        (CurrentAdditive.condition source (· ∈ Y) (hv.trans_le hY))
        ν.toFiniteLaw decode J ≤ ε) :
    d+1 ≤ Paper2.Compression.restrictionD
      (fun a s => F a.2 (decode s a.1)) (rowRectangle Good Rows) K :=
  rare_suffix_canonical μ ν F source decode hwise Good E hGood hOutside
    Rows Y K d x v ε hd hx hscale hprofile hrow hv hv1 hY hK hcond
    hεpos (epsilon_short_of_cap v ε hv hv1 hεcap) hεcap hTV

theorem rareboost_canonical_sharp
    (μ : PositiveRationalLaw X) (ν : PositiveRationalLaw Z)
    (F : X → Z → Bool) (source : FiniteLaw S)
    {q : ℕ} (decode : S → Fin q → Z)
    (hwise : IsDWise (8*1024) source decode ν.toFiniteLaw)
    (Good E : Finset (Fin q)) (Rows : Fin q → Set X) (Y K : Set S)
    (d a : ℕ) (x v ε : ℝ)
    (ha : 1 ≤ a) (hd : 2 ≤ d) (hx : 0 < x)
    (hscale : (2 : ℝ)^a * x ≤ 1)
    (hprofile : RestrictionProfile F μ.toFiniteLaw ν.toFiniteLaw x (d : ℤ))
    (hcount : 2^(a-1) + 1 ≤ Good.card)
    (hOutside : ∀ i ∈ Good, i ∉ E)
    (hrow : ∀ i ∈ Good, (2 : ℝ)^a * x ≤ μ.toFiniteLaw.prob (· ∈ Rows i))
    (hv : 0 < v) (hv1 : v ≤ 1)
    (hY : v ≤ source.prob (· ∈ Y)) (hK : K ⊆ Y)
    (hcond : (1/2 : ℝ) ≤ source.prob (· ∈ K) / source.prob (· ∈ Y))
    (hεpos : 0 < ε)
    (hεcap : ε ≤ (2 : ℝ)^(-20 : ℤ) / 1024 * v^((1 : ℝ)/256))
    (hTV : ∀ J : Finset (Fin q), J ⊆ Finset.univ \ E → J.card ≤ 8 →
      CurrentAdditive.projectionTV
        (CurrentAdditive.condition source (· ∈ Y) (hv.trans_le hY))
        ν.toFiniteLaw decode J ≤ ε) :
    d+a ≤ Paper2.Compression.restrictionD
      (fun a s => F a.2 (decode s a.1)) (rowRectangle Good Rows) K :=
  rareboost_canonical μ ν F source decode hwise Good E Rows Y K
    d a x v ε ha hd hx hscale hprofile hcount hOutside hrow hv hv1 hY hK
    hcond hεpos (epsilon_short_of_cap v ε hv hv1 hεcap) hεcap hTV

#print axioms CurrentAdditive.ArbitraryPrefix.rare_suffix_canonical_sharp
#print axioms CurrentAdditive.ArbitraryPrefix.rareboost_canonical_sharp

end CurrentAdditive.ArbitraryPrefix
