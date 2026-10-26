import CurrentAdditive.RareSuffixShortInjective
import CurrentAdditive.DeterministicSuffixLongGoodTV

/-! Private arbitrary-prefix composition with the checked source long suffix.
The short selected-coordinate TV premise is kept explicit pending the
conditioning-to-injective-selector adapter. -/

namespace CurrentAdditive.ArbitraryPrefix

open Paper2
open CurrentAdditive.SuffixLongSource

variable {X Z S : Type*} [Fintype X] [Fintype Z] [Fintype S]

theorem rare_suffix_all_good_tv
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
    (hεpos : 0 < ε) (hεshort : ε ≤ 1/1000)
    (hεcap : ε ≤ (2 : ℝ)^(-20 : ℤ) / 1024 * v^((1 : ℝ)/256))
    (hgood : ∀ (n : ℕ) (hn : n ≤ 8) (e : Fin n → Fin q),
      Function.Injective e → (∀ j, e j ∈ Good) →
      ∀ P : (Fin n → Z) → Prop,
      |source.prob (fun s => s ∈ Y ∧ P (fun j => decode s (e j))) /
        source.prob (· ∈ Y) - (ν.toFiniteLaw.iid n).prob P| ≤ ε)
    (hTV : ∀ J : Finset (Fin q), J ⊆ Finset.univ \ E → J.card ≤ 8 →
      CurrentAdditive.projectionTV
        (CurrentAdditive.condition source (· ∈ Y) (hv.trans_le hY))
        ν.toFiniteLaw decode J ≤ ε) :
    d+1 ≤ Paper2.Compression.restrictionD
      (fun a s => F a.2 (decode s a.1)) (rowRectangle Good Rows) K := by
  by_cases hb : b ≤ 4
  · exact rare_suffix_short_injective μ ν F source hb decode Good hGood Rows Y K
      d x ε hd hx hscale hprofile hrow (hv.trans_le hY) hK hcond
      hεshort hgood
  · have hb5 : 5 ≤ b := by omega
    have hrow' : ∀ i ∈ Good, (2 : ℝ)^(b+1) * x ≤
        μ.toFiniteLaw.prob (fun u => (i,u) ∈ rowRectangle Good Rows) := by
      intro i hi
      rw [rowRectangle_fiber Good Rows i hi]
      exact hrow i hi
    exact suffix_long_of_good_tv μ ν F source hb5 decode hwise
      Good E hGood hOutside (rowRectangle Good Rows) Y K
      d x v ε hd hx hscale hprofile hrow' hv hv1 hY hK hcond
      hεpos hεcap hTV

theorem rareboost_all_good_tv
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
    (hεpos : 0 < ε) (hεshort : ε ≤ 1/1000)
    (hεcap : ε ≤ (2 : ℝ)^(-20 : ℤ) / 1024 * v^((1 : ℝ)/256))
    (hgood : ∀ (n : ℕ) (hn : n ≤ 8) (e : Fin n → Fin q),
      Function.Injective e → (∀ j, e j ∈ Good) →
      ∀ P : (Fin n → Z) → Prop,
      |source.prob (fun s => s ∈ Y ∧ P (fun j => decode s (e j))) /
        source.prob (· ∈ Y) - (ν.toFiniteLaw.iid n).prob P| ≤ ε)
    (hTV : ∀ J : Finset (Fin q), J ⊆ Finset.univ \ E → J.card ≤ 8 →
      CurrentAdditive.projectionTV
        (CurrentAdditive.condition source (· ∈ Y) (hv.trans_le hY))
        ν.toFiniteLaw decode J ≤ ε) :
    d+a ≤ Paper2.Compression.restrictionD
      (fun a s => F a.2 (decode s a.1)) (rowRectangle Good Rows) K := by
  let G : (Fin q × X) → S → Bool := fun a s => F a.2 (decode s a.1)
  let D := Paper2.Compression.restrictionD G (rowRectangle Good Rows) K
  by_contra hn
  change ¬ (d+a ≤ D) at hn
  have hD : D ≤ d+a-1 := by omega
  obtain ⟨A, B, Good', Rows', K', P', hab, hcount', hrow', hcond',
    hGoodsub, hRowssub, hKsub, hKY, hcost, heval⟩ :=
    rare_prefix_state μ.toFiniteLaw source G Good Rows Y K d a x
      ha hx hcount hrow (hv.trans_le hY) hK hcond hD
  have hscale' : (2 : ℝ)^(B+1) * x ≤ 1 := by
    have hp : (2 : ℝ)^(B+1) ≤ (2 : ℝ)^a :=
      pow_le_pow_right₀ (by norm_num) (by omega)
    exact (mul_le_mul_of_nonneg_right hp hx.le).trans hscale
  have hgood' : ∀ (n : ℕ) (hn : n ≤ 8) (e : Fin n → Fin q),
      Function.Injective e → (∀ j, e j ∈ Good') →
      ∀ P : (Fin n → Z) → Prop,
      |source.prob (fun s => s ∈ Y ∧ P (fun j => decode s (e j))) /
        source.prob (· ∈ Y) - (ν.toFiniteLaw.iid n).prob P| ≤ ε := by
    intro n hn e hinj he P
    exact hgood n hn e hinj (fun j => hGoodsub (he j)) P
  have hOutside' : ∀ i ∈ Good', i ∉ E := by
    intro i hi
    exact hOutside i (hGoodsub hi)
  have hlower := rare_suffix_all_good_tv μ ν F source decode hwise
    Good' E hcount' hOutside' Rows' Y K' d x v ε hd hx hscale'
    hprofile hrow' hv hv1 hY hKY hcond' hεpos hεshort hεcap hgood' hTV
  have hupper : Paper2.Compression.restrictionD G
      (rowRectangle Good' Rows') K' ≤ d :=
    residual_restriction_upper G Good' Rows' K' P' d hcost heval
  change d+1 ≤ Paper2.Compression.restrictionD G
    (rowRectangle Good' Rows') K' at hlower
  omega

#print axioms CurrentAdditive.ArbitraryPrefix.rare_suffix_all_good_tv
#print axioms CurrentAdditive.ArbitraryPrefix.rareboost_all_good_tv

end CurrentAdditive.ArbitraryPrefix
