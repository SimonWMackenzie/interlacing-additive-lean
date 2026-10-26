import CurrentAdditive.RareSuffixGoodTV
import CurrentAdditive.InjectiveProjectionTVCompatible

/-! Appendix H `det:suffix` and `det:rareboost` with the canonical
good-coordinate projection-TV hypothesis and no separately assumed
selected-coordinate or moment estimates. -/

namespace CurrentAdditive.ArbitraryPrefix

open Paper2

variable {X Z S : Type*} [Fintype X] [Fintype Z] [Fintype S]

private theorem good_subset_outside {q : ℕ} (Good E : Finset (Fin q))
    (hOutside : ∀ i ∈ Good, i ∉ E) :
    Good ⊆ (Finset.univ : Finset (Fin q)) \ E := by
  intro i hi
  exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hOutside i hi⟩

/-- Complete arbitrary-`b` suffix reduction from the canonical conditional
projection-TV statement, actual source law, and actual indexed rows/columns. -/
theorem rare_suffix_canonical
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
    (hTV : ∀ J : Finset (Fin q), J ⊆ Finset.univ \ E → J.card ≤ 8 →
      CurrentAdditive.projectionTV
        (CurrentAdditive.condition source (· ∈ Y) (hv.trans_le hY))
        ν.toFiniteLaw decode J ≤ ε) :
    d+1 ≤ Paper2.Compression.restrictionD
      (fun a s => F a.2 (decode s a.1)) (rowRectangle Good Rows) K := by
  have hGoodSubset := good_subset_outside Good E hOutside
  have hgood : ∀ (n : ℕ) (hn : n ≤ 8) (e : Fin n → Fin q),
      Function.Injective e → (∀ j, e j ∈ Good) →
      ∀ P : (Fin n → Z) → Prop,
      |source.prob (fun s => s ∈ Y ∧ P (fun j => decode s (e j))) /
        source.prob (· ∈ Y) - (ν.toFiniteLaw.iid n).prob P| ≤ ε := by
    intro n hn e he heGood P
    exact CurrentAdditive.injective_good_conditioned_event_abs
      source ν.toFiniteLaw decode (· ∈ Y) (hv.trans_le hY)
      E Good hGoodSubset ε hTV hn e he heGood P
  exact rare_suffix_all_good_tv μ ν F source decode hwise Good E hGood
    hOutside Rows Y K d x v ε hd hx hscale hprofile hrow hv hv1 hY
    hK hcond hεpos hεshort hεcap hgood hTV

/-- `det:rareboost` for arbitrary positive amplification, using the actual
cost-minimizing protocol and the source's canonical good-coordinate estimate. -/
theorem rareboost_canonical
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
    (hTV : ∀ J : Finset (Fin q), J ⊆ Finset.univ \ E → J.card ≤ 8 →
      CurrentAdditive.projectionTV
        (CurrentAdditive.condition source (· ∈ Y) (hv.trans_le hY))
        ν.toFiniteLaw decode J ≤ ε) :
    d+a ≤ Paper2.Compression.restrictionD
      (fun a s => F a.2 (decode s a.1)) (rowRectangle Good Rows) K := by
  have hGoodSubset := good_subset_outside Good E hOutside
  have hgood : ∀ (n : ℕ) (hn : n ≤ 8) (e : Fin n → Fin q),
      Function.Injective e → (∀ j, e j ∈ Good) →
      ∀ P : (Fin n → Z) → Prop,
      |source.prob (fun s => s ∈ Y ∧ P (fun j => decode s (e j))) /
        source.prob (· ∈ Y) - (ν.toFiniteLaw.iid n).prob P| ≤ ε := by
    intro n hn e he heGood P
    exact CurrentAdditive.injective_good_conditioned_event_abs
      source ν.toFiniteLaw decode (· ∈ Y) (hv.trans_le hY)
      E Good hGoodSubset ε hTV hn e he heGood P
  exact rareboost_all_good_tv μ ν F source decode hwise Good E Rows Y K
    d a x v ε ha hd hx hscale hprofile hcount hOutside hrow hv hv1 hY
    hK hcond hεpos hεshort hεcap hgood hTV

#print axioms CurrentAdditive.ArbitraryPrefix.rare_suffix_canonical
#print axioms CurrentAdditive.ArbitraryPrefix.rareboost_canonical

end CurrentAdditive.ArbitraryPrefix
