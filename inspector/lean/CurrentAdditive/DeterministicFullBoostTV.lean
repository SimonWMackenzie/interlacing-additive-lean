import CurrentAdditive.DeterministicFullBoost
import CurrentAdditive.InjectiveProjectionTVCompatible

/-! The Appendix H full-cost amplification with a single conditioning output. -/

namespace CurrentAdditive.FullBoost

open Paper2
open CurrentAdditive.ArbitraryPrefix

variable {X Z S : Type*} [Fintype X] [Fintype Z] [Fintype S]

/-- The TV guarantee on every set of at most eight good coordinates supplies
the eventwise estimates used in both suffix branches. -/
theorem fullboost_of_tv
    (μ : PositiveRationalLaw X) (ν : PositiveRationalLaw Z)
    (F : X → Z → Bool) (source : FiniteLaw S)
    {q : ℕ} (decode : S → Fin q → Z)
    (hwise : IsDWise (8*1024) source decode ν.toFiniteLaw)
    (Good E : Finset (Fin q)) (Rows : Fin q → Set X) (Y : Set S)
    (C a : ℕ) (x v δ ε : ℝ)
    (hC : 3 ≤ C) (hx : 0 < x)
    (hscale : (2 : ℝ)^a * x ≤ 1)
    (hcount : (if a = 0 then 1 else 2^(a-1)+1) ≤ Good.card)
    (hOutside : ∀ i ∈ Good, i ∉ E)
    (hrow : ∀ i ∈ Good,
      (2 : ℝ)^a * x ≤ μ.toFiniteLaw.prob (· ∈ Rows i))
    (hv : 0 < v) (hv1 : v ≤ 1)
    (hY : v ≤ source.prob (· ∈ Y))
    (hnear : ∀ A : Set X, ∀ B : Set Z,
      x ≤ μ.toFiniteLaw.prob (· ∈ A) →
      1-δ ≤ ν.toFiniteLaw.prob (· ∈ B) →
      C ≤ Compression.restrictionD F A B)
    (hprofile : RestrictionProfile F μ.toFiniteLaw ν.toFiniteLaw x
      ((C-1 : ℕ) : ℤ))
    (hεδ : ε ≤ δ)
    (hεpos : 0 < ε) (hεshort : ε ≤ 1/1000)
    (hεcap : ε ≤ (2 : ℝ)^(-20 : ℤ) / 1024 * v^((1 : ℝ)/256))
    (hTV : ∀ J : Finset (Fin q), J ⊆ Finset.univ \ E → J.card ≤ 8 →
      CurrentAdditive.projectionTV
        (CurrentAdditive.condition source (· ∈ Y) (hv.trans_le hY))
        ν.toFiniteLaw decode J ≤ ε) :
    C+a ≤ Compression.restrictionD
      (fun a s => F a.2 (decode s a.1))
      (rowRectangle Good Rows) Y := by
  have hGoodSubset : Good ⊆ (Finset.univ : Finset (Fin q)) \ E := by
    intro i hi
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ i, hOutside i hi⟩
  have hgood : ∀ (n : ℕ) (_hn : n ≤ 8) (e : Fin n → Fin q),
      Function.Injective e → (∀ j, e j ∈ Good) →
      ∀ P : (Fin n → Z) → Prop,
      |source.prob (fun s => s ∈ Y ∧ P (fun j => decode s (e j))) /
        source.prob (· ∈ Y) - (ν.toFiniteLaw.iid n).prob P| ≤ ε := by
    intro n hn e he hegood P
    exact injective_good_conditioned_event_abs source ν.toFiniteLaw decode
      (· ∈ Y) (hv.trans_le hY) E Good hGoodSubset ε hTV hn e he hegood P
  exact fullboost_of_good_tv μ ν F source decode hwise Good E Rows Y
    C a x v δ ε hC hx hscale hcount hOutside hrow hv hv1 hY hnear
    hprofile hεδ hεpos hεshort hεcap hgood hTV

#print axioms fullboost_of_tv

end CurrentAdditive.FullBoost
