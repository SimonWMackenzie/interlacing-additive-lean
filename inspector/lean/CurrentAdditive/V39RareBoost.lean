import CurrentAdditive.V39SuffixShort
import CurrentAdditive.V38RareSuffixLong
import CurrentAdditive.V38RareBoostPrefix
import Paper2.SourceProjection

/-! Selected-v39 `det:suffix` and `det:rareboost`, with exactly two
base-profile thresholds. The event and exceptional set are fixed before
the arbitrary retained indexed column set is chosen. -/

namespace V38RareBoost

open Paper2 CurrentAdditive CurrentAdditive.ArbitraryPrefix

variable {X Z S : Type*} [Fintype X] [Fintype Z] [Fintype S]

theorem rare_suffix_two_threshold
    (μ : FiniteLaw X) (ν : PositiveRationalLaw Z)
    (F : X → Z → Bool) (source : FiniteLaw S)
    {q b : ℕ} (decode : S → Fin q → Z)
    (hwise : IsDWise 8192 source decode ν.toFiniteLaw)
    (Good E : Finset (Fin q)) (hGood : 2^b + 1 ≤ Good.card)
    (hOutside : ∀ i ∈ Good, i ∉ E)
    (Rows : Fin q → Set X) (Y K : Set S)
    (d : ℕ) (x v τ : ℝ) (hd : 2 ≤ d) (hx : 0 < x)
    (hprofile : V38RestrictionProfiles.TwoThresholdProfile F μ ν.toFiniteLaw x (d : ℤ))
    (hrow : ∀ i ∈ Good, (2 : ℝ)^(b+1)*x ≤ μ.prob (· ∈ Rows i))
    (hv : 0 < v) (hv1 : v ≤ 1) (hτ : 0 < τ)
    (hY : v ≤ source.prob (· ∈ Y)) (hK : K ⊆ Y)
    (hcond : 1/(2 : ℝ)^(b+1) ≤ source.prob (· ∈ K)/source.prob (· ∈ Y))
    (hTV : ∀ J : Finset (Fin q), J ⊆ Finset.univ \ E → J.card ≤ 8 →
      projectionTV (condition source (· ∈ Y) (hv.trans_le hY))
        ν.toFiniteLaw decode J ≤ V38Moments.epsilon v τ) :
    d+1 ≤ Compression.restrictionD
      (fun a s => F a.2 (decode s a.1)) (rowRectangle Good Rows) K := by
  by_cases hb : b ≤ 4
  · exact rare_suffix_short_fixed_E μ ν F source hb decode hwise Good E hGood
      hOutside Rows Y K d x v τ hd hx hprofile hrow hv hv1 hτ hY hK hcond hTV
  · exact rare_suffix_long_fixed_E μ ν.toFiniteLaw F source (by omega) decode
      hwise Good E hGood hOutside Rows Y K d x v τ hd hx hprofile hrow
      hv hv1 hτ hY hK hcond hTV

theorem rareboost_two_threshold
    (μ : FiniteLaw X) (ν : PositiveRationalLaw Z)
    (F : X → Z → Bool) (source : FiniteLaw S)
    {q : ℕ} (decode : S → Fin q → Z)
    (hwise : IsDWise 8192 source decode ν.toFiniteLaw)
    (Good E : Finset (Fin q)) (Rows : Fin q → Set X) (Y K : Set S)
    (d a : ℕ) (x v τ : ℝ)
    (ha : 1 ≤ a) (hd : 2 ≤ d) (hx : 0 < x)
    (hscale : (2 : ℝ)^a*x ≤ 1)
    (hprofile : V38RestrictionProfiles.TwoThresholdProfile F μ ν.toFiniteLaw x (d : ℤ))
    (hcount : 2^(a-1)+1 ≤ Good.card) (hOutside : ∀ i ∈ Good, i ∉ E)
    (hrow : ∀ i ∈ Good, (2 : ℝ)^a*x ≤ μ.prob (· ∈ Rows i))
    (hv : 0 < v) (hv1 : v ≤ 1) (hτ : 0 < τ)
    (hY : v ≤ source.prob (· ∈ Y)) (hK : K ⊆ Y)
    (hcond : (1/2 : ℝ) ≤ source.prob (· ∈ K)/source.prob (· ∈ Y))
    (hTV : ∀ J : Finset (Fin q), J ⊆ Finset.univ \ E → J.card ≤ 8 →
      projectionTV (condition source (· ∈ Y) (hv.trans_le hY))
        ν.toFiniteLaw decode J ≤ V38Moments.epsilon v τ) :
    d+a ≤ Compression.restrictionD
      (fun a s => F a.2 (decode s a.1)) (rowRectangle Good Rows) K := by
  apply rareboost_from_suffix μ F source decode Good Rows Y K d a x
    ha hx hscale hcount hrow (hv.trans_le hY) hK hcond
  intro b Q R C hQ hcount' hrow' _hscale' hC hmass
  exact rare_suffix_two_threshold μ ν F source decode hwise Q E hcount'
    (fun i hi => hOutside i (hQ hi)) R Y C d x v τ hd hx hprofile hrow'
    hv hv1 hτ hY (hC.trans hK) hmass hTV

/-- The exceptional set is selected once from the event, uniformly for
every later retained set, row family, and amplification parameter. -/
theorem rareboost_after_conditioning
    (μ : FiniteLaw X) (ν : PositiveRationalLaw Z)
    (F : X → Z → Bool) (source : FiniteLaw S)
    {q : ℕ} (decode : S → Fin q → Z)
    (hwise : IsDWise 8192 source decode ν.toFiniteLaw)
    (Y : Set S) (v τ : ℝ) (hv : 0 < v) (hv1 : v ≤ 1) (hτ : 0 < τ)
    (hY : v ≤ source.prob (· ∈ Y)) :
    ∃ E : Finset (Fin q), E.card ≤ V38Moments.exceptionCount v τ ∧
      ∀ (Good : Finset (Fin q)) (Rows : Fin q → Set X) (K : Set S)
        (d a : ℕ) (x : ℝ),
        1 ≤ a → 2 ≤ d → 0 < x → (2 : ℝ)^a*x ≤ 1 →
        V38RestrictionProfiles.TwoThresholdProfile F μ ν.toFiniteLaw x (d : ℤ) →
        2^(a-1)+1 ≤ Good.card → (∀ i ∈ Good, i ∉ E) →
        (∀ i ∈ Good, (2 : ℝ)^a*x ≤ μ.prob (· ∈ Rows i)) →
        K ⊆ Y → (1/2 : ℝ) ≤ source.prob (· ∈ K)/source.prob (· ∈ Y) →
        d+a ≤ Compression.restrictionD
          (fun a s => F a.2 (decode s a.1)) (rowRectangle Good Rows) K := by
  obtain ⟨E,hcard,hTV⟩ := V38Moments.conditioning_outside_exception
    source ν.toFiniteLaw decode hwise Y v τ hv hτ hY
  refine ⟨E,hcard,?_⟩
  intro Good Rows K d a x ha hd hx hscale hprofile hcount hOutside hrow hK hcond
  exact rareboost_two_threshold μ ν F source decode hwise Good E Rows Y K d a
    x v τ ha hd hx hscale hprofile hcount hOutside hrow hv hv1 hτ hY hK hcond hTV

/-- Full iid products satisfy the same source contract. -/
theorem iid_eight_thousand_wise (ν : FiniteLaw Z) (q : ℕ) :
    IsDWise 8192 (ν.iid q) id ν := by
  intro J _hJ P
  exact FiniteLaw.pi_prob_restrict (fun _ : Fin q => ν)
    (fun j : J => j.val) Subtype.val_injective P

/-- Full-product form of the conditioned boost. The tuple inputs are
literally complete tuples; the same fixed exceptional-set quantifier
precedes all subsequent retained restrictions. -/
theorem rareboost_full_after_conditioning
    (μ : FiniteLaw X) (ν : PositiveRationalLaw Z)
    (F : X → Z → Bool) (q : ℕ) (Y : Set (Fin q → Z))
    (v τ : ℝ) (hv : 0 < v) (hv1 : v ≤ 1) (hτ : 0 < τ)
    (hY : v ≤ (ν.toFiniteLaw.iid q).prob (· ∈ Y)) :
    ∃ E : Finset (Fin q), E.card ≤ V38Moments.exceptionCount v τ ∧
      ∀ (Good : Finset (Fin q)) (Rows : Fin q → Set X) (K : Set (Fin q → Z))
        (d a : ℕ) (x : ℝ),
        1 ≤ a → 2 ≤ d → 0 < x → (2 : ℝ)^a*x ≤ 1 →
        V38RestrictionProfiles.TwoThresholdProfile F μ ν.toFiniteLaw x (d : ℤ) →
        2^(a-1)+1 ≤ Good.card → (∀ i ∈ Good, i ∉ E) →
        (∀ i ∈ Good, (2 : ℝ)^a*x ≤ μ.prob (· ∈ Rows i)) →
        K ⊆ Y → (1/2 : ℝ) ≤
          (ν.toFiniteLaw.iid q).prob (· ∈ K)/(ν.toFiniteLaw.iid q).prob (· ∈ Y) →
        d+a ≤ Compression.restrictionD (fullInterlace F q)
          (rowRectangle Good Rows) K := by
  exact rareboost_after_conditioning μ ν F (ν.toFiniteLaw.iid q) id
    (iid_eight_thousand_wise ν.toFiniteLaw q) Y v τ hv hv1 hτ hY

/-- A lower bound on the canonical row rectangle transfers to any actual
retained row set containing those blocks. No label weight is changed. -/
theorem rareboost_retained_rows
    (μ : FiniteLaw X) (ν : PositiveRationalLaw Z)
    (F : X → Z → Bool) (source : FiniteLaw S)
    {q : ℕ} (decode : S → Fin q → Z)
    (hwise : IsDWise 8192 source decode ν.toFiniteLaw)
    (Good E : Finset (Fin q)) (U : Set (Fin q × X)) (Y K : Set S)
    (d a : ℕ) (x v τ : ℝ)
    (ha : 1 ≤ a) (hd : 2 ≤ d) (hx : 0 < x) (hscale : (2 : ℝ)^a*x ≤ 1)
    (hprofile : V38RestrictionProfiles.TwoThresholdProfile F μ ν.toFiniteLaw x (d : ℤ))
    (hcount : 2^(a-1)+1 ≤ Good.card) (hOutside : ∀ i ∈ Good, i ∉ E)
    (hrow : ∀ i ∈ Good, (2 : ℝ)^a*x ≤ μ.prob (fun z => (i,z) ∈ U))
    (hv : 0 < v) (hv1 : v ≤ 1) (hτ : 0 < τ)
    (hY : v ≤ source.prob (· ∈ Y)) (hK : K ⊆ Y)
    (hcond : (1/2 : ℝ) ≤ source.prob (· ∈ K)/source.prob (· ∈ Y))
    (hTV : ∀ J : Finset (Fin q), J ⊆ Finset.univ \ E → J.card ≤ 8 →
      projectionTV (condition source (· ∈ Y) (hv.trans_le hY))
        ν.toFiniteLaw decode J ≤ V38Moments.epsilon v τ) :
    d+a ≤ Compression.restrictionD
      (fun a s => F a.2 (decode s a.1)) U K := by
  let Rows : Fin q → Set X := fun i => {z | (i,z) ∈ U}
  have h := rareboost_two_threshold μ ν F source decode hwise Good E Rows Y K
    d a x v τ ha hd hx hscale hprofile hcount hOutside hrow hv hv1 hτ hY hK hcond hTV
  exact h.trans (SourceProjection.restrictionD_map_le
    (fun a s => F a.2 (decode s a.1)) id id U K (rowRectangle Good Rows) K
    (by intro z hz; exact hz.2) (by intro s hs; exact hs))

#print axioms rare_suffix_two_threshold
#print axioms rareboost_two_threshold
#print axioms rareboost_after_conditioning
#print axioms iid_eight_thousand_wise
#print axioms rareboost_full_after_conditioning
#print axioms rareboost_retained_rows

end V38RareBoost
