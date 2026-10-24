import CurrentAdditive.FiniteV35
import CurrentAdditive.ConditioningGeneralComplete

/-! A private selected-v35 readback for the exceptional set consumed by the
pair-projection consequence. The same set and same conditional law are used. -/

namespace FiniteV35Conditioning

open Paper2 Paper2.FiniteLaw CurrentAdditive

noncomputable def paperEpsilon (v τ : ℝ) : ℝ :=
  min τ ((2 : ℝ)^(-30 : ℤ) * v^((1 : ℝ)/256))

noncomputable def paperExceptionCount (v τ : ℝ) : ℕ :=
  8 * Nat.ceil (1024 * (paperEpsilon v τ)^(-(2 : ℝ)) *
    v^(-(1 : ℝ)/512))

theorem paperEpsilon_eq (v τ : ℝ) :
    paperEpsilon v τ = conditioningEpsilonR 1024 v τ := by
  unfold paperEpsilon conditioningEpsilonR
  congr 1
  norm_num

theorem paperExceptionCount_eq (v τ : ℝ) :
    paperExceptionCount v τ = conditioningExceptionCountR 1024 v τ := by
  simp only [paperExceptionCount, conditioningExceptionCountR,
    ← paperEpsilon_eq v τ]
  congr 2
  norm_num

/-- The two displayed conditional estimates use the exceptional set
actually produced from the original 8192-wise source. The set is selected
before the coordinate pairs, as in the manuscript. -/
theorem pair_estimates_from_produced_exception_set
    {S Z : Type*} [Fintype S] [Fintype Z]
    (source : FiniteLaw S) (μ : FiniteLaw Z)
    {q : ℕ} (decode : S → Fin q → Z)
    (hwise : IsDWise 8192 source decode μ)
    (Y K : Set S) (v τ : ℝ)
    (hv : 0 < v) (hτ : 0 < τ)
    (hY : v ≤ source.prob (· ∈ Y)) (hK : K ⊆ Y) :
    ∃ E : Finset (Fin q), E.card ≤ paperExceptionCount v τ ∧
      ∀ {m : ℕ}, 0 < m →
        ∀ (e : Fin (2*m) → Fin q), Function.Injective e →
          (∀ t : Fin (2*m), e t ∉ E) →
          (∀ i : Fin m,
            (μ.iid 2).prob
              (· ∈ CurrentAdditive.SuffixLong.pairImage decode e K i) < 9/25) →
          source.prob (· ∈ K) / source.prob (· ∈ Y) ≤
            ((m : ℝ)/4 + 3*(m : ℝ)^2/16) /
              ((16/25 : ℝ)^4*(m : ℝ)^4) +
                2*(paperEpsilon v τ)/(16/25 : ℝ)^4 ∧
          source.prob (· ∈ K) / source.prob (· ∈ Y) ≤
            2*(625 : ℝ)^512/(v*(m : ℝ)^512) := by
  obtain ⟨E, hcard, hTV⟩ :=
    conditioning_exceptional_coordinates_R
      (by decide : Even 1024) (by decide : 8 ≤ 1024)
      source μ decode (· ∈ Y) v τ hv hY hτ
      (by simpa only [show 8*1024 = 8192 by norm_num] using hwise)
  refine ⟨E, ?_, ?_⟩
  · simpa only [paperExceptionCount_eq] using hcard
  · intro m hm e he hgood hsmall
    constructor
    · simpa only [paperEpsilon_eq] using
        (FiniteV35.pair_projections_conditional_fourth source μ hm
          decode e he Y K hK (hv.trans_le hY) E
          (conditioningEpsilonR 1024 v τ) hgood hTV hsmall)
    · exact FiniteV35.pair_projections_conditional_high source μ hm
        decode hwise e he Y K v hv hY hK hsmall

/-- The exceptional-coordinate producer and the actual retained-pair
consequence share one E. A selected pair must still avoid E; the theorem does
not invent that property or assume the desired projection mass. -/
theorem pair_projections_from_produced_exception_set
    {S Z : Type*} [Fintype S] [Fintype Z]
    (source : FiniteLaw S) (μ : FiniteLaw Z)
    {q m : ℕ} (hm : 16 ≤ m) (decode : S → Fin q → Z)
    (hwise : IsDWise 8192 source decode μ)
    (Y K : Set S) (v τ : ℝ)
    (hv : 0 < v) (hv1 : v ≤ 1) (hτ : 0 < τ)
    (hY : v ≤ source.prob (· ∈ Y)) (hK : K ⊆ Y) :
    ∃ E : Finset (Fin q), E.card ≤ paperExceptionCount v τ ∧
      ∀ (e : Fin (2*m) → Fin q), Function.Injective e →
        (∀ t : Fin (2*m), e t ∉ E) →
        1/(4*(m : ℝ)) ≤
          source.prob (· ∈ K)/source.prob (· ∈ Y) →
        ∃ i : Fin m, (9/25 : ℝ) ≤
          (μ.iid 2).prob (· ∈ CurrentAdditive.SuffixLong.pairImage decode e K i) := by
  obtain ⟨E, hcard, hTV⟩ :=
    conditioning_exceptional_coordinates_R
      (by decide : Even 1024) (by decide : 8 ≤ 1024)
      source μ decode (· ∈ Y) v τ hv hY hτ
      (by simpa only [show 8*1024 = 8192 by norm_num] using hwise)
  refine ⟨E, ?_, ?_⟩
  · simpa only [paperExceptionCount_eq] using hcard
  · intro e he hgood hcond
    exact FiniteV35.pair_projections_good_source_epsilon
      source μ hm decode hwise e he Y K v τ hv hv1 hτ hY hK
      E hgood hTV hcond

#print axioms paperEpsilon_eq
#print axioms paperExceptionCount_eq
#print axioms pair_estimates_from_produced_exception_set
#print axioms pair_projections_from_produced_exception_set

end FiniteV35Conditioning
