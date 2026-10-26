import CurrentAdditive.FiniteV35
import CurrentAdditive.ConditioningExceptionV35

namespace FiniteV35Admission

open Paper2 CurrentAdditive CurrentAdditive.SuffixLong
open CurrentAdditive.FourthMoment
open scoped BigOperators

/-- The non-strict fourth-moment pair bound needs only a nonempty pair list.
The stronger m ≥ 8 condition is solely for the strict numerical corollary. -/
theorem exact_pair_tail_all
    {Ω : Type*} [Fintype Ω] {m : ℕ}
    (ρ : FiniteLaw Ω) (Z : Fin m → Ω → Bool)
    (β : Fin m → FiniteLaw Bool) (K : Ω → Prop)
    (hm : 0 < m)
    (hsmall : ∀ i, (β i).prob (fun b => b = true) < 9/25)
    (hK : ∀ ω, K ω → ∀ i, Z i ω = true)
    (hjoint : ∀ (s : Finset (Fin m)), s.card ≤ 4 →
      ∀ E : (s → Bool) → Prop,
        ρ.prob (fun ω => E (fun j : s => Z j.val ω)) =
          (FiniteLaw.pi (fun j : s => β j.val)).prob E) :
    ρ.prob K ≤
      ((m : ℝ)/4 + 3*(m : ℝ)^2/16) /
        ((16/25 : ℝ)^4 * (m : ℝ)^4) := by
  classical
  let S (ω : Ω) := ∑ i : Fin m, boolCentered β i (Z i ω)
  let a : ℝ := (16/25 : ℝ) * m
  have hmR : 0 < (m : ℝ) := Nat.cast_pos.mpr hm
  have ha : 0 < a := mul_pos (by norm_num) hmR
  have hsource : ∀ ω, K ω → a ≤ S ω := by
    intro ω hω
    have hpoints : ∀ i : Fin m, (16/25 : ℝ) ≤ boolCentered β i (Z i ω) := by
      intro i
      have hz := hK ω hω i
      have hp := hsmall i
      simp only [boolCentered, hz, ↓reduceIte]
      linarith
    calc
      a = ∑ _i : Fin m, (16/25 : ℝ) := by simp [a, mul_comm]
      _ ≤ ∑ i : Fin m, boolCentered β i (Z i ω) :=
        Finset.sum_le_sum (fun i _ => hpoints i)
  have hmoment : expect ρ (fun ω => (S ω)^4) ≤
      (m : ℝ)/4 + 3*(m : ℝ)^2/16 := by
    simpa only [S, Fintype.card_fin] using
      fourth_bound_of_four_wise ρ Z β hjoint
  have hmarkov := event_le_fourth_moment ρ S K a ha hsource
  have hden : (0 : ℝ) < (16/25 : ℝ)^4 * (m : ℝ)^4 := by positivity
  have ha4 : a^4 = (16/25 : ℝ)^4 * (m : ℝ)^4 := by simp [a, mul_pow]
  rw [ha4] at hmarkov
  apply (le_div_iff₀ hden).2
  simpa only [mul_comm] using hmarkov.trans hmoment

/-- Source-faithful first pair projection estimate for every m ≥ 1. -/
theorem pair_projections_first_all
    {S Z : Type*} [Fintype S] [Fintype Z]
    (source : FiniteLaw S) (μ : FiniteLaw Z)
    {m q : ℕ} (hm : 0 < m) (decode : S → Fin q → Z)
    (hwise : IsDWise 8 source decode μ)
    (e : Fin (2*m) → Fin q) (he : Function.Injective e)
    (K : Set S)
    (hsmall : ∀ i : Fin m,
      (μ.iid 2).prob (· ∈ pairImage decode e K i) < 9/25) :
    source.prob (· ∈ K) ≤
      ((m : ℝ)/4 + 3*(m : ℝ)^2/16) /
        ((16/25 : ℝ)^4*(m : ℝ)^4) := by
  classical
  let F : Fin m → S → Bool := fun i s => pairHit decode e K i (decode s)
  let β : Fin m → FiniteLaw Bool :=
    fun i => boolImageLaw (μ.iid q) (pairHit decode e K i)
  have hβ : ∀ i, (β i).prob (fun b => b = true) < 9/25 := by
    intro i
    have hmass := pairHit_ambient_mass μ decode e he K i
    simpa only [β, boolImageLaw, FiniteLaw.prob_singleton, hmass] using hsmall i
  have hK : ∀ s, s ∈ K → ∀ i, F i s = true := by
    intro s hs i
    exact pairHit_of_retained decode e K i s hs
  have hjoint : ∀ (s : Finset (Fin m)), s.card ≤ 4 →
      ∀ E : (s → Bool) → Prop,
        source.prob (fun ω => E (fun j : s => F j.val ω)) =
          (FiniteLaw.pi (fun j : s => β j.val)).prob E := by
    intro s hs E
    exact pairHit_source_four_wise_of_eight source μ decode hwise
      e he K s hs E
  exact exact_pair_tail_all source F β (· ∈ K) hm hβ hK hjoint

/-- The exceptional set is chosen from Y before the retained event K and
before any pair list. Both displayed conditional estimates and the final
large-m consequence use that very same set and original source law. -/
theorem universal_pair_estimates_and_projection
    {S Z : Type*} [Fintype S] [Fintype Z]
    (source : FiniteLaw S) (μ : FiniteLaw Z)
    {q : ℕ} (decode : S → Fin q → Z)
    (hwise : IsDWise 8192 source decode μ)
    (Y : Set S) (v τ : ℝ)
    (hv : 0 < v) (hv1 : v ≤ 1) (hτ : 0 < τ) (_hτ1 : τ ≤ 1)
    (hY : v ≤ source.prob (· ∈ Y)) :
    ∃ E : Finset (Fin q),
      E.card ≤ FiniteV35Conditioning.paperExceptionCount v τ ∧
      (∀ {m : ℕ}, 0 < m →
        ∀ (e : Fin (2*m) → Fin q), Function.Injective e →
          (∀ t : Fin (2*m), e t ∉ E) →
          ∀ K : Set S, K ⊆ Y →
            (∀ i : Fin m,
              (μ.iid 2).prob (· ∈ pairImage decode e K i) < 9/25) →
            source.prob (· ∈ K) / source.prob (· ∈ Y) ≤
              ((m : ℝ)/4 + 3*(m : ℝ)^2/16) /
                ((16/25 : ℝ)^4*(m : ℝ)^4) +
                  2*FiniteV35Conditioning.paperEpsilon v τ/(16/25 : ℝ)^4 ∧
            source.prob (· ∈ K) / source.prob (· ∈ Y) ≤
              2*(625 : ℝ)^512/(v*(m : ℝ)^512)) ∧
      (∀ {m : ℕ}, 16 ≤ m →
        ∀ (e : Fin (2*m) → Fin q), Function.Injective e →
          (∀ t : Fin (2*m), e t ∉ E) →
          ∀ K : Set S, K ⊆ Y →
            1/(4*(m : ℝ)) ≤
              source.prob (· ∈ K)/source.prob (· ∈ Y) →
            ∃ i : Fin m, (9/25 : ℝ) ≤
              (μ.iid 2).prob (· ∈ pairImage decode e K i)) := by
  have hwise' : IsDWise (8*1024) source decode μ := by
    simpa only [show 8*1024 = 8192 by norm_num] using hwise
  obtain ⟨E, hE, hTV⟩ :=
    CurrentAdditive.conditioning_exceptional_coordinates_R (R := 1024)
      (by norm_num) (by norm_num) source μ decode (· ∈ Y)
      v τ hv hY hτ hwise'
  refine ⟨E, ?_, ?_, ?_⟩
  · simpa only [FiniteV35Conditioning.paperExceptionCount_eq] using hE
  · intro m hm e he hgood K hK hsmall
    constructor
    · simpa only [FiniteV35Conditioning.paperEpsilon_eq] using
        (FiniteV35.pair_projections_conditional_fourth source μ hm
          decode e he Y K hK (hv.trans_le hY) E
          (CurrentAdditive.conditioningEpsilonR 1024 v τ)
          hgood hTV hsmall)
    · exact FiniteV35.pair_projections_conditional_high source μ hm
        decode hwise e he Y K v hv hY hK hsmall
  · intro m hm e he hgood K hK hcond
    exact FiniteV35.pair_projections_good_source_epsilon
      source μ hm decode hwise e he Y K v τ hv hv1 hτ hY hK
      E hgood hTV hcond

#print axioms exact_pair_tail_all
#print axioms pair_projections_first_all
#print axioms universal_pair_estimates_and_projection

end FiniteV35Admission
