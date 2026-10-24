import CurrentAdditive.ConditioningFiniteTV
import CurrentAdditive.TVBridge
import CurrentAdditive.FourthMoment

namespace CurrentAdditive.FourthMoment.ProjectionTVBridge

open Paper2

variable {A B Z : Type*} [Fintype A] [Fintype B] [Fintype Z]

/-- The finite pushforward of a law along a map. -/
noncomputable def mapLaw (ρ : FiniteLaw A) (f : A → B) : FiniteLaw B where
  weight b := ρ.prob (fun a => f a = b)
  nonneg b := ρ.prob_nonneg _
  total := by
    classical
    unfold FiniteLaw.prob
    rw [Finset.sum_comm]
    simpa using ρ.total

theorem mapLaw_prob (ρ : FiniteLaw A) (f : A → B) (E : B → Prop) :
    (mapLaw ρ f).prob E = ρ.prob (fun a => E (f a)) := by
  exact (FiniteLaw.prob_preimage_eq_of_fibres ρ (mapLaw ρ f) f
    (fun b => rfl) E).symm

theorem mapLaw_expect (ρ : FiniteLaw A) (f : A → B) (g : B → ℝ) :
    FourthMoment.expect (mapLaw ρ f) g =
      FourthMoment.expect ρ (fun a => g (f a)) := by
  exact (FourthMoment.expect_eq_of_prob_preimage ρ (mapLaw ρ f) f
    (fun E => (mapLaw_prob ρ f E).symm) g).symm

theorem prob_add_not (ρ : FiniteLaw A) (E : A → Prop) :
    ρ.prob E + ρ.prob (fun a => ¬ E a) = 1 := by
  classical
  unfold FiniteLaw.prob
  rw [← Finset.sum_add_distrib]
  calc
    _ = ∑ a, ρ.weight a := by
      apply Finset.sum_congr rfl
      intro a _
      by_cases h : E a <;> simp [h]
    _ = 1 := ρ.total

/-- A projection-TV cap bounds the absolute discrepancy of every event
defined on that finite projection. -/
theorem projection_event_abs_le
    {Ω : Type*} [Fintype Ω] {q : ℕ}
    (ρ : FiniteLaw Ω) (μ : FiniteLaw Z)
    (draw : Ω → Fin q → Z) (J : Finset (Fin q)) (ε : ℝ)
    (hTV : projectionTV ρ μ draw J ≤ ε)
    (E : (J → Z) → Prop) :
    |ρ.prob (fun ω => E (projection draw J ω)) -
      (μ.iid q).prob (fun z => E (projection id J z))| ≤ ε := by
  classical
  let A : Finset (J → Z) := Finset.univ.filter E
  let Ac : Finset (J → Z) := Finset.univ.filter (fun z => ¬ E z)
  have hA : projectionEventDifference ρ μ draw J A ≤ ε :=
    (Finset.le_sup' (fun B => projectionEventDifference ρ μ draw J B)
      (Finset.mem_univ A)).trans hTV
  have hAc : projectionEventDifference ρ μ draw J Ac ≤ ε :=
    (Finset.le_sup' (fun B => projectionEventDifference ρ μ draw J B)
      (Finset.mem_univ Ac)).trans hTV
  have hpos : ρ.prob (fun ω => E (projection draw J ω)) -
      (μ.iid q).prob (fun z => E (projection id J z)) ≤ ε := by
    simpa only [projectionEventDifference, A, Finset.mem_filter,
      Finset.mem_univ, true_and] using hA
  have hneg : (μ.iid q).prob (fun z => E (projection id J z)) -
      ρ.prob (fun ω => E (projection draw J ω)) ≤ ε := by
    have hr := prob_add_not ρ (fun ω => E (projection draw J ω))
    have hm := prob_add_not (μ.iid q) (fun z => E (projection id J z))
    have hc : ρ.prob (fun ω => ¬ E (projection draw J ω)) -
        (μ.iid q).prob (fun z => ¬ E (projection id J z)) ≤ ε := by
      simpa only [projectionEventDifference, Ac, Finset.mem_filter,
        Finset.mem_univ, true_and] using hAc
    linarith
  exact abs_le.mpr ⟨by linarith, hpos⟩

/-- Bounded projected tests inherit the standard `2ε` expectation error. -/
theorem projection_expect_abs_le_two
    {Ω : Type*} [Fintype Ω] {q : ℕ}
    (ρ : FiniteLaw Ω) (μ : FiniteLaw Z)
    (draw : Ω → Fin q → Z) (J : Finset (Fin q)) (ε : ℝ)
    (hTV : projectionTV ρ μ draw J ≤ ε)
    (g : (J → Z) → ℝ) (hg : ∀ z, |g z| ≤ 1) :
    |FourthMoment.expect ρ (fun ω => g (projection draw J ω)) -
      FourthMoment.expect (μ.iid q)
        (fun z => g (projection id J z))| ≤ 2 * ε := by
  let fρ := projection draw J
  let fμ := projection (fun z : Fin q → Z => z) J
  have hevent (E : (J → Z) → Prop) :
      |(mapLaw ρ fρ).prob E - (mapLaw (μ.iid q) fμ).prob E| ≤ ε := by
    simpa only [mapLaw_prob] using
      projection_event_abs_le ρ μ draw J ε hTV E
  have h := TVBridge.expect_abs_sub_le_two (mapLaw ρ fρ)
    (mapLaw (μ.iid q) fμ) g ε hevent hg
  change |FourthMoment.expect (mapLaw ρ fρ) g -
    FourthMoment.expect (mapLaw (μ.iid q) fμ) g| ≤ 2 * ε at h
  rw [mapLaw_expect, mapLaw_expect] at h
  exact h

#print axioms projection_expect_abs_le_two

end CurrentAdditive.FourthMoment.ProjectionTVBridge
