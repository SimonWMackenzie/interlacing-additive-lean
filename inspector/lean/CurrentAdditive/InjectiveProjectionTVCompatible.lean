import CurrentAdditive.RareSuffixGoodTV
import Paper2.ProductProjections

/-! Private adapter from good finite-set projections to injective tuple events. -/

namespace CurrentAdditive

open Paper2 Paper2.FiniteLaw

private theorem finiteLaw_prob_compl {Ω : Type*} [Fintype Ω]
    (ρ : FiniteLaw Ω) (P : Ω → Prop) :
    ρ.prob (fun ω => ¬ P ω) = 1 - ρ.prob P := by
  classical
  have hsum : ρ.prob (fun ω => ¬ P ω) + ρ.prob P = 1 := by
    unfold FiniteLaw.prob
    rw [← Finset.sum_add_distrib, ← ρ.total]
    apply Finset.sum_congr rfl
    intro ω _
    by_cases hP : P ω <;> simp [hP]
  linarith

private theorem projectionTV_event_abs
    {Ω Z : Type*} [Fintype Ω] [Fintype Z] {q : ℕ}
    (ρ : FiniteLaw Ω) (μ : FiniteLaw Z)
    (draw : Ω → Fin q → Z) (J : Finset (Fin q))
    (ε : ℝ) (hTV : projectionTV ρ μ draw J ≤ ε)
    (A : Finset (J → Z)) :
    |ρ.prob (fun ω => projection draw J ω ∈ A) -
      (μ.iid q).prob (fun z => projection id J z ∈ A)| ≤ ε := by
  classical
  let B : Finset (J → Z) := Finset.univ \ A
  have hforward : ρ.prob (fun ω => projection draw J ω ∈ A) -
      (μ.iid q).prob (fun z => projection id J z ∈ A) ≤ ε := by
    exact (Finset.le_sup' (projectionEventDifference ρ μ draw J)
      (Finset.mem_univ A)).trans hTV
  have hreverse : (μ.iid q).prob (fun z => projection id J z ∈ A) -
      ρ.prob (fun ω => projection draw J ω ∈ A) ≤ ε := by
    have hB := (Finset.le_sup' (projectionEventDifference ρ μ draw J)
      (Finset.mem_univ B)).trans hTV
    have hρ : ρ.prob (fun ω => projection draw J ω ∈ B) =
        1 - ρ.prob (fun ω => projection draw J ω ∈ A) := by
      simpa only [B, Finset.mem_sdiff, Finset.mem_univ, true_and] using
        finiteLaw_prob_compl ρ (fun ω => projection draw J ω ∈ A)
    have hμ : (μ.iid q).prob (fun z => projection id J z ∈ B) =
        1 - (μ.iid q).prob (fun z => projection id J z ∈ A) := by
      simpa only [B, Finset.mem_sdiff, Finset.mem_univ, true_and] using
        finiteLaw_prob_compl (μ.iid q) (fun z => projection id J z ∈ A)
    unfold projectionEventDifference at hB
    rw [hρ, hμ] at hB
    linarith
  exact abs_le.mpr ⟨by linarith, hforward⟩

/-- The TV bound on the image of an injective coordinate selection controls
all events of that ordered tuple against the independent product law. -/
theorem injective_projectionTV_event_abs
    {Ω Z : Type*} [Fintype Ω] [Fintype Z] {q n : ℕ}
    (ρ : FiniteLaw Ω) (μ : FiniteLaw Z)
    (draw : Ω → Fin q → Z) (e : Fin n → Fin q)
    (he : Function.Injective e) (ε : ℝ)
    (hTV : projectionTV ρ μ draw (Finset.univ.image e) ≤ ε)
    (P : (Fin n → Z) → Prop) :
    |ρ.prob (fun ω => P (fun i => draw ω (e i))) -
      (μ.iid n).prob P| ≤ ε := by
  classical
  let J : Finset (Fin q) := Finset.univ.image e
  have hmem (i : Fin n) : e i ∈ J :=
    Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
  let A : Finset (J → Z) := Finset.univ.filter
    (fun z => P (fun i => z ⟨e i, hmem i⟩))
  have hsource : ρ.prob (fun ω => P (fun i => draw ω (e i))) =
      ρ.prob (fun ω => projection draw J ω ∈ A) := by
    congr 1
    funext ω
    simp [A, projection]
  have hproduct : (μ.iid q).prob (fun z => projection id J z ∈ A) =
      (μ.iid n).prob P := by
    have hiidq : μ.iid q = FiniteLaw.pi (fun _ : Fin q => μ) := rfl
    have hiidn : μ.iid n = FiniteLaw.pi (fun _ : Fin n => μ) := rfl
    rw [hiidq, hiidn]
    simpa only [A, Finset.mem_filter, Finset.mem_univ, true_and,
      projection] using
      (FiniteLaw.pi_prob_restrict (fun _ : Fin q => μ) e he P)
  rw [hsource, ← hproduct]
  exact projectionTV_event_abs ρ μ draw J ε hTV A

/-- Conditional-event form consumed by the short-suffix theorem. -/
theorem condition_prob_event_eq_div
    {Ω : Type*} [Fintype Ω]
    (ν : FiniteLaw Ω) (Y P : Ω → Prop) (hY : 0 < ν.prob Y) :
    (condition ν Y hY).prob P =
      ν.prob (fun ω => Y ω ∧ P ω) / ν.prob Y := by
  classical
  unfold FiniteLaw.prob
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro ω _
  by_cases hYω : Y ω <;> by_cases hPω : P ω <;>
    simp [condition, hYω, hPω, FiniteLaw.prob]

/-- Convert the finite exceptional-set conclusion to the exact conditional
eventwise estimate required by a short suffix, for distinct selected good
coordinates. The injectivity assumption cannot be dropped. -/
theorem injective_good_conditioned_event_abs
    {Ω Z : Type*} [Fintype Ω] [Fintype Z] {q n : ℕ}
    (ν : FiniteLaw Ω) (μ : FiniteLaw Z)
    (draw : Ω → Fin q → Z) (Y : Ω → Prop)
    (hY : 0 < ν.prob Y) (E Good : Finset (Fin q))
    (hGoodSubset : Good ⊆ (Finset.univ : Finset (Fin q)) \ E)
    (ε : ℝ)
    (hTV : ∀ J : Finset (Fin q),
      J ⊆ (Finset.univ : Finset (Fin q)) \ E → J.card ≤ 8 →
        projectionTV (condition ν Y hY) μ draw J ≤ ε)
    (hn : n ≤ 8) (e : Fin n → Fin q) (he : Function.Injective e)
    (heGood : ∀ i, e i ∈ Good) (P : (Fin n → Z) → Prop) :
    |ν.prob (fun ω => Y ω ∧ P (fun i => draw ω (e i))) /
        ν.prob Y - (μ.iid n).prob P| ≤ ε := by
  classical
  let J : Finset (Fin q) := Finset.univ.image e
  have hJsubset : J ⊆ (Finset.univ : Finset (Fin q)) \ E := by
    intro j hj
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hj
    exact hGoodSubset (heGood i)
  have hJcard : J.card ≤ 8 := by
    exact (Finset.card_image_le).trans (by simpa [J] using hn)
  have ht := injective_projectionTV_event_abs (condition ν Y hY)
    μ draw e he ε (hTV J hJsubset hJcard) P
  rw [condition_prob_event_eq_div ν Y
    (fun ω => P (fun i => draw ω (e i))) hY] at ht
  exact ht

#print axioms injective_projectionTV_event_abs
#print axioms condition_prob_event_eq_div
#print axioms injective_good_conditioned_event_abs

end CurrentAdditive
