import CurrentAdditive.GeneratedPairwiseMissedEvents
import Paper2.SourceDeficiencyTemplate

/-!
The source-specific `det:near-full` deficiency contradiction. If eight times
q1 distinct inner coordinates each lose one of their q1 base-row blocks,
their missed events have total original mean at least seven. Exact two-wise
marginals and the second-moment bound then exclude any retained generated
inner-label event of mass greater than 1/7.
-/

namespace CurrentAdditive.DeterministicIndexedMatrix.Sources

open Paper2 Paper2.SourceMatrix Paper2.SourceDeficiencyTemplate
attribute [local instance] Classical.propDecidable

variable {X Y I : Type*} [Fintype X] [Fintype Y] [Fintype I]
  [DecidableEq X] [DecidableEq Y]
  {D q₁ q₂ s : ℕ} [NeZero s] [NeZero q₁] [NeZero q₂]
  {μX : PositiveRationalLaw X} {μY : PositiveRationalLaw Y}
  (src : Sources (D := D) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY)

private theorem prob_not {A : Type*} [Fintype A]
    (ν : FiniteLaw A) (E : A → Prop) :
    ν.prob (fun a => ¬ E a) = 1 - ν.prob E := by
  classical
  have h : ν.prob E + ν.prob (fun a => ¬ E a) = 1 := by
    unfold FiniteLaw.prob
    rw [← Finset.sum_add_distrib, ← ν.total]
    apply Finset.sum_congr rfl
    intro a _
    by_cases ha : E a <;> simp [ha]
  linarith

/-- The actual high-mass generated inner-label set cannot have `8*q₁`
distinct deficient decoded coordinates. The projection is the image of the
same retained set, so no independent retained-word law is used. -/
theorem no_eight_q1_deficient
    (hD : 2 ≤ D) (K : Set src.inner.Label)
    (hKmass : (1 / 7 : ℝ) < src.inner.law.toFiniteLaw.prob (· ∈ K))
    (e : Fin (8 * q₁) → Fin q₂) (he : Function.Injective e)
    (hdef : ∀ k : Fin (8 * q₁),
      Deficient μX (fun t : Template q₁ q₂ X =>
        ∃ z ∈ K, src.inner.decode z = t) (e k)) : False := by
  classical
  let μ := ((PositiveRationalLaw.uniform (Fin q₁)).prod μX).toFiniteLaw
  let A : Template q₁ q₂ X → Prop := fun t =>
    ∃ z ∈ K, src.inner.decode z = t
  let E : Fin (8 * q₁) → (Fin q₁ × X) → Prop := fun k v =>
    ¬ projectedAt A (e k) v
  have havoid (z : src.inner.Label) (hz : z ∈ K) (k : Fin (8 * q₁)) :
      ¬ E k (src.inner.decode z (e k)) := by
    simp only [E, not_not]
    exact ⟨src.inner.decode z, ⟨z, hz, rfl⟩, rfl⟩
  have hprob (k : Fin (8 * q₁)) :
      (7 / (8 * (q₁ : ℝ))) ≤ μ.prob (E k) := by
    have hproj := projection_mass_le μX A (e k) (hdef k)
    have hnot := prob_not μ (projectedAt A (e k))
    change μ.prob (E k) =
      1 - μ.prob (projectedAt A (e k)) at hnot
    change μ.prob (projectedAt A (e k)) ≤
      1 - 7 / (8 * (q₁ : ℝ)) at hproj
    linarith
  have hmean : (7 : ℝ) ≤ ∑ k : Fin (8 * q₁), μ.prob (E k) := by
    have hsum : (∑ _k : Fin (8 * q₁), (7 / (8 * (q₁ : ℝ)))) ≤
        ∑ k : Fin (8 * q₁), μ.prob (E k) := by
      apply Finset.sum_le_sum
      intro k _
      exact hprob k
    have hq : (0 : ℝ) < q₁ := by exact_mod_cast NeZero.pos q₁
    have hvalue : (∑ _k : Fin (8 * q₁),
        (7 / (8 * (q₁ : ℝ)))) = 7 := by
      simp only [Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul, Nat.cast_mul]
      field_simp
      norm_num
    linarith
  have hM : 0 < ∑ k : Fin (8 * q₁), μ.prob (E k) := by linarith
  have hbound := inner_avoid_mass_le src hD (8 * q₁) e he E K havoid hM
  have hinv : 1 / (∑ k : Fin (8 * q₁), μ.prob (E k)) ≤
      (1 / 7 : ℝ) := by
    exact one_div_le_one_div_of_le (by norm_num) hmean
  exact (not_lt_of_ge (hbound.trans hinv)) hKmass

/-- The actual finite set of deficient generated inner-source coordinates
has fewer than `8*q₁` members whenever the retained source event has mass
greater than `1/7`. Thus the manuscript's `>0.998` branch mass is more than
sufficient; the coordinate count is independent of the source-index length. -/
theorem deficient_coordinate_card_lt
    (hD : 2 ≤ D) (K : Set src.inner.Label)
    (hKmass : (1 / 7 : ℝ) < src.inner.law.toFiniteLaw.prob (· ∈ K)) :
    (Finset.univ.filter (fun α : Fin q₂ =>
      Deficient μX (fun t : Template q₁ q₂ X =>
        ∃ z ∈ K, src.inner.decode z = t) α)).card < 8 * q₁ := by
  classical
  let bad : Finset (Fin q₂) := Finset.univ.filter (fun α =>
    Deficient μX (fun t : Template q₁ q₂ X =>
      ∃ z ∈ K, src.inner.decode z = t) α)
  change bad.card < 8 * q₁
  by_contra hn
  have hle : Fintype.card (Fin (8 * q₁)) ≤ bad.card := by
    simpa using Nat.le_of_not_gt hn
  obtain ⟨e, he⟩ := Function.Embedding.exists_of_card_le_finset
    (s := bad) hle
  apply no_eight_q1_deficient src hD K hKmass e e.injective
  intro k
  have hmem : (e k : Fin q₂) ∈ bad := he ⟨k, rfl⟩
  exact (Finset.mem_filter.mp hmem).2

end CurrentAdditive.DeterministicIndexedMatrix.Sources

#print axioms CurrentAdditive.DeterministicIndexedMatrix.Sources.no_eight_q1_deficient
#print axioms CurrentAdditive.DeterministicIndexedMatrix.Sources.deficient_coordinate_card_lt
