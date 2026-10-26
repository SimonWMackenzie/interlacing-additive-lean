import CurrentAdditive.V39IncomingCapOne

/-! v42, proof of `res:incoming`: fix complete metadata and base streams
while retaining at least half of the original incoming diagonal density.
The analytic lower-tail estimate is deliberately a separate theorem input
to this averaging lemma. The final incoming theorem instantiates it. -/

namespace CurrentAdditive.V42IncomingWeightedSection

open Paper2
open CurrentAdditive.DeterministicIndexedMatrix
open CurrentAdditive.DeterministicIndexedMatrix.Sources
open scoped BigOperators

private theorem prod_prob_fst
    {A B : Type*} [Fintype A] [Fintype B]
    (ρ : FiniteLaw A) (σ : FiniteLaw B) (P : A → Prop) :
    (ρ.prod σ).prob (fun z => P z.1) = ρ.prob P := by
  classical
  rw [FiniteLaw.prod_prob ρ σ (fun a _ => P a)]
  unfold FiniteLaw.prob
  apply Finset.sum_congr rfl
  intro a _
  by_cases h : P a <;> simp [h, σ.total]

private theorem prob_inter_good_lower
    {A : Type*} [Fintype A] (ρ : FiniteLaw A)
    (Yevent Good : A → Prop) (θ : ℝ)
    (hY : θ/2 ≤ ρ.prob Yevent)
    (hbad : ρ.prob (fun x => ¬ Good x) ≤ θ/4) :
    θ/4 ≤ ρ.prob (fun x => Yevent x ∧ Good x) := by
  classical
  have hsplit : ρ.prob Yevent ≤
      ρ.prob (fun x => Yevent x ∧ Good x) +
        ρ.prob (fun x => ¬ Good x) := by
    unfold FiniteLaw.prob
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro x _
    by_cases hYx : Yevent x <;> by_cases hG : Good x <;>
      simp [hYx, hG, ρ.nonneg x]
  linarith

variable {I X Y : Type*} [Fintype I] [Fintype X] [Fintype Y]
  [DecidableEq I] [DecidableEq X] [DecidableEq Y]
  {q₁ q₂ s : ℕ} [NeZero s] [NeZero q₁] [NeZero q₂]
  {μX : PositiveRationalLaw X} {μY : PositiveRationalLaw Y}
  (src : Sources (D := 8192) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY)
  {μI : PositiveRationalLaw I} {w : ℕ}
  (streams : InternalStreams src μI w)

noncomputable def templateMass (d : Fin w → ℝ)
    (md : streams.metadataStream.Label) : ℝ :=
  ∑ i, d i * (if isTemplateFlag (streams.metadataStream.decode md i)
    then (1 : ℝ) else 0)

/-- Averaging uses complete source labels, preserving the original independent
selector law. No quotient of metadata or base labels is introduced. -/
theorem complete_weighted_template_section
    (d : Fin w → ℝ) (θ : ℝ) (hθ : 0 < θ)
    (Ystar : Set (streams.metadataStream.Label ×
      (streams.baseStream.Label × streams.selectorStream.Label)))
    (hYstar : θ/2 ≤ streams.law.toFiniteLaw.prob (· ∈ Ystar))
    (hbad : streams.metadataStream.law.toFiniteLaw.prob
      (fun md => templateMass src streams d md < (∑ i, d i)/2) ≤ θ/4) :
    ∃ md : streams.metadataStream.Label,
      ∃ base : streams.baseStream.Label,
        (∑ i, d i)/2 ≤ templateMass src streams d md ∧
        θ/4 ≤ streams.selectorStream.law.toFiniteLaw.prob
          (fun sel => (md,(base,sel)) ∈ Ystar) := by
  let bad : streams.metadataStream.Label → Prop := fun md =>
    templateMass src streams d md < (∑ i, d i)/2
  have hlaw : streams.law.toFiniteLaw =
      streams.metadataStream.law.toFiniteLaw.prod
        (streams.baseStream.law.toFiniteLaw.prod
          streams.selectorStream.law.toFiniteLaw) := by
    simp [InternalStreams.law, PositiveRationalLaw.toFiniteLaw_prod]
  have hbadTotal : streams.law.toFiniteLaw.prob
      (fun a => bad a.1) ≤ θ/4 := by
    rw [hlaw, prod_prob_fst]
    exact hbad
  have hgood : θ/4 ≤ streams.law.toFiniteLaw.prob
      (fun a => a ∈ Ystar ∧ ¬ bad a.1) :=
    prob_inter_good_lower streams.law.toFiniteLaw (· ∈ Ystar)
      (fun a => ¬ bad a.1) θ hYstar (by simpa using hbadTotal)
  obtain ⟨md,hmd,base,hsection⟩ :=
    exists_complete_stream_section src streams Ystar
      (fun md => ¬ bad md) (θ/4) (by linarith) hgood
  exact ⟨md,base,le_of_not_gt hmd,hsection⟩

end CurrentAdditive.V42IncomingWeightedSection

#print axioms CurrentAdditive.V42IncomingWeightedSection.complete_weighted_template_section
