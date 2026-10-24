import CurrentAdditive.IndexedSections

/-! Appendix I `det:incoming`: from the actual metadata flag tail to a
complete-stream section retaining selector mass. -/

namespace CurrentAdditive.DeterministicIndexedMatrix

open Paper2
open scoped BigOperators

private theorem finite_prod_prob_fst
    {A B : Type*} [Fintype A] [Fintype B]
    (ρ : FiniteLaw A) (σ : FiniteLaw B) (P : A → Prop) :
    (ρ.prod σ).prob (fun z => P z.1) = ρ.prob P := by
  classical
  rw [FiniteLaw.prod_prob ρ σ (fun a _ => P a)]
  unfold FiniteLaw.prob
  apply Finset.sum_congr rfl
  intro a _
  by_cases h : P a
  · simp [h, σ.total]
  · simp [h]

private theorem prob_inter_good_lower
    {A : Type*} [Fintype A] (ρ : FiniteLaw A)
    (Yevent Good : A → Prop) (v b : ℝ)
    (hY : v ≤ ρ.prob Yevent)
    (hbad : ρ.prob (fun x => ¬ Good x) ≤ b) :
    v - b ≤ ρ.prob (fun x => Yevent x ∧ Good x) := by
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
  {D q₁ q₂ s : ℕ} [NeZero s] [NeZero q₁] [NeZero q₂]
  {μX : PositiveRationalLaw X} {μY : PositiveRationalLaw Y}
  (src : Sources (D := D) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY)
  {μI : PositiveRationalLaw I} {w m : ℕ}
  (streams : Sources.InternalStreams src μI w)

/-- A first-Bob child with ambient mass `θ/2` and the verified 256th-moment
numerical guard has a fixed complete metadata/base configuration. At least
half the selected original positions are template flags, and its independent
selector section has mass `θ/4`. -/
theorem incoming_complete_template_section
    (e : Fin m → Fin w) (he : Function.Injective e)
    (Ystar : Set (streams.metadataStream.Label ×
      (streams.baseStream.Label × streams.selectorStream.Label)))
    (θ : ℝ) (hθ : 0 < θ) (hD : 8*256 ≤ D)
    (hYstar : θ/2 ≤ streams.law.toFiniteLaw.prob (· ∈ Ystar))
    (hguard : 2 * ((64 : ℝ) * m) ^ 128 /
      (((255 / 256 : ℝ) - 1/2) * m) ^ 256 ≤ θ/4) :
    ∃ md : streams.metadataStream.Label,
      (m : ℝ) / 2 ≤
        (∑ i : Fin m,
          if isTemplateFlag (streams.metadataStream.decode md (e i))
          then (1 : ℝ) else 0) ∧
      ∃ base : streams.baseStream.Label,
        θ/4 ≤ streams.selectorStream.law.toFiniteLaw.prob
          (fun sel => (md, (base, sel)) ∈ Ystar) := by
  let ρ := streams.metadataStream.law.toFiniteLaw
  let σ := streams.baseStream.law.toFiniteLaw
  let τ := streams.selectorStream.law.toFiniteLaw
  let bad : streams.metadataStream.Label → Prop := fun md =>
    (∑ i : Fin m,
      if isTemplateFlag (streams.metadataStream.decode md (e i))
      then (1 : ℝ) else 0) < (m : ℝ) / 2
  have hbad : ρ.prob bad ≤ θ/4 := by
    exact (metadata_half_template_tail src streams hD e he).trans hguard
  have hlaw : streams.law.toFiniteLaw = ρ.prod (σ.prod τ) := by
    simp [ρ, σ, τ, Sources.InternalStreams.law,
      PositiveRationalLaw.toFiniteLaw_prod]
  have hbadTotal : streams.law.toFiniteLaw.prob
      (fun a => bad a.1) ≤ θ/4 := by
    rw [hlaw, finite_prod_prob_fst]
    exact hbad
  have hgood : θ/4 ≤ streams.law.toFiniteLaw.prob
      (fun a => a ∈ Ystar ∧ ¬ bad a.1) := by
    have h := prob_inter_good_lower streams.law.toFiniteLaw
      (· ∈ Ystar) (fun a => ¬ bad a.1) (θ/2) (θ/4)
      hYstar (by simpa using hbadTotal)
    convert h using 1 <;> ring
  obtain ⟨md, hmd, base, hsection⟩ :=
    exists_complete_stream_section src streams Ystar
      (fun md => ¬ bad md) (θ/4) (by linarith) hgood
  exact ⟨md, le_of_not_gt hmd, base, hsection⟩

#print axioms incoming_complete_template_section

end CurrentAdditive.DeterministicIndexedMatrix
