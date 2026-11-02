import CurrentAdditive.DeterministicIndexedProfileMass
import Paper2.SourceProfilesInner

/-!
Appendix I `det:profiles`: population selection after the conditioning
exceptional set is removed. The selected block labels are original labels of
the constructed matrices. This module makes no protocol-cost assumption.
-/

namespace CurrentAdditive.DeterministicIndexedMatrix

open Paper2 Paper2.SourcePopulation Paper2.SourceProfilesInner

/-- If the retained population can pay for `n` qualifying blocks plus the
exceptional positions, choose `n` original good labels. -/
theorem select_avoiding_exceptions
    {Z : Type*} [Fintype Z] [DecidableEq Z]
    (μ : PositiveRationalLaw Z) (q n : ℕ) [NeZero q]
    (U : Set (Fin q × Z)) (E : Finset (Fin q)) (β t : ℝ)
    (ht : t < 1)
    (hU : β ≤ ((PositiveRationalLaw.uniform (Fin q)).prod μ).toFiniteLaw.prob
      (· ∈ U))
    (hbudget : ((n + E.card : ℕ) : ℝ) * (1 - t) ≤
      (q : ℝ) * (β - t)) :
    ∃ e : Fin n ↪ Fin q,
      (∀ j, e j ∉ E) ∧
      (∀ j, t ≤ μ.toFiniteLaw.prob (fun z => (e j, z) ∈ U)) := by
  classical
  let mass : Fin q → ℝ := fun i => μ.toFiniteLaw.prob (fun z => (i,z) ∈ U)
  have hq : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
  have htotal : (q : ℝ) * β ≤ ∑ i : Fin q, mass i := by
    rw [Paper2.SourceProjection.inner_block_average μ U] at hU
    have h := mul_le_mul_of_nonneg_left hU hq.le
    simpa only [← mul_assoc, mul_inv_cancel₀ hq.ne', one_mul] using h
  have hcard : n + E.card ≤ (qualifying mass t).card := by
    have hsum := sum_le_population mass t
      (fun i => μ.toFiniteLaw.prob_le_one _)
    simp only [Fintype.card_fin] at hsum
    have hr : ((n + E.card : ℕ) : ℝ) ≤ ((qualifying mass t).card : ℝ) := by
      nlinarith
    exact_mod_cast hr
  let Good := qualifying mass t \ E
  have hcover : qualifying mass t ⊆ Good ∪ E := by
    intro i hi
    by_cases he : i ∈ E
    · exact Finset.mem_union_right _ he
    · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hi, he⟩)
  have hgood : n ≤ Good.card := by
    have hbound := (Finset.card_le_card hcover).trans
      (Finset.card_union_le Good E)
    omega
  have hfin : n ≤ Fintype.card Good := by
    simpa only [Fintype.card_coe] using hgood
  let pick : Fin n → Good := fun j =>
    (Fintype.equivFin Good).symm
      ⟨j.val, lt_of_lt_of_le j.isLt hfin⟩
  have hpick : Function.Injective pick := by
    intro i j hij
    have h := (Fintype.equivFin Good).symm.injective hij
    exact Fin.ext (congrArg
      (fun z : Fin (Fintype.card Good) => z.val) h)
  refine ⟨⟨fun j => (pick j).val, Subtype.val_injective.comp hpick⟩, ?_, ?_⟩
  · intro j
    exact (Finset.mem_sdiff.mp (pick j).property).2
  · intro j
    exact (mem_qualifying mass t _).mp
      (Finset.mem_sdiff.mp (pick j).property).1

/-- The first profile rung selects actual first-level head positions from a
retained subset of the indexed `M₁` row alphabet. -/
theorem Sources.M₁_select_good_heads
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    {D q₁ q₂ s : ℕ} [NeZero q₁] [NeZero q₂] [NeZero s]
    {μX : PositiveRationalLaw X} {μY : PositiveRationalLaw Y}
    (src : Sources (D := D) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY)
    (U : Set (Fin q₁ × X)) (E : Finset (Fin q₁))
    (a n : ℕ) (β ρ : ℝ)
    (ht : (2 : ℝ)^a * ρ < 1)
    (hU : β ≤ ((PositiveRationalLaw.uniform (Fin q₁)).prod μX).toFiniteLaw.prob
      (· ∈ U))
    (hbudget : ((n + E.card : ℕ) : ℝ) * (1 - (2 : ℝ)^a * ρ) ≤
      (q₁ : ℝ) * (β - (2 : ℝ)^a * ρ)) :
    ∃ e : Fin n ↪ Fin q₁,
      (∀ j, e j ∉ E) ∧
      (∀ j, (2 : ℝ)^a * ρ ≤ μX.toFiniteLaw.prob
        (fun u => (e j,u) ∈ U)) := by
  exact select_avoiding_exceptions μX q₁ n U E β ((2 : ℝ)^a * ρ)
    ht hU hbudget

/-- The second profile rung selects original positions of the inner source.
Its base alphabet is the indexed Gamma list, including duplicate words. -/
theorem Sources.T_select_good_positions
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    {D q₁ q₂ s : ℕ} [NeZero q₁] [NeZero q₂] [NeZero s]
    {μX : PositiveRationalLaw X} {μY : PositiveRationalLaw Y}
    (src : Sources (D := D) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY)
    (U : Set (Fin q₂ × src.gamma.Label)) (E : Finset (Fin q₂))
    (a n : ℕ) (β x : ℝ)
    (ht : (2 : ℝ)^a * x < 1)
    (hU : β ≤ ((PositiveRationalLaw.uniform (Fin q₂)).prod
      src.gamma.law).toFiniteLaw.prob (· ∈ U))
    (hbudget : ((n + E.card : ℕ) : ℝ) * (1 - (2 : ℝ)^a * x) ≤
      (q₂ : ℝ) * (β - (2 : ℝ)^a * x)) :
    ∃ e : Fin n ↪ Fin q₂,
      (∀ j, e j ∉ E) ∧
      (∀ j, (2 : ℝ)^a * x ≤ src.gamma.law.toFiniteLaw.prob
        (fun γ => (e j,γ) ∈ U)) := by
  exact select_avoiding_exceptions src.gamma.law q₂ n U E β
    ((2 : ℝ)^a * x) ht hU hbudget

/-- The third rung starts from an actual retained subset of the raw row
alphabet, discards the source-item mass, and selects surviving template bins.
The ambient template law remains uniform over bins and indexed inner labels. -/
theorem Sources.Nref_select_good_bins
    {G V A X Y : Type*} [Fintype G] [Fintype V] [Fintype A]
    [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]
    {D q₁ q₂ s : ℕ} [NeZero q₁] [NeZero q₂] [NeZero s]
    {μX : PositiveRationalLaw X} {μY : PositiveRationalLaw Y}
    (src : Sources (D := D) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY)
    (μI : PositiveRationalLaw (G × (V ⊕ A)))
    (U : Set (Row (I := G × (V ⊕ A)) src)) (E : Finset (Fin s))
    (a n : ℕ) (β x : ℝ)
    (ht : (2 : ℝ)^a * x < 1)
    (hU : β ≤ (rowLaw src μI).toFiniteLaw.prob (· ∈ U))
    (hbudget : ((n + E.card : ℕ) : ℝ) * (1 - (2 : ℝ)^a * x) ≤
      (s : ℝ) * ((β - (1 - 255 / 256)) / (255 / 256) -
        (2 : ℝ)^a * x)) :
    ∃ e : Fin n ↪ Fin s,
      (∀ j, e j ∉ E) ∧
      (∀ j, (2 : ℝ)^a * x ≤ src.inner.law.toFiniteLaw.prob
        (fun z => Sum.inl (e j,z) ∈ U)) := by
  have htemplate := Sources.template_retained src μI U β hU
  exact select_avoiding_exceptions src.inner.law s n
    (fun pz => Sum.inl pz ∈ U) E
    ((β - (1 - 255 / 256)) / (255 / 256))
    ((2 : ℝ)^a * x) ht (by simpa [templateRowLaw] using htemplate)
    hbudget

end CurrentAdditive.DeterministicIndexedMatrix
