import Paper2.FiniteSampling

/-!
# One Bob step for actual diagonal word supports

Frozen v12, Section 4, `src:near-full`, the remaining-conversation
paragraph. Supports are sets of original word labels, and `query i w`
is the actual Bob bit on that coordinate and word. Ordinary supports
follow a heavier half (false wins ties). An attachment splits exactly
when both halves reach the next floor. This file proves the local
transition; it does not assume or construct a stopping frontier.
-/

namespace Paper2.SourceSupportStep

variable {I W : Type*} [Fintype W]

/-- Original-law mass of a finite set of full word labels. -/
noncomputable def mass (μ : FiniteLaw W) (S : Finset W) : ℝ :=
  μ.prob (fun w => w ∈ S)

/-- The actual message fibre, retaining the original labels. -/
noncomputable def fibre (S : Finset W) (query : W → Bool) (b : Bool) : Finset W := by
  classical
  exact S.filter fun w => query w = b

omit [Fintype W] in
@[simp] theorem mem_fibre (S : Finset W) (query : W → Bool) (b : Bool) (w : W) :
    w ∈ fibre S query b ↔ w ∈ S ∧ query w = b := by
  classical
  simp [fibre]

omit [Fintype W] in
theorem fibre_subset (S : Finset W) (query : W → Bool) (b : Bool) :
    fibre S query b ⊆ S := by
  intro w hw
  exact (mem_fibre S query b w).mp hw |>.1

theorem mass_partition (μ : FiniteLaw W) (S : Finset W) (query : W → Bool) :
    mass μ (fibre S query false) + mass μ (fibre S query true) = mass μ S := by
  classical
  unfold mass FiniteLaw.prob
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro w _
  cases h : query w <;> by_cases hw : w ∈ S <;> simp [h, hw]

/-- A fixed tie rule makes this one routing function, not an existential choice. -/
noncomputable def heavyBit (μ : FiniteLaw W) (S : Finset W) (query : W → Bool) : Bool :=
  if mass μ (fibre S query true) ≤ mass μ (fibre S query false) then false else true

theorem heavy_ge_other (μ : FiniteLaw W) (S : Finset W) (query : W → Bool) :
    mass μ (fibre S query (!(heavyBit μ S query))) ≤
      mass μ (fibre S query (heavyBit μ S query)) := by
  classical
  unfold heavyBit
  split_ifs with h <;> simp only [Bool.not_false, Bool.not_true]
  · exact h
  · exact (lt_of_not_ge h).le

theorem mass_partition_heavy (μ : FiniteLaw W) (S : Finset W) (query : W → Bool) :
    mass μ (fibre S query (heavyBit μ S query)) +
      mass μ (fibre S query (!(heavyBit μ S query))) = mass μ S := by
  cases heavyBit μ S query <;> simpa [add_comm] using mass_partition μ S query

theorem heavy_floor (μ : FiniteLaw W) (S : Finset W) (query : W → Bool)
    (t : ℝ) (h : 2 * t ≤ mass μ S) :
    t ≤ mass μ (fibre S query (heavyBit μ S query)) := by
  have hp := mass_partition_heavy μ S query
  have hg := heavy_ge_other μ S query
  linarith

/-- Both actual query fibres reach the next floor. -/
def Both (μ : FiniteLaw W) (S : Finset W) (query : W → Bool) (t : ℝ) : Prop :=
  t ≤ mass μ (fibre S query false) ∧ t ≤ mass μ (fibre S query true)

theorem other_lt_of_not_both (μ : FiniteLaw W) (S : Finset W)
    (query : W → Bool) (t : ℝ) (h : ¬ Both μ S query t) :
    mass μ (fibre S query (!(heavyBit μ S query))) < t := by
  by_contra hn
  have ho := le_of_not_gt hn
  have hh := ho.trans (heavy_ge_other μ S query)
  apply h
  cases hb : heavyBit μ S query <;> simp only [hb, Bool.not_false, Bool.not_true] at ho hh
  · exact ⟨hh, ho⟩
  · exact ⟨ho, hh⟩

/-- Exactly the attached coordinates whose actual support splits. -/
noncomputable def splits (μ : FiniteLaw W) (Z : Finset I)
    (S : I → Finset W) (query : I → W → Bool) (t : ℝ) : Finset I := by
  classical
  exact Z.filter fun i => Both μ (S i) (query i) t

/-- A child gets each ordinary support once, and each splitting support once. -/
noncomputable def childCoordinates (μ : FiniteLaw W) (Q Z : Finset I)
    (S : I → Finset W) (query : I → W → Bool) (t : ℝ) (b : Bool) : Finset I := by
  classical
  exact Q.filter fun i => i ∈ splits μ Z S query t ∨ heavyBit μ (S i) (query i) = b

/-- Attachments are removed on a split and otherwise follow their support. -/
noncomputable def childAttachments (μ : FiniteLaw W) (Z : Finset I)
    (S : I → Finset W) (query : I → W → Bool) (t : ℝ) (b : Bool) : Finset I := by
  classical
  exact Z.filter fun i => i ∉ splits μ Z S query t ∧ heavyBit μ (S i) (query i) = b

/-- The support in a child is the actual query fibre, not a replacement set. -/
noncomputable def childSupport (S : I → Finset W) (query : I → W → Bool)
    (b : Bool) (i : I) : Finset W := fibre (S i) (query i) b

omit [Fintype W] in
@[simp] theorem mem_childSupport (S : I → Finset W) (query : I → W → Bool)
    (b : Bool) (i : I) (w : W) :
    w ∈ childSupport S query b i ↔ w ∈ S i ∧ query i w = b := by
  exact mem_fibre (S i) (query i) b w

@[simp] theorem mem_splits (μ : FiniteLaw W) (Z : Finset I)
    (S : I → Finset W) (query : I → W → Bool) (t : ℝ) (i : I) :
    i ∈ splits μ Z S query t ↔ i ∈ Z ∧ Both μ (S i) (query i) t := by
  classical
  simp [splits]

@[simp] theorem mem_childCoordinates (μ : FiniteLaw W) (Q Z : Finset I)
    (S : I → Finset W) (query : I → W → Bool) (t : ℝ) (b : Bool) (i : I) :
    i ∈ childCoordinates μ Q Z S query t b ↔
      i ∈ Q ∧ (i ∈ splits μ Z S query t ∨ heavyBit μ (S i) (query i) = b) := by
  classical
  simp [childCoordinates]

@[simp] theorem mem_childAttachments (μ : FiniteLaw W) (Z : Finset I)
    (S : I → Finset W) (query : I → W → Bool) (t : ℝ) (b : Bool) (i : I) :
    i ∈ childAttachments μ Z S query t b ↔
      i ∈ Z ∧ i ∉ splits μ Z S query t ∧ heavyBit μ (S i) (query i) = b := by
  classical
  simp [childAttachments]

theorem childCoordinates_subset (μ : FiniteLaw W) (Q Z : Finset I)
    (S : I → Finset W) (query : I → W → Bool) (t : ℝ) (b : Bool) :
    childCoordinates μ Q Z S query t b ⊆ Q := by
  intro i hi
  exact (mem_childCoordinates μ Q Z S query t b i).mp hi |>.1

theorem childAttachments_subset (μ : FiniteLaw W) (Q Z : Finset I)
    (S : I → Finset W) (query : I → W → Bool) (t : ℝ) (b : Bool)
    (hZ : Z ⊆ Q) :
    childAttachments μ Z S query t b ⊆ childCoordinates μ Q Z S query t b := by
  intro i hi
  obtain ⟨hi, _, hb⟩ := (mem_childAttachments μ Z S query t b i).mp hi
  exact (mem_childCoordinates μ Q Z S query t b i).mpr ⟨hZ hi, Or.inr hb⟩

theorem child_floor (μ : FiniteLaw W) (Q Z : Finset I)
    (S : I → Finset W) (query : I → W → Bool) (t : ℝ) (b : Bool)
    (hfloor : ∀ i ∈ Q, 2 * t ≤ mass μ (S i)) :
    ∀ i ∈ childCoordinates μ Q Z S query t b,
      t ≤ mass μ (childSupport S query b i) := by
  intro i hi
  obtain ⟨hiQ, hs | hb⟩ := (mem_childCoordinates μ Q Z S query t b i).mp hi
  · have hh := ((mem_splits μ Z S query t i).mp hs).2
    cases b
    · exact hh.1
    · exact hh.2
  · unfold childSupport
    rw [← hb]
    exact heavy_floor μ (S i) (query i) t (hfloor i hiQ)

/-- Every routed word is still an original retained column and reaches
the indicated child of the actual Bob query. No representative is reselected. -/
theorem childSupport_reaches {C : Type*} (μ : FiniteLaw W) (Q Z : Finset I)
    (S : I → Finset W) (input : I → W → C) (query : C → Bool)
    (U : Set C) (t : ℝ) (b : Bool)
    (hret : ∀ i ∈ Q, ∀ w ∈ S i, input i w ∈ U) :
    ∀ i ∈ childCoordinates μ Q Z S (fun i w => query (input i w)) t b,
      ∀ w ∈ childSupport S (fun i w => query (input i w)) b i,
        input i w ∈ U ∧ query (input i w) = b := by
  intro i hi w hw
  obtain ⟨hw, hb⟩ := (mem_childSupport S _ b i w).mp hw
  exact ⟨hret i (childCoordinates_subset μ Q Z S _ t b hi) w hw, hb⟩

theorem childSupport_nonempty (μ : FiniteLaw W) (Q Z : Finset I)
    (S : I → Finset W) (query : I → W → Bool) (t : ℝ) (b : Bool)
    (ht : 0 < t) (hfloor : ∀ i ∈ Q, 2 * t ≤ mass μ (S i)) :
    ∀ i ∈ childCoordinates μ Q Z S query t b,
      (childSupport S query b i).Nonempty := by
  intro i hi
  have hf := child_floor μ Q Z S query t b hfloor i hi
  by_contra hn
  have he := Finset.not_nonempty_iff_eq_empty.mp hn
  simp [he, mass] at hf
  linarith

/-- An unsplit attachment loses strictly less than the next floor. -/
theorem attachment_loss (μ : FiniteLaw W) (Z : Finset I)
    (S : I → Finset W) (query : I → W → Bool) (t : ℝ) (b : Bool)
    (i : I) (hi : i ∈ childAttachments μ Z S query t b) :
    mass μ (S i) - mass μ (childSupport S query b i) < t := by
  obtain ⟨hiZ, hns, hb⟩ := (mem_childAttachments μ Z S query t b i).mp hi
  have hn : ¬ Both μ (S i) (query i) t := by
    intro hh
    exact hns ((mem_splits μ Z S query t i).mpr ⟨hiZ, hh⟩)
  have ho := other_lt_of_not_both μ (S i) (query i) t hn
  have hp := mass_partition_heavy μ (S i) (query i)
  unfold childSupport
  rw [← hb]
  linarith

/-- The finite-stage attachment invariant propagates without an infinite sum. -/
theorem attachment_floor (μ : FiniteLaw W) (Z : Finset I)
    (S : I → Finset W) (query : I → W → Bool) (t base : ℝ) (b : Bool)
    (h : ∀ i ∈ Z, base + 2 * t ≤ mass μ (S i)) :
    ∀ i ∈ childAttachments μ Z S query t b,
      base + t ≤ mass μ (childSupport S query b i) := by
  intro i hi
  have hl := attachment_loss μ Z S query t b i hi
  have hf := h i ((mem_childAttachments μ Z S query t b i).mp hi).1
  linarith

section Counts

variable [DecidableEq I]

omit [DecidableEq I] in
theorem splits_subset (μ : FiniteLaw W) (Z : Finset I)
    (S : I → Finset W) (query : I → W → Bool) (t : ℝ) :
    splits μ Z S query t ⊆ Z := by
  intro i hi
  exact ((mem_splits μ Z S query t i).mp hi).1

theorem childCoordinates_union (μ : FiniteLaw W) (Q Z : Finset I)
    (S : I → Finset W) (query : I → W → Bool) (t : ℝ) :
    childCoordinates μ Q Z S query t false ∪
      childCoordinates μ Q Z S query t true = Q := by
  ext i
  simp only [Finset.mem_union, mem_childCoordinates]
  cases heavyBit μ (S i) (query i) <;> simp <;> aesop

theorem childCoordinates_inter (μ : FiniteLaw W) (Q Z : Finset I)
    (S : I → Finset W) (query : I → W → Bool) (t : ℝ) (hZ : Z ⊆ Q) :
    childCoordinates μ Q Z S query t false ∩
      childCoordinates μ Q Z S query t true = splits μ Z S query t := by
  ext i
  simp only [Finset.mem_inter, mem_childCoordinates]
  have hs : i ∈ splits μ Z S query t → i ∈ Q :=
    fun hi => hZ (splits_subset μ Z S query t hi)
  cases heavyBit μ (S i) (query i) <;> simp_all <;> aesop

omit [DecidableEq I] in
theorem childCoordinates_card (μ : FiniteLaw W) (Q Z : Finset I)
    (S : I → Finset W) (query : I → W → Bool) (t : ℝ) (hZ : Z ⊆ Q) :
    (childCoordinates μ Q Z S query t false).card +
      (childCoordinates μ Q Z S query t true).card =
        Q.card + (splits μ Z S query t).card := by
  classical
  have hc := Finset.card_union_add_card_inter
    (childCoordinates μ Q Z S query t false)
    (childCoordinates μ Q Z S query t true)
  rw [childCoordinates_union, childCoordinates_inter μ Q Z S query t hZ] at hc
  exact hc.symm

omit [DecidableEq I] in
theorem childAttachments_disjoint (μ : FiniteLaw W) (Z : Finset I)
    (S : I → Finset W) (query : I → W → Bool) (t : ℝ) :
    Disjoint (childAttachments μ Z S query t false)
      (childAttachments μ Z S query t true) := by
  apply Finset.disjoint_left.mpr
  intro i hl hr
  have h0 := ((mem_childAttachments μ Z S query t false i).mp hl).2.2
  have h1 := ((mem_childAttachments μ Z S query t true i).mp hr).2.2
  simp [h0] at h1

theorem childAttachments_union (μ : FiniteLaw W) (Z : Finset I)
    (S : I → Finset W) (query : I → W → Bool) (t : ℝ) :
    childAttachments μ Z S query t false ∪
      childAttachments μ Z S query t true = Z \ splits μ Z S query t := by
  ext i
  simp only [Finset.mem_union, mem_childAttachments, Finset.mem_sdiff]
  cases heavyBit μ (S i) (query i) <;> simp

omit [DecidableEq I] in
theorem childAttachments_card (μ : FiniteLaw W) (Z : Finset I)
    (S : I → Finset W) (query : I → W → Bool) (t : ℝ) :
    (childAttachments μ Z S query t false).card +
      (childAttachments μ Z S query t true).card +
        (splits μ Z S query t).card = Z.card := by
  classical
  rw [← Finset.card_union_of_disjoint (childAttachments_disjoint μ Z S query t),
    childAttachments_union]
  exact Finset.card_sdiff_add_card_eq_card (splits_subset μ Z S query t)

end Counts

end Paper2.SourceSupportStep
