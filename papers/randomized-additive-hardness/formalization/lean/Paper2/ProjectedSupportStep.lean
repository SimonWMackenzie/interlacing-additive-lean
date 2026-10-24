import Paper2.ProjectedSupportMass
import Paper2.ProjectedSupportRouting

/-!
# One physical query with overlapping selector images

Frozen v12, Section 5, `res:two-stream`. Choices use the selector-image
law; supports remain the actual original-row query fibres. Splitting an
attachment removes that attachment but keeps both raw child supports.
Unsplit attachments lose little mass in their original ambient raw law.
-/

namespace Paper2.ProjectedSupportStep

variable {I W S : Type*} [Fintype S]

noncomputable def splits (μ : FiniteLaw S) (σ : I → W → S)
    (Z : Finset I) (F : I → Finset W) (query : I → W → Bool) (t : ℝ) :
    Finset I := by
  classical
  exact Z.filter fun i => Both μ (σ i) (F i) (query i) t

noncomputable def childCoordinates (μ : FiniteLaw S) (σ : I → W → S)
    (Q Z : Finset I) (F : I → Finset W) (query : I → W → Bool)
    (t : ℝ) (b : Bool) : Finset I := by
  classical
  exact ProjectedSupportRouting.childCoordinates Q (splits μ σ Z F query t)
    (fun i => heavyBit μ (σ i) (F i) (query i)) b

noncomputable def childAttachments (μ : FiniteLaw S) (σ : I → W → S)
    (Z : Finset I) (F : I → Finset W) (query : I → W → Bool)
    (t : ℝ) (b : Bool) : Finset I := by
  classical
  exact ProjectedSupportRouting.childAttachments Z (splits μ σ Z F query t)
    (fun i => heavyBit μ (σ i) (F i) (query i)) b

noncomputable def childSupport (F : I → Finset W) (query : I → W → Bool)
    (b : Bool) (i : I) : Finset W := fibre (F i) (query i) b

omit [Fintype S] in
@[simp] theorem mem_childSupport (F : I → Finset W) (query : I → W → Bool)
    (b : Bool) (i : I) (w : W) :
    w ∈ childSupport F query b i ↔ w ∈ F i ∧ query i w = b :=
  mem_fibre (F i) (query i) b w

@[simp] theorem mem_splits (μ : FiniteLaw S) (σ : I → W → S)
    (Z : Finset I) (F : I → Finset W) (query : I → W → Bool) (t : ℝ) (i : I) :
    i ∈ splits μ σ Z F query t ↔ i ∈ Z ∧ Both μ (σ i) (F i) (query i) t := by
  classical
  simp [splits]

@[simp] theorem mem_childCoordinates (μ : FiniteLaw S) (σ : I → W → S)
    (Q Z : Finset I) (F : I → Finset W) (query : I → W → Bool)
    (t : ℝ) (b : Bool) (i : I) :
    i ∈ childCoordinates μ σ Q Z F query t b ↔
      i ∈ Q ∧ (i ∈ splits μ σ Z F query t ∨
        heavyBit μ (σ i) (F i) (query i) = b) := by
  classical
  simp only [childCoordinates, ProjectedSupportRouting.mem_childCoordinates, or_comm]

@[simp] theorem mem_childAttachments (μ : FiniteLaw S) (σ : I → W → S)
    (Z : Finset I) (F : I → Finset W) (query : I → W → Bool)
    (t : ℝ) (b : Bool) (i : I) :
    i ∈ childAttachments μ σ Z F query t b ↔
      i ∈ Z ∧ i ∉ splits μ σ Z F query t ∧
        heavyBit μ (σ i) (F i) (query i) = b := by
  classical
  simp only [childAttachments, ProjectedSupportRouting.mem_childAttachments]
  tauto

theorem splits_subset (μ : FiniteLaw S) (σ : I → W → S)
    (Z : Finset I) (F : I → Finset W) (query : I → W → Bool) (t : ℝ) :
    splits μ σ Z F query t ⊆ Z := by
  intro i hi
  exact ((mem_splits μ σ Z F query t i).mp hi).1

theorem childCoordinates_subset (μ : FiniteLaw S) (σ : I → W → S)
    (Q Z : Finset I) (F : I → Finset W) (query : I → W → Bool)
    (t : ℝ) (b : Bool) : childCoordinates μ σ Q Z F query t b ⊆ Q := by
  intro i hi
  exact ((mem_childCoordinates μ σ Q Z F query t b i).mp hi).1

theorem childAttachments_subset (μ : FiniteLaw S) (σ : I → W → S)
    (Q Z : Finset I) (F : I → Finset W) (query : I → W → Bool)
    (t : ℝ) (b : Bool) (hZ : Z ⊆ Q) :
    childAttachments μ σ Z F query t b ⊆ childCoordinates μ σ Q Z F query t b := by
  intro i hi
  obtain ⟨hiZ, _, hb⟩ := (mem_childAttachments μ σ Z F query t b i).mp hi
  exact (mem_childCoordinates μ σ Q Z F query t b i).mpr ⟨hZ hiZ, Or.inr hb⟩

theorem child_floor (μ : FiniteLaw S) (σ : I → W → S)
    (Q Z : Finset I) (F : I → Finset W) (query : I → W → Bool)
    (t : ℝ) (b : Bool) (hfloor : ∀ i ∈ Q, 2 * t ≤ mass μ (σ i) (F i)) :
    ∀ i ∈ childCoordinates μ σ Q Z F query t b,
      t ≤ mass μ (σ i) (childSupport F query b i) := by
  intro i hi
  obtain ⟨hiQ, hs | hb⟩ := (mem_childCoordinates μ σ Q Z F query t b i).mp hi
  · have hh := ((mem_splits μ σ Z F query t i).mp hs).2
    cases b
    · exact hh.1
    · exact hh.2
  · unfold childSupport
    rw [← hb]
    exact heavy_floor μ (σ i) (F i) (query i) t (hfloor i hiQ)

theorem childSupport_reaches {C : Type*} (μ : FiniteLaw S) (σ : I → W → S)
    (Q Z : Finset I) (F : I → Finset W) (input : I → W → C)
    (query : C → Bool) (U : Set C) (t : ℝ) (b : Bool)
    (hret : ∀ i ∈ Q, ∀ w ∈ F i, input i w ∈ U) :
    ∀ i ∈ childCoordinates μ σ Q Z F (fun i w => query (input i w)) t b,
      ∀ w ∈ childSupport F (fun i w => query (input i w)) b i,
        input i w ∈ U ∧ query (input i w) = b := by
  intro i hi w hw
  obtain ⟨hw, hb⟩ := (mem_childSupport F _ b i w).mp hw
  exact ⟨hret i (childCoordinates_subset μ σ Q Z F _ t b hi) w hw, hb⟩

theorem childSupport_nonempty (μ : FiniteLaw S) (σ : I → W → S)
    (Q Z : Finset I) (F : I → Finset W) (query : I → W → Bool)
    (t : ℝ) (b : Bool) (ht : 0 < t)
    (hfloor : ∀ i ∈ Q, 2 * t ≤ mass μ (σ i) (F i)) :
    ∀ i ∈ childCoordinates μ σ Q Z F query t b, (childSupport F query b i).Nonempty := by
  intro i hi
  have hf := child_floor μ σ Q Z F query t b hfloor i hi
  by_contra hn
  have he := Finset.not_nonempty_iff_eq_empty.mp hn
  rw [he, mass_empty] at hf
  linarith

/-- Unsplit attachment loss is in the ambient raw-row law. Only that law's
query fibres partition; the image law was used solely for an upper bound. -/
theorem attachment_loss [Fintype W] (κ : FiniteLaw W) (μ : FiniteLaw S)
    (σ : I → W → S) (Z : Finset I) (F : I → Finset W)
    (query : I → W → Bool) (t : ℝ) (b : Bool) (i : I)
    (hσ : κ.PushesTo μ (σ i)) (hi : i ∈ childAttachments μ σ Z F query t b) :
    SourceSupportStep.mass κ (F i) -
      SourceSupportStep.mass κ (childSupport F query b i) < t := by
  obtain ⟨hiZ, hns, hb⟩ := (mem_childAttachments μ σ Z F query t b i).mp hi
  have hn : ¬ Both μ (σ i) (F i) (query i) t := by
    intro hh
    exact hns ((mem_splits μ σ Z F query t i).mpr ⟨hiZ, hh⟩)
  have ho := other_lt_of_not_both μ (σ i) (F i) (query i) t hn
  have hr := raw_mass_le κ μ (σ i) hσ (fibre (F i) (query i) (!(heavyBit μ (σ i) (F i) (query i))))
  have hp : SourceSupportStep.mass κ (fibre (F i) (query i) (heavyBit μ (σ i) (F i) (query i))) +
      SourceSupportStep.mass κ (fibre (F i) (query i) (!(heavyBit μ (σ i) (F i) (query i)))) =
        SourceSupportStep.mass κ (F i) := by
    cases heavyBit μ (σ i) (F i) (query i) <;>
      simpa [add_comm] using SourceSupportStep.mass_partition κ (F i) (query i)
  unfold childSupport
  rw [← hb]
  linarith

/-- An ambient surviving-mass invariant propagates with exact halving. -/
theorem attachment_floor [Fintype W] (κ : I → FiniteLaw W) (μ : FiniteLaw S)
    (σ : I → W → S) (Z : Finset I) (F : I → Finset W)
    (query : I → W → Bool) (t : ℝ) (base : I → ℝ) (b : Bool)
    (hσ : ∀ i ∈ Z, (κ i).PushesTo μ (σ i))
    (h : ∀ i ∈ Z, base i + 2 * t ≤ SourceSupportStep.mass (κ i) (F i)) :
    ∀ i ∈ childAttachments μ σ Z F query t b,
      base i + t ≤ SourceSupportStep.mass (κ i) (childSupport F query b i) := by
  intro i hi
  have hiZ := ((mem_childAttachments μ σ Z F query t b i).mp hi).1
  have hl := attachment_loss (κ i) μ σ Z F query t b i (hσ i hiZ) hi
  have hf := h i hiZ
  linarith

theorem childCoordinates_card (μ : FiniteLaw S) (σ : I → W → S)
    (Q Z : Finset I) (F : I → Finset W) (query : I → W → Bool)
    (t : ℝ) (hZ : Z ⊆ Q) :
    (childCoordinates μ σ Q Z F query t false).card +
      (childCoordinates μ σ Q Z F query t true).card =
        Q.card + (splits μ σ Z F query t).card := by
  classical
  exact ProjectedSupportRouting.childCoordinates_card Q _ _
    ((splits_subset μ σ Z F query t).trans hZ)

theorem childAttachments_card (μ : FiniteLaw S) (σ : I → W → S)
    (Z : Finset I) (F : I → Finset W) (query : I → W → Bool) (t : ℝ) :
    (childAttachments μ σ Z F query t false).card +
      (childAttachments μ σ Z F query t true).card +
        (splits μ σ Z F query t).card = Z.card := by
  classical
  exact ProjectedSupportRouting.childAttachments_card Z _ _ (splits_subset μ σ Z F query t)

end Paper2.ProjectedSupportStep
