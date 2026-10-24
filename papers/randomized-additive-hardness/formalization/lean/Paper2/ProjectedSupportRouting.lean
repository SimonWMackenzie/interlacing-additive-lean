import Mathlib

/-!
# Finite routing counts for projection-aware raw supports

At a row query, an ordinary coordinate follows its chosen child. A splitting
attachment leaves an ordinary coordinate in both children, but ceases to be
an attachment. This file concerns only those finite index sets. In particular
it asserts no disjointness or mass identity for images of raw row supports.
Frozen v12, Section 5, `res:two-stream`, lines 134–201.
-/

namespace Paper2.ProjectedSupportRouting

variable {I : Type*}
variable [DecidableEq I]

/-- Ordinary coordinates routed to physical child `b`. A split coordinate is
present in both children. -/
noncomputable def childCoordinates (Q split : Finset I) (choose : I → Bool)
    (b : Bool) : Finset I := by
  classical
  exact Q.filter fun i => choose i = b ∨ i ∈ split

/-- Unsplit attachments follow their chosen child; split attachments vanish. -/
noncomputable def childAttachments (Z split : Finset I) (choose : I → Bool)
    (b : Bool) : Finset I := by
  classical
  exact Z.filter fun i => choose i = b ∧ i ∉ split

@[simp] theorem mem_childCoordinates (Q split : Finset I) (choose : I → Bool)
    (b : Bool) (i : I) :
    i ∈ childCoordinates Q split choose b ↔
      i ∈ Q ∧ (choose i = b ∨ i ∈ split) := by
  classical
  simp [childCoordinates]

@[simp] theorem mem_childAttachments (Z split : Finset I) (choose : I → Bool)
    (b : Bool) (i : I) :
    i ∈ childAttachments Z split choose b ↔
      i ∈ Z ∧ choose i = b ∧ i ∉ split := by
  classical
  simp [childAttachments]

theorem childCoordinates_subset (Q split : Finset I) (choose : I → Bool)
    (b : Bool) : childCoordinates Q split choose b ⊆ Q := by
  intro i hi
  exact (mem_childCoordinates Q split choose b i).mp hi |>.1

theorem childAttachments_subset (Z split : Finset I) (choose : I → Bool)
    (b : Bool) : childAttachments Z split choose b ⊆ Z := by
  intro i hi
  exact (mem_childAttachments Z split choose b i).mp hi |>.1

theorem childAttachments_subset_childCoordinates (Q Z split : Finset I)
    (choose : I → Bool) (b : Bool) (hZ : Z ⊆ Q) :
    childAttachments Z split choose b ⊆ childCoordinates Q split choose b := by
  intro i hi
  exact (mem_childCoordinates Q split choose b i).mpr
    ⟨hZ ((mem_childAttachments Z split choose b i).mp hi).1,
      Or.inl ((mem_childAttachments Z split choose b i).mp hi).2.1⟩

theorem childCoordinates_union (Q split : Finset I) (choose : I → Bool) :
    childCoordinates Q split choose false ∪
      childCoordinates Q split choose true = Q := by
  ext i
  simp only [Finset.mem_union, mem_childCoordinates]
  cases choose i <;> simp <;> tauto

theorem childCoordinates_inter (Q split : Finset I) (choose : I → Bool)
    (h : split ⊆ Q) :
    childCoordinates Q split choose false ∩
      childCoordinates Q split choose true = split := by
  ext i
  simp only [Finset.mem_inter, mem_childCoordinates]
  have hi : i ∈ split → i ∈ Q := fun hs => h hs
  cases choose i <;> simp <;> tauto

theorem childCoordinates_card (Q split : Finset I) (choose : I → Bool)
    (h : split ⊆ Q) :
    (childCoordinates Q split choose false).card +
      (childCoordinates Q split choose true).card = Q.card + split.card := by
  classical
  have hc := Finset.card_union_add_card_inter
    (childCoordinates Q split choose false)
    (childCoordinates Q split choose true)
  rw [childCoordinates_union, childCoordinates_inter Q split choose h] at hc
  exact hc.symm

theorem childAttachments_disjoint (Z split : Finset I) (choose : I → Bool) :
    Disjoint (childAttachments Z split choose false)
      (childAttachments Z split choose true) := by
  apply Finset.disjoint_left.mpr
  intro i hl hr
  have h0 := ((mem_childAttachments Z split choose false i).mp hl).2.1
  have h1 := ((mem_childAttachments Z split choose true i).mp hr).2.1
  simp [h0] at h1

theorem childAttachments_union (Z split : Finset I) (choose : I → Bool) :
    childAttachments Z split choose false ∪
      childAttachments Z split choose true = Z \ split := by
  ext i
  simp only [Finset.mem_union, mem_childAttachments, Finset.mem_sdiff]
  cases choose i <;> simp

theorem childAttachments_card (Z split : Finset I) (choose : I → Bool)
    (h : split ⊆ Z) :
    (childAttachments Z split choose false).card +
      (childAttachments Z split choose true).card + split.card = Z.card := by
  classical
  rw [← Finset.card_union_of_disjoint (childAttachments_disjoint Z split choose),
    childAttachments_union]
  exact Finset.card_sdiff_add_card_eq_card h

end Paper2.ProjectedSupportRouting
