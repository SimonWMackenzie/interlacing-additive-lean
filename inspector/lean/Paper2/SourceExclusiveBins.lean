import Mathlib

/-!
# Exclusive bins in the source construction

Source: frozen Paper 2 v12, source item witness argument (T11).

Items belong to groups and are assigned bins.  A group is exclusive if a
nonempty retained bin contains only its items.  Distinct exclusive groups
require distinct bins.  In every other group, each retained item shares its
bin with a retained item of another group.  This file proves only this finite
combinatorial component, independently of the graph construction.
-/

namespace Paper2.SourceExclusiveBins

variable {G I B : Type*}

/-- A group owns all retained items in at least one nonempty bin. -/
def IsExclusive (owner : I → G) (bin : I → B) (K : Finset I) (g : G) : Prop :=
  ∃ b : B, (∃ i ∈ K, owner i = g ∧ bin i = b) ∧
    ∀ j ∈ K, bin j = b → owner j = g

/-- The actual set of exclusive groups for the retained items. -/
noncomputable def exclusiveGroups [Fintype G] (owner : I → G) (bin : I → B) (K : Finset I) :
    Finset G := by
  classical
  exact Finset.univ.filter (IsExclusive owner bin K)

@[simp] theorem mem_exclusiveGroups [Fintype G] (owner : I → G) (bin : I → B) (K : Finset I)
    (g : G) : g ∈ exclusiveGroups owner bin K ↔ IsExclusive owner bin K g := by
  classical
  simp [exclusiveGroups]

/-- Choosing an exclusively owned bin injects the exclusive groups into bins. -/
theorem card_exclusiveGroups_le [Fintype G] [Fintype B]
    (owner : I → G) (bin : I → B) (K : Finset I) :
    (exclusiveGroups owner bin K).card ≤ Fintype.card B := by
  classical
  let f : {g : G // IsExclusive owner bin K g} → B := fun g => g.property.choose
  have hf : Function.Injective f := by
    intro g h heq
    apply Subtype.ext
    obtain ⟨i, hi, howner, hbin⟩ := g.property.choose_spec.1
    have hb : bin i = h.property.choose := hbin.trans heq
    exact howner.symm.trans (h.property.choose_spec.2 i hi hb)
  simpa [exclusiveGroups, Fintype.card_subtype] using Fintype.card_le_of_injective f hf

/-- Without an exclusive bin, every retained item has a foreign companion. -/
theorem exists_foreign_of_not_exclusive (owner : I → G) (bin : I → B) (K : Finset I)
    {g : G} (hg : ¬ IsExclusive owner bin K g) {i : I} (hi : i ∈ K)
    (howner : owner i = g) :
    ∃ j ∈ K, bin j = bin i ∧ owner j ≠ g := by
  classical
  by_contra! h
  exact hg ⟨bin i, ⟨i, hi, howner, rfl⟩, h⟩

/-- The preceding witness has a different owner from the starting item. -/
theorem exists_foreign_of_not_mem [Fintype G]
    (owner : I → G) (bin : I → B) (K : Finset I)
    {i : I} (hi : i ∈ K) (hg : owner i ∉ exclusiveGroups owner bin K) :
    ∃ j ∈ K, bin j = bin i ∧ owner j ≠ owner i := by
  exact exists_foreign_of_not_exclusive owner bin K
    (fun h => hg ((mem_exclusiveGroups owner bin K (owner i)).mpr h)) hi rfl

end Paper2.SourceExclusiveBins
