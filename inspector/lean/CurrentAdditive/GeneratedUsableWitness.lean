import CurrentAdditive.GeneratedGraphBranch

/-!
An assigned graph collision outside the actual generated-source deficits has
all the head groups and three item groups needed by the checked collision
cost theorem. The branch row set is the original retained indexed row set
intersected with the actual common-prefix label.
-/

namespace CurrentAdditive.DeterministicIndexedMatrix.Sources

open Paper2 Paper2.SourceMatrix Paper2.SourceDeficiencyTemplate
open Paper2.SourceSurvivingCollisions Paper2.SourceDeficiency
open Paper2.SourceProjectionDiagonal

variable {G E X Y : Type*} [Fintype G] [Nonempty G] [Fintype E]
  [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]
  {D q₁ q₂ s : ℕ} [NeZero s] [NeZero q₁] [NeZero q₂]
  {μX : PositiveRationalLaw X} {μY : PositiveRationalLaw Y}
  (src : Sources (D := D) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY)

def indexedBranchRows
    (V : Set (Row (I := SourceConstruction.Items s G) src))
    (rowCode : Row (I := SourceConstruction.Items s G) src → Fin s)
    (j : Fin s) : Set (Row (I := SourceConstruction.Items s G) src) :=
  {row | row ∈ V ∧ rowCode row = j}

theorem projected_label_image_event (K : Set src.inner.Label)
    (α : Fin q₂) (r : Fin q₁) :
    (fun u : X => projectedAt
      (fun t : Template q₁ q₂ X => ∃ z ∈ K, src.inner.decode z = t)
      α (r, u)) =
    (fun u : X => (r,u) ∈ (fun z => src.inner.decode z α) '' K) := by
  funext u
  apply propext
  constructor
  · rintro ⟨t, ⟨z, hz, rfl⟩, hval⟩
    exact ⟨z, hz, hval⟩
  · rintro ⟨z, hz, hval⟩
    exact ⟨src.inner.decode z, ⟨z, hz, rfl⟩, hval⟩

theorem usable_assigned_collision_data
    (order : SourceConstruction.Items s G ≃
      Fin (Fintype.card (SourceConstruction.Items s G)))
    (edge : E → Bool → G) (hs : 4 ≤ s) (r : ℕ)
    (hq : q₂ = SourceItems.sourceQ0 (Fin (4*s)) E * r)
    (ρ : ℝ) (hscale : 4 * (s : ℝ)^2 * ρ ≤ 1)
    (V : Set (Row (I := SourceConstruction.Items s G) src))
    (rowCode : Row (I := SourceConstruction.Items s G) src → Fin s)
    (K : Set src.inner.Label) (U : Set (Column src))
    (j : Fin s) (α : Fin q₂)
    (hα : α ∈ assignedCoordinates edge r hq μX
      (rawItemShadow src V) (rawItemCode src rowCode) j \
        branchBad src K U (2 * (s : ℝ) * ρ)) :
    (∀ r : Fin q₁, 2 * (s : ℝ) * ρ ≤ μX.toFiniteLaw.prob
      (fun u => (r,u) ∈ (fun z => src.inner.decode z α) '' K)) ∧
    ∃ i₁ i₂ i₀ : SourceConstruction.Items s G, ∃ p p' : Fin s,
      p ≠ p' ∧
      SourceConstruction.activity order edge (by omega : 3 ≤ s) r hq i₁ α = some p ∧
      SourceConstruction.activity order edge (by omega : 3 ≤ s) r hq i₂ α = some p' ∧
      SourceConstruction.activity order edge (by omega : 3 ≤ s) r hq i₀ α = none ∧
      ∀ t : Fin 3, 2 * (s : ℝ) * ρ ≤ μX.toFiniteLaw.prob
        (fun u => Sum.inr (collisionItem i₁ i₂ i₀ t, u) ∈
          indexedBranchRows src V rowCode j) := by
  classical
  have hα' := Finset.mem_sdiff.mp hα
  have hgood := (usable_coordinate_masses src K U
    (2 * (s : ℝ) * ρ) α hα'.2).1
  have hhead : ∀ r : Fin q₁, 2 * (s : ℝ) * ρ ≤ μX.toFiniteLaw.prob
      (fun u => (r,u) ∈ (fun z => src.inner.decode z α) '' K) := by
    intro r
    rw [← projected_label_image_event src K α r]
    exact hgood r
  obtain ⟨i₁, i₂, i₀, p, p', _, hpp, h₁, h₂, h₀,
      hm₁, hm₂, hm₀⟩ :=
    assignedCoordinates_items order edge (by omega : 3 ≤ s) r hq μX
      (rawItemShadow src V) (rawItemCode src rowCode) j α hα'.1 ρ hscale
  refine ⟨hhead, i₁, i₂, i₀, p, p', hpp, h₁, h₂, h₀, ?_⟩
  intro t
  fin_cases t
  · simpa only [indexedBranchRows, Set.mem_setOf_eq,
      raw_shadow_item_branch_mass] using hm₁
  · simpa only [indexedBranchRows, Set.mem_setOf_eq,
      raw_shadow_item_branch_mass] using hm₂
  · simpa only [indexedBranchRows, Set.mem_setOf_eq,
      raw_shadow_item_branch_mass] using hm₀

end CurrentAdditive.DeterministicIndexedMatrix.Sources

#print axioms CurrentAdditive.DeterministicIndexedMatrix.Sources.projected_label_image_event
#print axioms CurrentAdditive.DeterministicIndexedMatrix.Sources.usable_assigned_collision_data
