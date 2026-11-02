import CurrentAdditive.V38FullUsable
import Paper2.SourceSurvivingCollisionsItems
import Paper2.SourceProjectionDiagonal

/-! Derive actual edge-only collision coordinates from the graph gap and
the original retained rows. The item assignment is a single function
chosen before the activity coordinate. No collision witness is a premise.
Source v39/v38 robustness.tex:196--243 and src:item-witness. -/

namespace CurrentAdditive.V38EdgeCollisionGeometry

open Paper2 Paper2.SourceMatrix Paper2.SourceDeficiency
open Paper2.SourceSurvivingCollisions Paper2.SourceCollisionPartition
open CurrentAdditive.EdgeSourceMatrix
open scoped BigOperators

variable {V E X Y : Type*} [Fintype V] [Nonempty V] [Fintype E]
  [Fintype X] [Fintype Y] {q₁ q₂ s : ℕ} [NeZero q₁] [NeZero q₂] [NeZero s]

/-- The new edge-only coordinates, not the obsolete three-per-edge source. -/
noncomputable def witnessCoordinates (edge : E → Bool → V) (r : ℕ)
    (hq : q₂ = EdgeSource.sourceQ0 (Fin (4*s)) E * r)
    (μ : PositiveRationalLaw X) (W : Set (RawRow q₁ q₂ s X (Items s V)))
    (rowCode : RawRow q₁ q₂ s X (Items s V) → Fin s) : Finset (Fin q₂) :=
  (SourcePadding.witnessCoords (EdgeSource.sourceActive edge r)
    (itemKept μ W) (itemBranch μ W rowCode)).map
      (coordinateEquiv r hq).symm.toEmbedding

theorem mem_witnessCoordinates (edge : E → Bool → V) (r : ℕ)
    (hq : q₂ = EdgeSource.sourceQ0 (Fin (4*s)) E * r)
    (μ : PositiveRationalLaw X) (W : Set (RawRow q₁ q₂ s X (Items s V)))
    (rowCode : RawRow q₁ q₂ s X (Items s V) → Fin s) (α : Fin q₂) :
    α ∈ witnessCoordinates edge r hq μ W rowCode ↔
      SourcePadding.Witness (EdgeSource.sourceActive edge r)
        (itemKept μ W) (itemBranch μ W rowCode) (coordinateEquiv r hq α) := by
  classical
  simp [witnessCoordinates]

theorem witnessCoordinates_card_ge
    (edge : E → Bool → V) (loopless : ∀ e, edge e false ≠ edge e true)
    (hs : 4 ≤ s) (r Δ : ℕ) (hΔ : 0 < Δ)
    (hq : q₂ = EdgeSource.sourceQ0 (Fin (4*s)) E * r)
    (hdegree : ∀ v, SourceItems.degree edge v ≤ Δ)
    (γ : ℝ) (hγ : 0 < γ) (hE : 0 < Fintype.card E)
    (gap : ∀ colour : V → Fin 3, γ * Fintype.card E ≤
      ((Finset.univ.filter (fun e => colour (edge e false) = colour (edge e true))).card : ℝ))
    (μ : PositiveRationalLaw X) (W : Set (RawRow q₁ q₂ s X (Items s V)))
    (rowCode : RawRow q₁ q₂ s X (Items s V) → Fin s)
    (hW : 1 - deletionAllowance (V := V) (E := E) γ Δ s ≤
      (SourceLawBinding.matrixColumnLaw μ q₁ q₂ s hs).toFiniteLaw.prob (· ∈ W)) :
    γ / 24 * q₂ ≤ (witnessCoordinates edge r hq μ W rowCode).card := by
  classical
  have hdpos := vertexTolerance_pos (V := V) (E := E) γ Δ hγ hΔ hE
  have hzpos : 0 < witnessDensity γ := by unfold witnessDensity; positivity
  have hη := SourceDeletionParameters.eta_pos s (NeZero.pos s)
    (vertexTolerance (V := V) (E := E) γ Δ) (witnessDensity γ) hdpos hzpos
  have hv := vertexDeficient_card_lt μ hs W _ hη hW
  have ha := auxiliaryDeficient_card_lt μ hs W _ hη hW
  have hvbudget := SourceDeletionParameters.vertex_allowance s (Fintype.card V) hs
    (vertexTolerance (V := V) (E := E) γ Δ) (witnessDensity γ) hdpos.le
  have habudget := SourceDeletionParameters.auxiliary_allowance s hs
    (vertexTolerance (V := V) (E := E) γ Δ) (witnessDensity γ)
  have hd : ((SourceItems.deletedVertexItems (keptItems μ W)).card : ℝ) <
      (s : ℝ) / 2 * (γ * Fintype.card E / (2*Δ)) := by
    rw [deletedVertexItems_eq]
    have hh := hv.trans_le hvbudget
    unfold vertexTolerance at hh
    rw [SourceItems.vertex_deletion_budget γ s (Fintype.card E) Δ (Fintype.card V)
      hΔ Fintype.card_pos] at hh
    exact hh
  have haux : ((SourceItems.deletedAuxiliaryItems (keptItems μ W)).card : ℝ) <
      (s : ℝ) / 2 := by
    rw [deletedAuxiliaryItems_eq]
    exact ha.trans habudget
  have hc := EdgeSource.collisions_after_deletion_retained edge loopless hs
    r Δ hΔ hdegree (keptItems μ W)
    (fun i => itemBranch μ W rowCode i.val) γ hγ hE gap hd haux
  rw [extend_itemBranch] at hc
  simp only [mem_keptItems] at hc
  simpa only [witnessCoordinates, Finset.card_map, hq, Nat.cast_mul] using hc

def collisionAt (edge : E → Bool → V) (r : ℕ)
    (hq : q₂ = EdgeSource.sourceQ0 (Fin (4*s)) E * r)
    (μ : PositiveRationalLaw X) (W : Set (RawRow q₁ q₂ s X (Items s V)))
    (rowCode : RawRow q₁ q₂ s X (Items s V) → Fin s)
    (b : Fin s) (α : Fin q₂) : Prop :=
  ∃ i j h : Items s V, i ≠ j ∧ itemKept μ W i ∧ itemKept μ W j ∧ itemKept μ W h ∧
    EdgeSource.sourceActive edge r (coordinateEquiv r hq α) i ∧
    EdgeSource.sourceActive edge r (coordinateEquiv r hq α) j ∧
    ¬ EdgeSource.sourceActive edge r (coordinateEquiv r hq α) h ∧
    itemBranch μ W rowCode i = b ∧ itemBranch μ W rowCode j = b ∧
    itemBranch μ W rowCode h = b

theorem exists_collision_branch (edge : E → Bool → V) (r : ℕ)
    (hq : q₂ = EdgeSource.sourceQ0 (Fin (4*s)) E * r)
    (μ : PositiveRationalLaw X) (W : Set (RawRow q₁ q₂ s X (Items s V)))
    (rowCode : RawRow q₁ q₂ s X (Items s V) → Fin s)
    (α : Fin q₂) (hα : α ∈ witnessCoordinates edge r hq μ W rowCode) :
    ∃ b, collisionAt edge r hq μ W rowCode b α := by
  obtain ⟨i,j,h,hij,hi,hj,hh,hai,haj,hah,hbij,hbih⟩ :=
    (mem_witnessCoordinates edge r hq μ W rowCode α).mp hα
  exact ⟨itemBranch μ W rowCode i,i,j,h,hij,hi,hj,hh,hai,haj,hah,
    rfl,hbij.symm,hbih.symm⟩

/-- Actual distinct requested tail positions, and base-row masses in the
same fixed prefix part. This is the geometric input to local supplier(iii). -/
theorem collision_items
    (order : Items s V ≃ Fin (Fintype.card (Items s V)))
    (edge : E → Bool → V) (hs : 3 ≤ s) (r : ℕ)
    (hq : q₂ = EdgeSource.sourceQ0 (Fin (4*s)) E * r)
    (μ : PositiveRationalLaw X) (W : Set (RawRow q₁ q₂ s X (Items s V)))
    (rowCode : RawRow q₁ q₂ s X (Items s V) → Fin s)
    (b : Fin s) (α : Fin q₂) (hα : collisionAt edge r hq μ W rowCode b α)
    (ρ : ℝ) (hscale : 4*(s : ℝ)^2*ρ ≤ 1) :
    ∃ (i j h : Items s V) (p p' : Fin s), p ≠ p' ∧
      activity order edge hs r hq i α = some p ∧
      activity order edge hs r hq j α = some p' ∧
      activity order edge hs r hq h α = none ∧
      ∀ t : Fin 3, 2*(s : ℝ)*ρ ≤ μ.toFiniteLaw.prob
        (fun u => Sum.inr (SourceProjectionDiagonal.collisionItem i j h t,u) ∈ W ∧
          rowCode (Sum.inr (SourceProjectionDiagonal.collisionItem i j h t,u)) = b) := by
  obtain ⟨i,j,h,hij,hi,hj,hh,hai,haj,hah,hbi,hbj,hbh⟩ := hα
  obtain ⟨p,hp⟩ := (orderedActivity_some_iff order edge hs r i _).mpr hai
  obtain ⟨p',hp'⟩ := (orderedActivity_some_iff order edge hs r j _).mpr haj
  have hpp : p ≠ p' := by
    intro he
    subst p'
    exact hij (orderedActivity_injective order edge hs r _ i j p hp hp')
  have hn : activity order edge hs r hq h α = none := by
    cases he : activity order edge hs r hq h α with
    | none => rfl
    | some p =>
      exact False.elim
        (hah ((orderedActivity_some_iff order edge hs r h _).mp ⟨p,he⟩))
  have hcap := SourceDeletionParameters.assignment_floor s (NeZero.pos s) ρ hscale
  have hmi : 2*(s : ℝ)*ρ ≤ itemBranchMass μ W rowCode i b := by
    simpa only [hbi] using itemBranch_mass_ge_cap μ W rowCode i hi _ hcap
  have hmj : 2*(s : ℝ)*ρ ≤ itemBranchMass μ W rowCode j b := by
    simpa only [hbj] using itemBranch_mass_ge_cap μ W rowCode j hj _ hcap
  have hmh : 2*(s : ℝ)*ρ ≤ itemBranchMass μ W rowCode h b := by
    simpa only [hbh] using itemBranch_mass_ge_cap μ W rowCode h hh _ hcap
  refine ⟨i,j,h,p,p',hpp,hp,hp',hn,?_⟩
  intro t
  fin_cases t
  · exact hmi
  · exact hmj
  · exact hmh

end CurrentAdditive.V38EdgeCollisionGeometry

#print axioms CurrentAdditive.V38EdgeCollisionGeometry.witnessCoordinates
#print axioms CurrentAdditive.V38EdgeCollisionGeometry.mem_witnessCoordinates
#print axioms CurrentAdditive.V38EdgeCollisionGeometry.witnessCoordinates_card_ge
#print axioms CurrentAdditive.V38EdgeCollisionGeometry.collisionAt
#print axioms CurrentAdditive.V38EdgeCollisionGeometry.exists_collision_branch
#print axioms CurrentAdditive.V38EdgeCollisionGeometry.collision_items
