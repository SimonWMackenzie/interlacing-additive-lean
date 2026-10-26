import Paper2.SourceDeficiencyAssignment
import Paper2.SourceDeletionParameters

/-!
# Collision coordinates surviving actual source-item deletions

Frozen v12 Section 4, `src:near-full`, the surviving-collisions paragraph.
The kept items and their single branch assignment are derived from the
original retained rows.  The graph input is the explicit violated-edge gap;
no collision property is supplied as a hypothesis.
-/

namespace Paper2.SourceSurvivingCollisions

open scoped BigOperators
open SourceMatrix SourceLawBinding SourceDeficiency

variable {V E X : Type*} [Fintype V] [Nonempty V] [Fintype E] [Fintype X]
  {q₁ q₂ s : ℕ} [NeZero q₁] [NeZero s]

noncomputable def keptItems (μ : PositiveRationalLaw X)
    (W : Set (RawRow q₁ q₂ s X (SourceConstruction.Items s V))) :
    Finset (SourceConstruction.Items s V) := by
  classical
  exact Finset.univ.filter (itemKept μ W)

@[simp] theorem mem_keptItems (μ : PositiveRationalLaw X)
    (W : Set (RawRow q₁ q₂ s X (SourceConstruction.Items s V)))
    (i : SourceConstruction.Items s V) : i ∈ keptItems μ W ↔ itemKept μ W i := by
  classical
  simp [keptItems]

theorem deletedVertexItems_eq (μ : PositiveRationalLaw X)
    (W : Set (RawRow q₁ q₂ s X (SourceConstruction.Items s V))) :
    SourceItems.deletedVertexItems (keptItems μ W) = vertexDeficient μ W := by
  classical
  ext i
  simp [SourceItems.deletedVertexItems, SourceGroupCounting.grouped, itemKept]

theorem deletedAuxiliaryItems_eq (μ : PositiveRationalLaw X)
    (W : Set (RawRow q₁ q₂ s X (SourceConstruction.Items s V))) :
    SourceItems.deletedAuxiliaryItems (keptItems μ W) = auxiliaryDeficient μ W := by
  classical
  ext i
  simp [SourceItems.deletedAuxiliaryItems, SourceGroupCounting.grouped, itemKept]

/-- The graph parameters used in the literal deletion schedule. -/
noncomputable def vertexTolerance (γ : ℝ) (Δ : ℕ) : ℝ :=
  γ * Fintype.card E / (2 * Δ * Fintype.card V)

noncomputable def witnessDensity (γ : ℝ) : ℝ := γ / 24

theorem vertexTolerance_pos (γ : ℝ) (Δ : ℕ) (hγ : 0 < γ)
    (hΔ : 0 < Δ) (hE : 0 < Fintype.card E) :
    0 < vertexTolerance (V := V) (E := E) γ Δ := by
  unfold vertexTolerance
  exact div_pos (mul_pos hγ (by exact_mod_cast hE))
    (by have hv := Fintype.card_pos (α := V); positivity)

/-- This is precisely the source's minimum-defined deletion allowance. -/
noncomputable def deletionAllowance (γ : ℝ) (Δ : ℕ) (s : ℕ) : ℝ :=
  SourceDeletionParameters.eta s (vertexTolerance (V := V) (E := E) γ Δ)
    (witnessDensity γ)

/-- Extension from kept items agrees with the same branch assignment on
all labels, including the common default used for deficient items. -/
theorem extend_itemBranch (μ : PositiveRationalLaw X)
    (W : Set (RawRow q₁ q₂ s X (SourceConstruction.Items s V)))
    (rowCode : RawRow q₁ q₂ s X (SourceConstruction.Items s V) → Fin s) :
    SourceItems.extendBins (NeZero.pos s) (keptItems μ W)
      (fun i => itemBranch μ W rowCode i.val) = itemBranch μ W rowCode := by
  classical
  funext i
  by_cases hi : itemKept μ W i
  · simp only [SourceItems.extendBins, mem_keptItems, dif_pos hi]
  · simp only [SourceItems.extendBins, mem_keptItems, dif_neg hi, itemBranch]

/-- Actual Fin-q₂ coordinate labels for the retained collision event. -/
noncomputable def witnessCoordinates (edge : E → Bool → V) (r : ℕ)
    (hq : q₂ = SourceItems.sourceQ0 (Fin (4 * s)) E * r)
    (μ : PositiveRationalLaw X)
    (W : Set (RawRow q₁ q₂ s X (SourceConstruction.Items s V)))
    (rowCode : RawRow q₁ q₂ s X (SourceConstruction.Items s V) → Fin s) :
    Finset (Fin q₂) :=
  (SourcePadding.witnessCoords (SourceItems.sourceActive edge r)
    (itemKept μ W) (itemBranch μ W rowCode)).map
      (SourceConstruction.coordinateEquiv r hq).symm.toEmbedding

@[simp] theorem mem_witnessCoordinates (edge : E → Bool → V) (r : ℕ)
    (hq : q₂ = SourceItems.sourceQ0 (Fin (4 * s)) E * r)
    (μ : PositiveRationalLaw X)
    (W : Set (RawRow q₁ q₂ s X (SourceConstruction.Items s V)))
    (rowCode : RawRow q₁ q₂ s X (SourceConstruction.Items s V) → Fin s)
    (α : Fin q₂) :
    α ∈ witnessCoordinates edge r hq μ W rowCode ↔
      SourcePadding.Witness (SourceItems.sourceActive edge r)
        (itemKept μ W) (itemBranch μ W rowCode)
        (SourceConstruction.coordinateEquiv r hq α) := by
  classical
  simp [witnessCoordinates]

/-- The graph gap and actual protected retained mass yield at least
ζq₂ collision coordinates, with ζ=γ/24 from the source construction. -/
theorem witnessCoordinates_card_ge
    (edge : E → Bool → V) (loopless : ∀ e, edge e false ≠ edge e true)
    (hs : 4 ≤ s) (r Δ : ℕ) (hΔ : 0 < Δ)
    (hq : q₂ = SourceItems.sourceQ0 (Fin (4 * s)) E * r)
    (hdegree : ∀ v, SourceItems.degree edge v ≤ Δ)
    (γ : ℝ) (hγ : 0 < γ) (hE : 0 < Fintype.card E)
    (gap : ∀ colour : V → Fin 3, γ * Fintype.card E ≤
      ((Finset.univ.filter (fun e => colour (edge e false) = colour (edge e true))).card : ℝ))
    (μ : PositiveRationalLaw X)
    (W : Set (RawRow q₁ q₂ s X (SourceConstruction.Items s V)))
    (rowCode : RawRow q₁ q₂ s X (SourceConstruction.Items s V) → Fin s)
    (hW : 1 - deletionAllowance (V := V) (E := E) γ Δ s ≤
      (matrixColumnLaw μ q₁ q₂ s hs).toFiniteLaw.prob (· ∈ W)) :
    witnessDensity γ * q₂ ≤ (witnessCoordinates edge r hq μ W rowCode).card := by
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
      (s : ℝ) / 2 * (γ * Fintype.card E / (2 * Δ)) := by
    rw [deletedVertexItems_eq]
    have hh := hv.trans_le hvbudget
    unfold vertexTolerance at hh
    rw [SourceItems.vertex_deletion_budget γ s (Fintype.card E) Δ (Fintype.card V)
      hΔ Fintype.card_pos] at hh
    exact hh
  have hdaux : ((SourceItems.deletedAuxiliaryItems (keptItems μ W)).card : ℝ) <
      (s : ℝ) / 2 := by
    rw [deletedAuxiliaryItems_eq]
    exact ha.trans habudget
  have hc := SourceItems.collisions_after_deletion_retained edge loopless
    (by omega : 3 ≤ s) r Δ hΔ hdegree (keptItems μ W)
    (fun i => itemBranch μ W rowCode i.val) γ hγ hE gap hd hdaux
  rw [extend_itemBranch] at hc
  simp only [mem_keptItems] at hc
  simpa only [witnessDensity, witnessCoordinates, Finset.card_map, hq, Nat.cast_mul] using hc

end Paper2.SourceSurvivingCollisions

#print axioms Paper2.SourceSurvivingCollisions.witnessCoordinates_card_ge
