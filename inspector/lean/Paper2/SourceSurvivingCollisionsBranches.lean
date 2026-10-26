import Paper2.SourceSurvivingCollisionsItems
import Paper2.SourceDeficiencyBudget
import Paper2.SourceCollisionPartition

/-!
# Assigning surviving collisions to one usable source branch

Frozen v12 Section 4, `src:near-full`, lines 409--452.  Each retained
collision coordinate is assigned once to a branch actually containing its
three items.  The dominant template event is the original retained-row
event intersected with that same branch's label.  Counting the actual two
deficient-coordinate sets then selects a branch; the selected branch and
its witness excess are conclusions, never input certificates.
-/

namespace Paper2.SourceSurvivingCollisions

open scoped BigOperators
open SourceMatrix SourceLawBinding SourceDeficiency SourceCollisionPartition

variable {V E X Y : Type*} [Fintype V] [Nonempty V] [Fintype E]
  [Fintype X] [Fintype Y] {q₁ q₂ s : ℕ} [NeZero q₁] [NeZero q₂] [NeZero s]

/-- A literal collision whose three retained items were assigned to branch b. -/
def collisionAt (edge : E → Bool → V) (r : ℕ)
    (hq : q₂ = SourceItems.sourceQ0 (Fin (4 * s)) E * r)
    (μ : PositiveRationalLaw X)
    (W : Set (RawRow q₁ q₂ s X (SourceConstruction.Items s V)))
    (rowCode : RawRow q₁ q₂ s X (SourceConstruction.Items s V) → Fin s)
    (b : Fin s) (α : Fin q₂) : Prop :=
  ∃ i j h : SourceConstruction.Items s V, i ≠ j ∧
    itemKept μ W i ∧ itemKept μ W j ∧ itemKept μ W h ∧
    SourceItems.sourceActive edge r (SourceConstruction.coordinateEquiv r hq α) i ∧
    SourceItems.sourceActive edge r (SourceConstruction.coordinateEquiv r hq α) j ∧
    ¬ SourceItems.sourceActive edge r (SourceConstruction.coordinateEquiv r hq α) h ∧
    itemBranch μ W rowCode i = b ∧ itemBranch μ W rowCode j = b ∧
    itemBranch μ W rowCode h = b

theorem exists_collision_branch (edge : E → Bool → V) (r : ℕ)
    (hq : q₂ = SourceItems.sourceQ0 (Fin (4 * s)) E * r)
    (μ : PositiveRationalLaw X)
    (W : Set (RawRow q₁ q₂ s X (SourceConstruction.Items s V)))
    (rowCode : RawRow q₁ q₂ s X (SourceConstruction.Items s V) → Fin s)
    (α : Fin q₂) (hα : α ∈ witnessCoordinates edge r hq μ W rowCode) :
    ∃ b, collisionAt edge r hq μ W rowCode b α := by
  obtain ⟨i, j, h, hij, hi, hj, hh, hai, haj, hah, hbij, hbih⟩ :=
    (mem_witnessCoordinates edge r hq μ W rowCode α).mp hα
  exact ⟨itemBranch μ W rowCode i, i, j, h, hij, hi, hj, hh, hai, haj, hah,
    rfl, hbij.symm, hbih.symm⟩

/-- The source's U_b: a disjoint assignment of each original witness
coordinate to one of its actual collision branches. -/
noncomputable def assignedCoordinates (edge : E → Bool → V) (r : ℕ)
    (hq : q₂ = SourceItems.sourceQ0 (Fin (4 * s)) E * r)
    (μ : PositiveRationalLaw X)
    (W : Set (RawRow q₁ q₂ s X (SourceConstruction.Items s V)))
    (rowCode : RawRow q₁ q₂ s X (SourceConstruction.Items s V) → Fin s)
    (b : Fin s) : Finset (Fin q₂) :=
  part (witnessCoordinates edge r hq μ W rowCode)
    (chooseBranch (witnessCoordinates edge r hq μ W rowCode)
      (collisionAt edge r hq μ W rowCode)
      (exists_collision_branch edge r hq μ W rowCode)) b

theorem assignedCoordinates_disjoint (edge : E → Bool → V) (r : ℕ)
    (hq : q₂ = SourceItems.sourceQ0 (Fin (4 * s)) E * r)
    (μ : PositiveRationalLaw X)
    (W : Set (RawRow q₁ q₂ s X (SourceConstruction.Items s V)))
    (rowCode : RawRow q₁ q₂ s X (SourceConstruction.Items s V) → Fin s)
    {b c : Fin s} (hbc : b ≠ c) :
    Disjoint (assignedCoordinates edge r hq μ W rowCode b)
      (assignedCoordinates edge r hq μ W rowCode c) :=
  parts_disjoint _ _ hbc

theorem sum_assignedCoordinates_card (edge : E → Bool → V) (r : ℕ)
    (hq : q₂ = SourceItems.sourceQ0 (Fin (4 * s)) E * r)
    (μ : PositiveRationalLaw X)
    (W : Set (RawRow q₁ q₂ s X (SourceConstruction.Items s V)))
    (rowCode : RawRow q₁ q₂ s X (SourceConstruction.Items s V) → Fin s) :
    (∑ b, (assignedCoordinates edge r hq μ W rowCode b).card) =
      (witnessCoordinates edge r hq μ W rowCode).card :=
  sum_part_card _ _

theorem assignedCoordinates_collision (edge : E → Bool → V) (r : ℕ)
    (hq : q₂ = SourceItems.sourceQ0 (Fin (4 * s)) E * r)
    (μ : PositiveRationalLaw X)
    (W : Set (RawRow q₁ q₂ s X (SourceConstruction.Items s V)))
    (rowCode : RawRow q₁ q₂ s X (SourceConstruction.Items s V) → Fin s)
    (b : Fin s) (α : Fin q₂)
    (hα : α ∈ assignedCoordinates edge r hq μ W rowCode b) :
    collisionAt edge r hq μ W rowCode b α :=
  part_witness _ _ _ b α hα

/-- Three original item groups, in this same branch, request two distinct
active tail positions and the inactive tail position of the actual matrix. -/
theorem assignedCoordinates_items
    (order : SourceConstruction.Items s V ≃ Fin (Fintype.card (SourceConstruction.Items s V)))
    (edge : E → Bool → V) (hs : 3 ≤ s) (r : ℕ)
    (hq : q₂ = SourceItems.sourceQ0 (Fin (4 * s)) E * r)
    (μ : PositiveRationalLaw X)
    (W : Set (RawRow q₁ q₂ s X (SourceConstruction.Items s V)))
    (rowCode : RawRow q₁ q₂ s X (SourceConstruction.Items s V) → Fin s)
    (b : Fin s) (α : Fin q₂)
    (hα : α ∈ assignedCoordinates edge r hq μ W rowCode b)
    (ρ : ℝ) (hscale : 4 * (s : ℝ) ^ 2 * ρ ≤ 1) :
    ∃ i j h p p', i ≠ j ∧ p ≠ p' ∧
      SourceConstruction.activity order edge hs r hq i α = some p ∧
      SourceConstruction.activity order edge hs r hq j α = some p' ∧
      SourceConstruction.activity order edge hs r hq h α = none ∧
      2 * (s : ℝ) * ρ ≤ itemBranchMass μ W rowCode i b ∧
      2 * (s : ℝ) * ρ ≤ itemBranchMass μ W rowCode j b ∧
      2 * (s : ℝ) * ρ ≤ itemBranchMass μ W rowCode h b := by
  obtain ⟨i, j, h, hij, hi, hj, hh, hai, haj, hah, hbi, hbj, hbh⟩ :=
    assignedCoordinates_collision edge r hq μ W rowCode b α hα
  obtain ⟨p, hp⟩ := (SourceConstruction.orderedActivity_some_iff order edge hs r i _).mpr hai
  obtain ⟨p', hp'⟩ := (SourceConstruction.orderedActivity_some_iff order edge hs r j _).mpr haj
  have hpp : p ≠ p' := by
    intro heq
    subst p'
    exact hij (SourceProjectionProtected.graph_position_injective order edge hs r hq α i j p hp hp')
  have hn : SourceConstruction.activity order edge hs r hq h α = none := by
    cases hc : SourceConstruction.activity order edge hs r hq h α with
    | none => rfl
    | some p => exact False.elim (hah
        ((SourceConstruction.orderedActivity_some_iff order edge hs r h _).mp ⟨p, hc⟩))
  have hcap := SourceDeletionParameters.assignment_floor s (NeZero.pos s) ρ hscale
  refine ⟨i, j, h, p, p', hij, hpp, hp, hp', hn, ?_, ?_, ?_⟩
  · simpa only [hbi] using itemBranch_mass_ge_cap μ W rowCode i hi _ hcap
  · simpa only [hbj] using itemBranch_mass_ge_cap μ W rowCode j hj _ hcap
  · simpa only [hbh] using itemBranch_mass_ge_cap μ W rowCode h hh _ hcap

/-- Actual surviving templates from the designated dominant bin at a
branch. The common-prefix theorem supplies the dominant-bin bijection. -/
def branchTemplates
    (W : Set (RawRow q₁ q₂ s X (SourceConstruction.Items s V)))
    (rowCode : RawRow q₁ q₂ s X (SourceConstruction.Items s V) → Fin s)
    (dom : Fin s → Fin s) (b : Fin s) (z : Template q₁ q₂ X) : Prop :=
  Sum.inl (dom b, z) ∈ W ∧ rowCode (Sum.inl (dom b, z)) = b

theorem row_cap_le_eighth (hs : 4 ≤ s) (ρ : ℝ)
    (hscale : 4 * (s : ℝ) ^ 2 * ρ ≤ 1) : 2 * (s : ℝ) * ρ ≤ 1 / 8 := by
  apply (SourceDeletionParameters.assignment_floor s (NeZero.pos s) ρ hscale).trans
  have hsR : (4 : ℝ) ≤ s := by exact_mod_cast hs
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * s)).mpr
  nlinarith

/-- The actual deficient-coordinate population fits below the scheduled
quarter-witness budget. No deficient-cardinality bound is assumed. -/
theorem total_deficient_lt
    (μ : PositiveRationalLaw X) (ν : PositiveRationalLaw Y) (hs : 4 ≤ s)
    (γ : ℝ) (Δ : ℕ) (hγ : 0 < γ) (hΔ : 0 < Δ) (hE : 0 < Fintype.card E)
    (ρ : ℝ) (hscale : 4 * (s : ℝ) ^ 2 * ρ ≤ 1)
    (hcount : 8 * (s : ℝ) * q₁ ≤ witnessDensity γ * q₂ / 16)
    (U : Set (TaggedColumn q₁ q₂ s Y))
    (W : Set (RawRow q₁ q₂ s X (SourceConstruction.Items s V)))
    (rowCode : RawRow q₁ q₂ s X (SourceConstruction.Items s V) → Fin s)
    (dom : Fin s → Fin s)
    (hA : ∀ b, (998 / 1000 : ℝ) < (SourceLaws.templateLaw μ q₁ q₂).toFiniteLaw.prob
      (branchTemplates W rowCode dom b))
    (hU : 1 - deletionAllowance (V := V) (E := E) γ Δ s ≤
      (matrixRowLaw ν q₁ q₂ s).toFiniteLaw.prob (· ∈ U)) :
    (∑ b, ((branchDeficient μ ν (branchTemplates W rowCode dom b) U
      (2 * (s : ℝ) * ρ)).card : ℝ)) < witnessDensity γ * q₂ / 4 := by
  have hd := vertexTolerance_pos (V := V) (E := E) γ Δ hγ hΔ hE
  have hz : 0 < witnessDensity γ := by unfold witnessDensity; positivity
  have hη := SourceDeletionParameters.eta_pos s (NeZero.pos s)
    (vertexTolerance (V := V) (E := E) γ Δ) (witnessDensity γ) hd hz
  have hb := sum_branchDeficient_card_lt μ ν (branchTemplates W rowCode dom) U
    (2 * (s : ℝ) * ρ) _ (row_cap_le_eighth hs ρ hscale) hη hA hU
  exact hb.trans (SourceDeletionParameters.coordinate_allowance s q₁ q₂
    (NeZero.pos s) (NeZero.pos q₂) _ _ hz hcount)

/-- The chosen branch has strictly more witnesses than four times its
actual deficit count, and more than three times that count remain usable. -/
theorem select_usable_branch
    (edge : E → Bool → V) (loopless : ∀ e, edge e false ≠ edge e true)
    (hs : 4 ≤ s) (r Δ : ℕ) (hΔ : 0 < Δ)
    (hq : q₂ = SourceItems.sourceQ0 (Fin (4 * s)) E * r)
    (hdegree : ∀ v, SourceItems.degree edge v ≤ Δ)
    (γ : ℝ) (hγ : 0 < γ) (hE : 0 < Fintype.card E)
    (gap : ∀ colour : V → Fin 3, γ * Fintype.card E ≤
      ((Finset.univ.filter (fun e => colour (edge e false) = colour (edge e true))).card : ℝ))
    (μ : PositiveRationalLaw X) (ν : PositiveRationalLaw Y)
    (ρ : ℝ) (hscale : 4 * (s : ℝ) ^ 2 * ρ ≤ 1)
    (hcount : 8 * (s : ℝ) * q₁ ≤ witnessDensity γ * q₂ / 16)
    (U : Set (TaggedColumn q₁ q₂ s Y))
    (W : Set (RawRow q₁ q₂ s X (SourceConstruction.Items s V)))
    (rowCode : RawRow q₁ q₂ s X (SourceConstruction.Items s V) → Fin s)
    (dom : Fin s → Fin s)
    (hA : ∀ b, (998 / 1000 : ℝ) < (SourceLaws.templateLaw μ q₁ q₂).toFiniteLaw.prob
      (branchTemplates W rowCode dom b))
    (hU : 1 - deletionAllowance (V := V) (E := E) γ Δ s ≤
      (matrixRowLaw ν q₁ q₂ s).toFiniteLaw.prob (· ∈ U))
    (hW : 1 - deletionAllowance (V := V) (E := E) γ Δ s ≤
      (matrixColumnLaw μ q₁ q₂ s hs).toFiniteLaw.prob (· ∈ W)) :
    ∃ b : Fin s,
      let B := branchDeficient μ ν (branchTemplates W rowCode dom b) U (2 * (s : ℝ) * ρ)
      4 * B.card < (assignedCoordinates edge r hq μ W rowCode b).card ∧
      3 * B.card < (assignedCoordinates edge r hq μ W rowCode b \ B).card := by
  classical
  have hw := witnessCoordinates_card_ge edge loopless hs r Δ hΔ hq hdegree γ hγ hE gap
    μ W rowCode hW
  have hb := total_deficient_lt μ ν hs γ Δ hγ hΔ hE ρ hscale hcount U W rowCode dom hA hU
  exact select_surviving_branch (witnessCoordinates edge r hq μ W rowCode) _
    (fun b => branchDeficient μ ν (branchTemplates W rowCode dom b) U (2 * (s : ℝ) * ρ))
    (witnessDensity γ * q₂) hw hb

end Paper2.SourceSurvivingCollisions

#print axioms Paper2.SourceSurvivingCollisions.assignedCoordinates_items
#print axioms Paper2.SourceSurvivingCollisions.total_deficient_lt
#print axioms Paper2.SourceSurvivingCollisions.select_usable_branch
