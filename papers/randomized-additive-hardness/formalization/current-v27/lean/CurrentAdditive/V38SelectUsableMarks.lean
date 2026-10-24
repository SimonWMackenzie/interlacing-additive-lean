import CurrentAdditive.V38EdgeCollisionGeometry

/-! v39/v38 robustness.tex:196--265. Actual graph witnesses, fixed item
assignment and actual two-family deletion budgets select the marked
collision fibres; no collision existence or marked excess is assumed. -/

namespace CurrentAdditive.V38SelectUsableMarks

open Paper2 Paper2.SourceMatrix Paper2.SourceProjectionDiagonal
open Paper2.SourceSurvivingCollisions Paper2.SourceCollisionPartition
open CurrentAdditive.EdgeSourceMatrix CurrentAdditive.V38FullUsable
open scoped BigOperators

variable {V E X Y : Type*} [Fintype V] [Nonempty V] [Fintype E]
  [Fintype X] [Fintype Y] {q₁ q₂ s : ℕ} [NeZero q₁] [NeZero q₂] [NeZero s]

theorem select_marks_from_actual_retention
    (order : Items s V ≃ Fin (Fintype.card (Items s V)))
    (edge : E → Bool → V) (loopless : ∀ e, edge e false ≠ edge e true)
    (hs : 4 ≤ s) (r Δ : ℕ) (hΔ : 0 < Δ)
    (hq : q₂ = EdgeSource.sourceQ0 (Fin (4*s)) E * r)
    (hdegree : ∀ v, SourceItems.degree edge v ≤ Δ)
    (γ : ℝ) (hγ : 0 < γ) (hE : 0 < Fintype.card E)
    (gap : ∀ colour : V → Fin 3, γ * Fintype.card E ≤
      ((Finset.univ.filter (fun e => colour (edge e false) = colour (edge e true))).card : ℝ))
    (μ : PositiveRationalLaw X) (ν : PositiveRationalLaw Y)
    (W : Set (RawRow q₁ q₂ s X (Items s V)))
    (U : Set (V38Matrix.TaggedColumn q₁ q₂ s Y))
    (rowCode : RawRow q₁ q₂ s X (Items s V) → Fin s)
    (K : Fin s → Set (Template q₁ q₂ X)) (ρ η : ℝ)
    (hη : 0 < η) (hηAllowance : η ≤ deletionAllowance (V := V) (E := E) γ Δ s)
    (hscale : 4*(s : ℝ)^2*ρ ≤ 1)
    (hmargin : 8*(s : ℝ)*q₁ + 1024*s*η*q₂ < (γ/24)*q₂/4)
    (hKmass : ∀ j, (998/1000 : ℝ) <
      (SourceLaws.templateLaw μ q₁ q₂).toFiniteLaw.prob (· ∈ K j))
    (hW : 1-η ≤ (V38Matrix.columnLaw (V := V) μ hs).toFiniteLaw.prob (· ∈ W))
    (hU : 1-η ≤ (V38Matrix.taggedLaw ν).toFiniteLaw.prob (· ∈ U)) :
    ∃ (j : Fin s) (Marks : Finset (Fin q₂)),
      Marks ⊆ Finset.univ \ bad μ ν (K j) U (2*(s : ℝ)*ρ) ∧
      (bad μ ν (K j) U (2*(s : ℝ)*ρ)).card < Marks.card ∧
      ∀ α ∈ Marks, ∃ (i₁ i₂ i₀ : Items s V) (p p' : Fin s), p ≠ p' ∧
        activity order edge (by omega : 3 ≤ s) r hq i₁ α = some p ∧
        activity order edge (by omega : 3 ≤ s) r hq i₂ α = some p' ∧
        activity order edge (by omega : 3 ≤ s) r hq i₀ α = none ∧
        ∀ t : Fin 3, 2*(s : ℝ)*ρ ≤ μ.toFiniteLaw.prob
          (fun u => Sum.inr (collisionItem i₁ i₂ i₀ t,u) ∈ W ∧
            rowCode (Sum.inr (collisionItem i₁ i₂ i₀ t,u)) = j) := by
  classical
  have hW' : 1 - deletionAllowance (V := V) (E := E) γ Δ s ≤
      (SourceLawBinding.matrixColumnLaw μ q₁ q₂ s hs).toFiniteLaw.prob (· ∈ W) := by
    have hstart : 1 - deletionAllowance (V := V) (E := E) γ Δ s ≤ 1-η := by linarith
    exact hstart.trans hW
  have hw := V38EdgeCollisionGeometry.witnessCoordinates_card_ge
    edge loopless hs r Δ hΔ hq hdegree γ hγ hE gap μ W rowCode hW'
  have hcap : 2*(s : ℝ)*ρ ≤ 1/8 := by
    have hfloor := SourceDeletionParameters.assignment_floor s (NeZero.pos s) ρ hscale
    have hsR : (4 : ℝ) ≤ s := by exact_mod_cast hs
    have hden : (0 : ℝ) < 2*s := by positivity
    have hbound : 1/(2*(s : ℝ)) ≤ 1/8 := by
      apply (div_le_iff₀ hden).mpr
      nlinarith
    exact hfloor.trans hbound
  have hb := sum_bad_card_lt μ ν K U (2*(s : ℝ)*ρ) η hcap hη hKmass hU
  have hb' : (∑ j, ((bad μ ν (K j) U (2*(s : ℝ)*ρ)).card : ℝ)) <
      (γ/24)*q₂/4 := hb.trans hmargin
  let Coords := V38EdgeCollisionGeometry.witnessCoordinates edge r hq μ W rowCode
  let WitnessAt := V38EdgeCollisionGeometry.collisionAt edge r hq μ W rowCode
  have hWitness : ∀ α ∈ Coords, ∃ j, WitnessAt j α :=
    V38EdgeCollisionGeometry.exists_collision_branch edge r hq μ W rowCode
  obtain ⟨j,_hfour,hthree,hinfo⟩ := select_witness_branch Coords WitnessAt hWitness
    (fun j => bad μ ν (K j) U (2*(s : ℝ)*ρ)) ((γ/24)*q₂) hw hb'
  let Marks := part Coords (chooseBranch Coords WitnessAt hWitness) j \
    bad μ ν (K j) U (2*(s : ℝ)*ρ)
  refine ⟨j, Marks, ?_, ?_, ?_⟩
  · intro α hα
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, (Finset.mem_sdiff.mp hα).2⟩
  · change (bad μ ν (K j) U (2*(s : ℝ)*ρ)).card < Marks.card
    change 3*(bad μ ν (K j) U (2*(s : ℝ)*ρ)).card < Marks.card at hthree
    omega
  · intro α hα
    exact V38EdgeCollisionGeometry.collision_items order edge (by omega) r hq μ W
      rowCode j α (hinfo α hα).2.1 ρ hscale

end CurrentAdditive.V38SelectUsableMarks

#print axioms CurrentAdditive.V38SelectUsableMarks.select_marks_from_actual_retention
