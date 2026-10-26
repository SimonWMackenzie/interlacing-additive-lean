import CurrentAdditive.V39IndexedUsable
import CurrentAdditive.V38EdgeCollisionGeometry
import CurrentAdditive.GeneratedShadowMass

/-! Current indexed source: graph witnesses and the original indexed-law
deletion budgets select usable marked coordinates on the same matrix. -/

namespace CurrentAdditive.V39IndexedSelectMarks

open Paper2 Paper2.SourceMatrix Paper2.SourceProjectionDiagonal
open Paper2.SourceSurvivingCollisions Paper2.SourceCollisionPartition
open CurrentAdditive.EdgeSourceMatrix CurrentAdditive.DeterministicIndexedMatrix
open CurrentAdditive.DeterministicIndexedMatrix.Sources
open CurrentAdditive.V38IndexedUsable
open scoped BigOperators

variable {V E X Y : Type*} [Fintype V] [Nonempty V] [Fintype E]
  [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]
  {D q₁ q₂ s : ℕ} [NeZero q₁] [NeZero q₂] [NeZero s]
  {μX : PositiveRationalLaw X} {μY : PositiveRationalLaw Y}
  (src : Sources (D := D) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY)

theorem select_marks_from_actual_retention
    (hD : 2 ≤ D)
    (order : Items s V ≃ Fin (Fintype.card (Items s V)))
    (edge : E → Bool → V) (loopless : ∀ e, edge e false ≠ edge e true)
    (hs : 4 ≤ s) (r Δ : ℕ) (hΔ : 0 < Δ)
    (hq : q₂ = EdgeSource.sourceQ0 (Fin (4*s)) E * r)
    (hdegree : ∀ v, SourceItems.degree edge v ≤ Δ)
    (γ : ℝ) (hγ : 0 < γ) (hE : 0 < Fintype.card E)
    (gap : ∀ colour : V → Fin 3, γ * Fintype.card E ≤
      ((Finset.univ.filter (fun e => colour (edge e false) = colour (edge e true))).card : ℝ))
    (W : Set (Row (I := Items s V) src))
    (U : Set (V38IndexedTwoTag.Column src))
    (rowCode : Row (I := Items s V) src → Fin s)
    (K : Fin s → Set src.inner.Label) (ρ η : ℝ)
    (hη : 0 < η) (hηAllowance : η ≤ deletionAllowance (V := V) (E := E) γ Δ s)
    (hscale : 4*(s : ℝ)^2*ρ ≤ 1)
    (hmargin : 8*(s : ℝ)*q₁ + 1024*s*η*q₂ < (γ/24)*q₂/4)
    (hKmass : ∀ j, (998/1000 : ℝ) < src.inner.law.toFiniteLaw.prob (· ∈ K j))
    [Nonempty (Fin (4*s))] [Nonempty (Fin (s-3))]
    (hW : 1-η ≤ (rowLaw src
      (itemLaw (G := Fin (4*s)) (V := V) (A := Fin (s-3)))).toFiniteLaw.prob (· ∈ W))
    (hU : 1-η ≤ (V38IndexedTwoTag.law src).toFiniteLaw.prob (· ∈ U)) :
    ∃ (j : Fin s) (Marks : Finset (Fin q₂)),
      Marks ⊆ Finset.univ \ bad src (K j) U (2*(s : ℝ)*ρ) ∧
      (bad src (K j) U (2*(s : ℝ)*ρ)).card < Marks.card ∧
      ∀ α ∈ Marks, ∃ (i₁ i₂ i₀ : Items s V) (p p' : Fin s), p ≠ p' ∧
        activity order edge (by omega : 3 ≤ s) r hq i₁ α = some p ∧
        activity order edge (by omega : 3 ≤ s) r hq i₂ α = some p' ∧
        activity order edge (by omega : 3 ≤ s) r hq i₀ α = none ∧
        ∀ t : Fin 3, 2*(s : ℝ)*ρ ≤ μX.toFiniteLaw.prob
          (fun u => Sum.inr (collisionItem i₁ i₂ i₀ t,u) ∈ W ∧
            rowCode (Sum.inr (collisionItem i₁ i₂ i₀ t,u)) = j) := by
  classical
  let Wraw := rawItemShadow src W
  let code := rawItemCode src rowCode
  have hW' := raw_item_shadow_retained_of_total (E := E) src hs γ Δ W η hW hηAllowance
  have hw := V38EdgeCollisionGeometry.witnessCoordinates_card_ge
    edge loopless hs r Δ hΔ hq hdegree γ hγ hE gap μX Wraw code hW'
  have hcap : 2*(s : ℝ)*ρ ≤ 1/8 := by
    have hfloor := SourceDeletionParameters.assignment_floor s (NeZero.pos s) ρ hscale
    have hsR : (4 : ℝ) ≤ s := by exact_mod_cast hs
    have hden : (0 : ℝ) < 2*s := by positivity
    have hbound : 1/(2*(s : ℝ)) ≤ 1/8 := by
      apply (div_le_iff₀ hden).mpr
      nlinarith
    exact hfloor.trans hbound
  have hb := sum_bad_card_lt src hD K U (2*(s : ℝ)*ρ) η hcap hη hKmass hU
  have hb' : (∑ j, ((bad src (K j) U (2*(s : ℝ)*ρ)).card : ℝ)) <
      (γ/24)*q₂/4 := hb.trans hmargin
  let Coords := V38EdgeCollisionGeometry.witnessCoordinates edge r hq μX Wraw code
  let WitnessAt := V38EdgeCollisionGeometry.collisionAt edge r hq μX Wraw code
  have hWitness : ∀ α ∈ Coords, ∃ j, WitnessAt j α :=
    V38EdgeCollisionGeometry.exists_collision_branch edge r hq μX Wraw code
  obtain ⟨j,_hfour,hthree,hinfo⟩ := select_witness_branch Coords WitnessAt hWitness
    (fun j => bad src (K j) U (2*(s : ℝ)*ρ)) ((γ/24)*q₂) hw hb'
  let Marks := part Coords (chooseBranch Coords WitnessAt hWitness) j \
    bad src (K j) U (2*(s : ℝ)*ρ)
  refine ⟨j, Marks, ?_, ?_, ?_⟩
  · intro α hα
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, (Finset.mem_sdiff.mp hα).2⟩
  · change (bad src (K j) U (2*(s : ℝ)*ρ)).card < Marks.card
    change 3*(bad src (K j) U (2*(s : ℝ)*ρ)).card < Marks.card at hthree
    omega
  · intro α hα
    simpa only [Wraw,code,rawItemShadow_source,rawItemCode_source] using
      V38EdgeCollisionGeometry.collision_items order edge (by omega) r hq μX Wraw
        code j α (hinfo α hα).2.1 ρ hscale

end CurrentAdditive.V39IndexedSelectMarks

#print axioms CurrentAdditive.V39IndexedSelectMarks.select_marks_from_actual_retention
