import CurrentAdditive.GeneratedRawItemShadow

/-!
The old graph collision theorem applies to the actual indexed source-item
rows through a raw shadow that keeps exactly those item rows. Combining its
graph-derived witness population with the new generated-template and
diagonal deficit counts selects a usable collision branch. The retained
shadow probability is a concrete law-transport premise, not a cost bound.
-/

namespace CurrentAdditive.DeterministicIndexedMatrix.Sources

open Paper2 Paper2.SourceMatrix Paper2.SourceSurvivingCollisions

variable {G E X Y : Type*} [Fintype G] [Nonempty G] [Fintype E]
  [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]
  {D q₁ q₂ s : ℕ} [NeZero s] [NeZero q₁] [NeZero q₂]
  {μX : PositiveRationalLaw X} {μY : PositiveRationalLaw Y}
  (src : Sources (D := D) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY)

theorem select_generated_collision_branch
    (hD : 2 ≤ D) (edge : E → Bool → G)
    (loopless : ∀ e, edge e false ≠ edge e true)
    (hs : 4 ≤ s) (r Δ : ℕ) (hΔ : 0 < Δ)
    (hq : q₂ = SourceItems.sourceQ0 (Fin (4*s)) E * r)
    (hdegree : ∀ v, SourceItems.degree edge v ≤ Δ)
    (γ : ℝ) (hγ : 0 < γ) (hE : 0 < Fintype.card E)
    (gap : ∀ colour : G → Fin 3,
      γ * Fintype.card E ≤
      ((Finset.univ.filter (fun e =>
        colour (edge e false) = colour (edge e true))).card : ℝ))
    (V : Set (Row (I := SourceConstruction.Items s G) src))
    (rowCode : Row (I := SourceConstruction.Items s G) src → Fin s)
    (hshadow : 1 - deletionAllowance (V := G) (E := E) γ Δ s ≤
      (Paper2.SourceLawBinding.matrixColumnLaw μX q₁ q₂ s hs).toFiniteLaw.prob
        (· ∈ rawItemShadow src V))
    (K : Fin s → Set src.inner.Label)
    (hKmass : ∀ j, (1/7 : ℝ) <
      src.inner.law.toFiniteLaw.prob (· ∈ K j))
    (U : Set (Column src)) (η xcap : ℝ)
    (hη : 0 < η) (hxcap : xcap ≤ 1/8)
    (hU : 1 - η ≤ (columnLaw src).toFiniteLaw.prob (· ∈ U))
    (hSchedule : 8 * s * q₁ + 1024 * s * η * q₂ <
      witnessDensity γ * q₂ / 4) :
    ∃ j : Fin s,
      let part := assignedCoordinates edge r hq μX
        (rawItemShadow src V) (rawItemCode src rowCode) j
      let bad := branchBad src (K j) U xcap
      4 * bad.card < part.card ∧
        3 * bad.card < (part \ bad).card ∧
        ∀ α ∈ part \ bad,
          collisionAt edge r hq μX
            (rawItemShadow src V) (rawItemCode src rowCode) j α ∧
          α ∉ bad := by
  classical
  let W := witnessCoordinates edge r hq μX
    (rawItemShadow src V) (rawItemCode src rowCode)
  let WitnessAt := collisionAt edge r hq μX
    (rawItemShadow src V) (rawItemCode src rowCode)
  have hW : witnessDensity γ * q₂ ≤ (W.card : ℝ) :=
    witnessCoordinates_card_ge edge loopless hs r Δ hΔ hq hdegree
      γ hγ hE gap μX (rawItemShadow src V) (rawItemCode src rowCode) hshadow
  have hwit : ∀ α ∈ W, ∃ j, WitnessAt j α := by
    intro α hα
    exact exists_collision_branch edge r hq μX
      (rawItemShadow src V) (rawItemCode src rowCode) α hα
  obtain ⟨j, hj⟩ := select_usable_witness_branch src hD
    K hKmass U η xcap (witnessDensity γ) hη hxcap hU W WitnessAt
    hwit hW hSchedule
  refine ⟨j, ?_⟩
  simpa only [W, WitnessAt, assignedCoordinates] using
    ⟨hj.1, hj.2.1, fun α hα => ⟨(hj.2.2 α hα).2.1,
      (hj.2.2 α hα).2.2⟩⟩

end CurrentAdditive.DeterministicIndexedMatrix.Sources

#print axioms CurrentAdditive.DeterministicIndexedMatrix.Sources.select_generated_collision_branch
