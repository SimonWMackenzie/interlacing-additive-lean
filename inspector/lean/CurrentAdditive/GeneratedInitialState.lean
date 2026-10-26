import CurrentAdditive.GeneratedUsableWitness

/-!
The Bob-only initial state on a chosen generated-source branch is made from
the actual retained diagonal columns. Every support and attachment is a
literal subset of those columns; its gamma mass follows from the checked
diagonal deficit estimate.
-/

namespace CurrentAdditive.DeterministicIndexedMatrix.Sources

open Paper2 Paper2.SourceSupportFrontier

variable {X Y I : Type*} [Fintype X] [Fintype Y] [Fintype I]
  [DecidableEq X] [DecidableEq Y]
  {D q₁ q₂ s : ℕ} [NeZero s] [NeZero q₁] [NeZero q₂]
  {μX : PositiveRationalLaw X} {μY : PositiveRationalLaw Y}
  (src : Sources (D := D) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY)

noncomputable def diagonalSupport (U : Set (Column src))
    (α : Fin q₂) : Finset src.gamma.Label := by
  classical
  exact Finset.univ.filter (fun γ => Column.diagonal (α, γ) ∈ U)

theorem diagonalSupport_mass (U : Set (Column src)) (α : Fin q₂) :
    Paper2.SourceSupportStep.mass src.gamma.law.toFiniteLaw
      (diagonalSupport src U α) =
    src.gamma.law.toFiniteLaw.prob
      (fun γ => Column.diagonal (α,γ) ∈ U) := by
  classical
  simp [Paper2.SourceSupportStep.mass, diagonalSupport]

noncomputable def initialIndexedState
    (U : Set (Column src))
    (V : Set (Row (I := I) src))
    (P : Workspace.Types.Protocol.Protocol V (Column src) Bool)
    (bad part : Finset (Fin q₂)) :
    State V (Column src) (Fin q₂) src.gamma.Label where
  protocol := P
  columns := U
  coordinates := Finset.univ \ bad
  attachments := part \ bad
  support := diagonalSupport src U

theorem initialIndexedState_invariants
    (U : Set (Column src))
    (V : Set (Row (I := I) src))
    (P : Workspace.Types.Protocol.Protocol V (Column src) Bool)
    (K : Set src.inner.Label) (xcap x : ℝ)
    (bad part : Finset (Fin q₂))
    (hbad : bad = branchBad src K U xcap)
    (hsmall : Paper2.SourceSupportSchedule.floor q₂ x 0 ≤ 1/8) :
    let initial := initialIndexedState src U V P bad part
    initial.attachments ⊆ initial.coordinates ∧
    initial.coordinates.card + bad.card = q₂ ∧
    (∀ α ∈ initial.coordinates,
      Paper2.SourceSupportSchedule.floor q₂ x 0 ≤
        Paper2.SourceSupportStep.mass src.gamma.law.toFiniteLaw
          (initial.support α)) ∧
    (∀ α ∈ initial.attachments,
      (3/4 : ℝ) ≤ Paper2.SourceSupportStep.mass
        src.gamma.law.toFiniteLaw (initial.support α)) ∧
    (∀ α ∈ initial.coordinates, ∀ γ ∈ initial.support α,
      Column.diagonal (α, γ) ∈ initial.columns) := by
  classical
  let initial := initialIndexedState src U V P bad part
  change initial.attachments ⊆ initial.coordinates ∧
    initial.coordinates.card + bad.card = q₂ ∧
    (∀ α ∈ initial.coordinates, Paper2.SourceSupportSchedule.floor q₂ x 0 ≤
      Paper2.SourceSupportStep.mass src.gamma.law.toFiniteLaw (initial.support α)) ∧
    (∀ α ∈ initial.attachments, (3/4 : ℝ) ≤
      Paper2.SourceSupportStep.mass src.gamma.law.toFiniteLaw
        (initial.support α)) ∧
    (∀ α ∈ initial.coordinates, ∀ γ ∈ initial.support α,
      Column.diagonal (α, γ) ∈ initial.columns)
  have hsupport : ∀ α, α ∉ bad →
      (3/4 : ℝ) ≤ Paper2.SourceSupportStep.mass
        src.gamma.law.toFiniteLaw (diagonalSupport src U α) := by
    intro α hα
    have hh := (usable_coordinate_masses src K U xcap α
      (by simpa only [hbad] using hα)).2
    rw [diagonalSupport_mass]
    exact hh
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro α hα
    exact Finset.mem_sdiff.mpr
      ⟨Finset.mem_univ _, (Finset.mem_sdiff.mp hα).2⟩
  · have hb : bad ⊆ (Finset.univ : Finset (Fin q₂)) :=
      Finset.subset_univ _
    have hc := Finset.card_sdiff_add_card_eq_card hb
    simpa [initial, initialIndexedState] using hc
  · intro α hα
    have hnot := (Finset.mem_sdiff.mp hα).2
    change Paper2.SourceSupportSchedule.floor q₂ x 0 ≤
      Paper2.SourceSupportStep.mass src.gamma.law.toFiniteLaw
        (diagonalSupport src U α)
    linarith [hsupport α hnot]
  · intro α hα
    have hnot := (Finset.mem_sdiff.mp hα).2
    exact hsupport α hnot
  · intro α _ γ hγ
    exact (Finset.mem_filter.mp hγ).2

end CurrentAdditive.DeterministicIndexedMatrix.Sources

#print axioms CurrentAdditive.DeterministicIndexedMatrix.Sources.initialIndexedState_invariants
