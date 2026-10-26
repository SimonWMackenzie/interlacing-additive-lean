import CurrentAdditive.IndexedSuccessorStage
import CurrentAdditive.IndexedGraphUpper
import Paper2.RestrictionProfiles

/-!
Semantic upper bounds and profile identity for one actual indexed successor
viewed as a dependent iteration stage.  The underlying matrix is the literal
`Sources.successor` on the same complete Code_D labels and laws.
-/

namespace CurrentAdditive.IndexedStagePresentation

open Paper2 Paper2.SourceMatrix Workspace.Types.CommComplexity
open CurrentAdditive.DeterministicIndexedMatrix

universe u

variable {I X Y : Type u} [Fintype I] [Fintype X] [Fintype Y]
  [DecidableEq I] [DecidableEq X] [DecidableEq Y]
  {D q₁ q₂ s : ℕ} [NeZero s] [NeZero q₁] [NeZero q₂]
  {μX : PositiveRationalLaw X} {μY : PositiveRationalLaw Y}
  (src : Sources (D := D) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY)

theorem successorStage_cost_profile
    {μI : PositiveRationalLaw I} {w Q Npub : ℕ} [NeZero w] [NeZero Q]
    (streams : Sources.InternalStreams src μI w)
    (final : CodeSource D Q (Fin w × Sources.Column src)
      ((PositiveRationalLaw.uniform (Fin w)).prod (Sources.columnLaw src)))
    (R : X → Y → Bool) (activity : I → Fin q₂ → Option (Fin s))
    (ξ₀ : Tail s Y) (S clock : ℕ)
    (hS : Fintype.card final.Label *
      Fintype.card (Fin Q ×
        (streams.metadataStream.Label ×
          (streams.baseStream.Label × streams.selectorStream.Label))) ≤ S)
    (hNQ : Npub ≤ Q) (ρ : ℝ) (d : ℤ) :
    let stage := successorStage src streams final R activity ξ₀ S clock hS hNQ
    Workspace.Types.CommComplexity.D stage.matrix =
      Workspace.Types.CommComplexity.D
        (Sources.successor src streams final R activity ξ₀) ∧
    (RestrictionProfile stage.matrix stage.rowLaw.toFiniteLaw
      stage.colLaw.toFiniteLaw ρ d ↔
      RestrictionProfile (Sources.successor src streams final R activity ξ₀)
        final.law.toFiniteLaw
        (((PositiveRationalLaw.uniform (Fin Q)).prod
          (Sources.InternalStreams.law src streams)).toFiniteLaw) ρ d) := by
  dsimp only
  constructor
  · rfl
  · rfl

theorem successorStage_universal_upper
    {μI : PositiveRationalLaw I} {w Q Npub : ℕ} [NeZero w] [NeZero Q]
    (streams : Sources.InternalStreams src μI w)
    (final : CodeSource D Q (Fin w × Sources.Column src)
      ((PositiveRationalLaw.uniform (Fin w)).prod (Sources.columnLaw src)))
    (R : X → Y → Bool) (activity : I → Fin q₂ → Option (Fin s))
    (ξ₀ : Tail s Y) (S clock : ℕ)
    (hS : Fintype.card final.Label *
      Fintype.card (Fin Q ×
        (streams.metadataStream.Label ×
          (streams.baseStream.Label × streams.selectorStream.Label))) ≤ S)
    (hNQ : Npub ≤ Q) :
    Workspace.Types.CommComplexity.D
      (successorStage src streams final R activity ξ₀ S clock hS hNQ).matrix ≤
      Workspace.Types.CommComplexity.D R +
        (Nat.clog 2 s + Nat.clog 2 q₂ + Nat.clog 2 (q₁ + s + 1) +
        Nat.clog 2 w + Nat.clog 2 Q) := by
  exact Sources.indexed_successor_universal_D_le src streams final activity ξ₀ R

theorem successorStage_yes_upper
    {μI : PositiveRationalLaw I} {w Q Npub : ℕ} [NeZero w] [NeZero Q]
    (streams : Sources.InternalStreams src μI w)
    (final : CodeSource D Q (Fin w × Sources.Column src)
      ((PositiveRationalLaw.uniform (Fin w)).prod (Sources.columnLaw src)))
    (R : X → Y → Bool) (assign : I → Fin s)
    (activity : I → Fin q₂ → Option (Fin s))
    (hc : CollisionFree assign activity) (ξ₀ : Tail s Y)
    (S clock : ℕ)
    (hS : Fintype.card final.Label *
      Fintype.card (Fin Q ×
        (streams.metadataStream.Label ×
          (streams.baseStream.Label × streams.selectorStream.Label))) ≤ S)
    (hNQ : Npub ≤ Q) :
    Workspace.Types.CommComplexity.D
      (successorStage src streams final R activity ξ₀ S clock hS hNQ).matrix ≤
      Workspace.Types.CommComplexity.D R +
        (Nat.clog 2 s + Nat.clog 2 q₂ + Nat.clog 2 (q₁ + 2) +
        Nat.clog 2 w + Nat.clog 2 Q) := by
  exact Sources.indexed_successor_yes_D_le src streams final assign activity hc ξ₀ R

#print axioms successorStage_cost_profile
#print axioms successorStage_universal_upper
#print axioms successorStage_yes_upper

end CurrentAdditive.IndexedStagePresentation
