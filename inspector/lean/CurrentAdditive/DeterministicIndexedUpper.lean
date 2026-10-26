import CurrentAdditive.DeterministicIndexedSuccessor

/-! Appendix I: transport of the checked protocol upper bounds to the actual
indexed deterministic successor. No NO lower profile is asserted here. -/

namespace CurrentAdditive.DeterministicIndexedMatrix

open Paper2 Paper2.SourceMatrix Workspace.Types.CommComplexity

variable {I X Y : Type*} [Fintype I] [Fintype X] [Fintype Y]
  [DecidableEq I] [DecidableEq X] [DecidableEq Y]
  {D q₁ q₂ s : ℕ} [NeZero s] [NeZero q₁] [NeZero q₂]
  {μX : PositiveRationalLaw X} {μY : PositiveRationalLaw Y}
  (src : Sources (D := D) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY)

namespace Sources

theorem indexed_B_yes_D_le (assign : I → Fin s)
    (activity : I → Fin q₂ → Option (Fin s))
    (hc : CollisionFree assign activity) (ξ₀ : Tail s Y)
    (R : X → Y → Bool) :
    Workspace.Types.CommComplexity.D (B src R activity ξ₀) ≤
      Nat.clog 2 s + Nat.clog 2 q₂ + Nat.clog 2 (q₁ + 2) +
        Workspace.Types.CommComplexity.D R := by
  obtain ⟨P, hcost, hcomp⟩ :=
    Nat.sInf_mem (Workspace.UpperBound.AchievableCosts_nonempty R)
  have hcst := yesProtocol_cost src assign activity ξ₀ P
  rw [hcost] at hcst
  have hmem : (yesProtocol src assign activity ξ₀ P).cost ∈
      AchievableCosts (B src R activity ξ₀) :=
    ⟨_, rfl, yesProtocol_computes src assign activity hc ξ₀ R P hcomp⟩
  exact (Nat.sInf_le hmem).trans hcst

theorem indexed_B_universal_D_le
    (activity : I → Fin q₂ → Option (Fin s)) (ξ₀ : Tail s Y)
    (R : X → Y → Bool) :
    Workspace.Types.CommComplexity.D (B src R activity ξ₀) ≤
      Nat.clog 2 s + Nat.clog 2 q₂ + Nat.clog 2 (q₁ + s + 1) +
        Workspace.Types.CommComplexity.D R := by
  obtain ⟨P, hcost, hcomp⟩ :=
    Nat.sInf_mem (Workspace.UpperBound.AchievableCosts_nonempty R)
  have hcst := universalProtocol_cost src activity ξ₀ P
  rw [hcost] at hcst
  have hmem : (universalProtocol src activity ξ₀ P).cost ∈
      AchievableCosts (B src R activity ξ₀) :=
    ⟨_, rfl, universalProtocol_computes src activity ξ₀ R P hcomp⟩
  exact (Nat.sInf_le hmem).trans hcst

theorem indexed_N_D_eq_B (activity : I → Fin q₂ → Option (Fin s))
    (ξ₀ : Tail s Y) (R : X → Y → Bool) :
    Workspace.Types.CommComplexity.D (N src R activity ξ₀) =
      Workspace.Types.CommComplexity.D (B src R activity ξ₀) := by
  exact transpose_D _

theorem indexed_W_D_le {μI : PositiveRationalLaw I} {w : ℕ} [NeZero w]
    (streams : InternalStreams src μI w)
    (activity : I → Fin q₂ → Option (Fin s)) (ξ₀ : Tail s Y)
    (R : X → Y → Bool) :
    Workspace.Types.CommComplexity.D (W src streams R activity ξ₀) ≤
      Nat.clog 2 w + Workspace.Types.CommComplexity.D (N src R activity ξ₀) := by
  exact Paper2.indexedInterlace_transpose_D_le
    (N src R activity ξ₀) (NeZero.pos w)
    (InternalStreams.decode src streams)

theorem indexed_successor_D_le {μI : PositiveRationalLaw I} {w Q : ℕ}
    [NeZero w] [NeZero Q] (streams : InternalStreams src μI w)
    (final : CodeSource D Q (Fin w × Column src)
      ((PositiveRationalLaw.uniform (Fin w)).prod (columnLaw src)))
    (activity : I → Fin q₂ → Option (Fin s)) (ξ₀ : Tail s Y)
    (R : X → Y → Bool) :
    Workspace.Types.CommComplexity.D
      (successor src streams final R activity ξ₀) ≤
      Nat.clog 2 Q + Nat.clog 2 w +
        Workspace.Types.CommComplexity.D (N src R activity ξ₀) := by
  have hfinal := Paper2.indexedInterlace_transpose_D_le
    (W src streams R activity ξ₀) (NeZero.pos Q) final.decode
  change Workspace.Types.CommComplexity.D
    (successor src streams final R activity ξ₀) ≤
      Nat.clog 2 Q +
        Workspace.Types.CommComplexity.D (W src streams R activity ξ₀) at hfinal
  have hinner := indexed_W_D_le src streams activity ξ₀ R
  omega

/-- YES transport for the exact successor labels. Only the collision-free
assignment enters this upper-bound proof; it is not a constructor input. -/
theorem indexed_successor_yes_D_le {μI : PositiveRationalLaw I} {w Q : ℕ}
    [NeZero w] [NeZero Q] (streams : InternalStreams src μI w)
    (final : CodeSource D Q (Fin w × Column src)
      ((PositiveRationalLaw.uniform (Fin w)).prod (columnLaw src)))
    (assign : I → Fin s) (activity : I → Fin q₂ → Option (Fin s))
    (hc : CollisionFree assign activity) (ξ₀ : Tail s Y)
    (R : X → Y → Bool) :
    Workspace.Types.CommComplexity.D
      (successor src streams final R activity ξ₀) ≤
      Workspace.Types.CommComplexity.D R +
        (Nat.clog 2 s + Nat.clog 2 q₂ + Nat.clog 2 (q₁ + 2) +
          Nat.clog 2 w + Nat.clog 2 Q) := by
  have hs := indexed_successor_D_le src streams final activity ξ₀ R
  have hn := indexed_N_D_eq_B src activity ξ₀ R
  have hb := indexed_B_yes_D_le src assign activity hc ξ₀ R
  omega

theorem indexed_successor_universal_D_le {μI : PositiveRationalLaw I} {w Q : ℕ}
    [NeZero w] [NeZero Q] (streams : InternalStreams src μI w)
    (final : CodeSource D Q (Fin w × Column src)
      ((PositiveRationalLaw.uniform (Fin w)).prod (columnLaw src)))
    (activity : I → Fin q₂ → Option (Fin s)) (ξ₀ : Tail s Y)
    (R : X → Y → Bool) :
    Workspace.Types.CommComplexity.D
      (successor src streams final R activity ξ₀) ≤
      Workspace.Types.CommComplexity.D R +
        (Nat.clog 2 s + Nat.clog 2 q₂ + Nat.clog 2 (q₁ + s + 1) +
          Nat.clog 2 w + Nat.clog 2 Q) := by
  have hs := indexed_successor_D_le src streams final activity ξ₀ R
  have hn := indexed_N_D_eq_B src activity ξ₀ R
  have hb := indexed_B_universal_D_le src activity ξ₀ R
  omega

end Sources

end CurrentAdditive.DeterministicIndexedMatrix
