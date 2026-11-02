import CurrentAdditive.DeterministicIndexedUpper

/-! Appendix I `det:entries`: the indexed first and second template matrices.
These upper bounds concern the actual decoded sources, with no gap premise. -/

namespace CurrentAdditive.DeterministicIndexedMatrix

open Paper2 Paper2.SourceMatrix Workspace.Types.CommComplexity

variable {X Y : Type*} [Fintype X] [Fintype Y]
  [DecidableEq X] [DecidableEq Y]
  {D q₁ q₂ s : ℕ} [NeZero s] [NeZero q₁] [NeZero q₂]
  {μX : PositiveRationalLaw X} {μY : PositiveRationalLaw Y}
  (src : Sources (D := D) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY)

namespace Sources

def M₁ (R : X → Y → Bool) : InnerRow q₁ X → src.gamma.Label → Bool :=
  fun a γ => SourceMatrix.M₁ R a (gammaWord src γ)

def A (R : X → Y → Bool) : src.gamma.Label → InnerRow q₁ X → Bool :=
  fun γ a => M₁ src R a γ

def T (R : X → Y → Bool) : src.inner.Label → J src → Bool :=
  fun z j => A src R j.2 (innerWord src z j.1)

@[simp] theorem M₁_entry (R : X → Y → Bool)
    (r : Fin q₁) (u : X) (γ : src.gamma.Label) :
    M₁ src R (r, u) γ = R u (head (gammaWord src γ) r) := rfl

@[simp] theorem T_entry (R : X → Y → Bool)
    (z : src.inner.Label) (j : J src) :
    T src R z j = M₁ src R (src.inner.decode z j.1) j.2 := rfl

theorem M₁_D_le (R : X → Y → Bool) :
    Workspace.Types.CommComplexity.D (M₁ src R) ≤
      Nat.clog 2 q₁ + Workspace.Types.CommComplexity.D R := by
  exact Paper2.indexedInterlace_D_le R (NeZero.pos q₁)
    (fun γ r => head (gammaWord src γ) r)

theorem A_D_eq_M₁ (R : X → Y → Bool) :
    Workspace.Types.CommComplexity.D (A src R) =
      Workspace.Types.CommComplexity.D (M₁ src R) := by
  exact transpose_D _

theorem T_D_le (R : X → Y → Bool) :
    Workspace.Types.CommComplexity.D (T src R) ≤
      Nat.clog 2 q₂ + Workspace.Types.CommComplexity.D (A src R) := by
  exact Paper2.indexedInterlace_transpose_D_le
    (A src R) (NeZero.pos q₂) (innerWord src)

end Sources

end CurrentAdditive.DeterministicIndexedMatrix
