import CurrentAdditive.GeneratedNExactNearFull

/-! The generated internal interlace has its exact manuscript upper
budget once the same indexed N has its exact cost. -/

namespace CurrentAdditive.DeterministicIndexedMatrix.Sources

open Paper2 Paper2.SourceMatrix Workspace.Types.CommComplexity
open CurrentAdditive.DeterministicParameters

variable {I X Y : Type*} [Fintype I] [Fintype X] [Fintype Y]
  [DecidableEq I] [DecidableEq X] [DecidableEq Y]
  {μX : PositiveRationalLaw X} {μY : PositiveRationalLaw Y}

theorem generated_W_upper_at_schedule (L d : ℕ)
    [NeZero (q₁ L)] [NeZero (q₂ L)] [NeZero (s L)] [NeZero (w L)]
    (src : Sources (D := 8192) (q₁ := q₁ L) (q₂ := q₂ L)
      (s := s L) μX μY)
    {μI : PositiveRationalLaw I}
    (streams : InternalStreams src μI (w L))
    (R : X → Y → Bool)
    (activity : I → Fin (q₂ L) → Option (Fin (s L)))
    (ξ₀ : Tail (s L) Y)
    (hN : D (N src R activity ξ₀) =
      d+(L+3)/4+4*L+(L+3)/4+1) :
    D (W src streams R activity ξ₀) ≤
      d+(L+3)/4+4*L+(L+3)/4+1+2*L := by
  have hu := indexed_W_D_le src streams activity ξ₀ R
  have hlogW : Nat.clog 2 (w L) = 2*L := by
    rw [w_eq_pow L, Nat.clog_pow 2 (2*L) (by decide)]
  rw [hlogW, hN] at hu
  omega

end CurrentAdditive.DeterministicIndexedMatrix.Sources

#print axioms CurrentAdditive.DeterministicIndexedMatrix.Sources.generated_W_upper_at_schedule
