import CurrentAdditive.GeneratedOwnerCountGuard
import CurrentAdditive.DeterministicIndexedUpper

/-! The universal protocol on the same literal generated N labels has
the manuscript's C-bit cost at current dyadic widths. -/

namespace CurrentAdditive.DeterministicIndexedMatrix.Sources

open Paper2 Paper2.SourceMatrix Workspace.Types.CommComplexity
open CurrentAdditive.DeterministicParameters

variable {I X Y : Type*} [Fintype I] [Fintype X] [Fintype Y]
  [DecidableEq X] [DecidableEq Y]
  {μX : PositiveRationalLaw X} {μY : PositiveRationalLaw Y}

theorem generated_N_upper_at_schedule (L : ℕ) (hL : 2004 ≤ L)
    [NeZero (q₁ L)] [NeZero (q₂ L)] [NeZero (s L)]
    (src : Sources (D := 8192) (q₁ := q₁ L) (q₂ := q₂ L)
      (s := s L) μX μY)
    (activity : I → Fin (q₂ L) → Option (Fin (s L)))
    (ξ₀ : Tail (s L) Y) (R : X → Y → Bool) (d : ℕ)
    (hD : D R = d) :
    D (N src R activity ξ₀) ≤ d + (L+3)/4 + 4*L + (L+3)/4 + 1 := by
  classical
  let a := (L+3)/4
  have hlogS : Nat.clog 2 (s L) = a := by
    rw [show s L = 2^a by rfl, Nat.clog_pow 2 a (by decide)]
  have hlogQ : Nat.clog 2 (q₂ L) = 4*L := by
    rw [q₂_eq_pow L, Nat.clog_pow 2 (4*L) (by decide)]
  have hsel : Nat.clog 2 (q₁ L + s L + 1) ≤ a+1 := by
    apply Nat.clog_le_of_le_pow
    rw [pow_succ, show 2^a = s L by rfl]
    have hs : 0 < s L := s_pos L
    unfold q₁
    omega
  have hu := indexed_B_universal_D_le src activity ξ₀ R
  rw [← indexed_N_D_eq_B src activity ξ₀ R, hlogS, hlogQ, hD] at hu
  omega

end CurrentAdditive.DeterministicIndexedMatrix.Sources

#print axioms CurrentAdditive.DeterministicIndexedMatrix.Sources.generated_N_upper_at_schedule
