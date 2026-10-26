import Paper2.SourceOverheadBounds
import Paper2.LogSquareCutoff

/-!
The actual public-source overhead satisfies the frozen v12 Appendix C
`h ≤ 7L` admissibility check beyond an explicit graph-parameter cutoff.
The stronger `h ≤ 2L` is a conservative finite consequence of the reviewed
actual-Q sandwich and the reviewed ceiling-log quadratic cutoff.
-/

namespace Paper2.ParameterCutoff

open SourceOverheadBounds LogSquareCutoff
  RestorationWidthScheduleScratch

variable {V E : Type*} [Fintype V] [Nonempty V] [Fintype E]

/-- An explicit all-larger threshold for the source overhead comparison.
It depends only on the public rational source constants, not on an optimum,
protocol, colouring, base matrix or requested amplification count. -/
def overheadCutoff (Δ : ℕ) (γ : ℚ) : ℕ :=
  LogSquareCutoff.cutoff 2 6
    (64 + SourceOverheadBounds.coefficientExponent Δ γ)

theorem actual_overhead_le_two_L (edge : E → Bool → V)
    (L Δ : ℕ) (γ : ℚ)
    (hL : overheadCutoff Δ γ ≤ L)
    (hγ : 0 < γ) (hΔ : 0 < Δ)
    (hincident : ∀ v, ∃ e b, edge e b = v)
    (hdegree : ∀ v, SourceItems.degree edge v ≤ Δ) :
    SourceOverheadBounds.overhead (V := V) (E := E) L Δ γ ≤ 2 * L := by
  have hL1 : 1 ≤ L := by
    have hp : 0 < overheadCutoff Δ γ := by
      unfold overheadCutoff LogSquareCutoff.cutoff
      positivity
    omega
  have hpoly := LogSquareCutoff.quadratic_log_le
    2 6 (64 + SourceOverheadBounds.coefficientExponent Δ γ) L hL
  have hbound := (SourceOverheadBounds.overhead_bounds (V := V) (E := E)
    edge L Δ γ hL1 hγ hΔ hincident hdegree).2
  dsimp [RestorationWidthScheduleScratch.depth] at hbound
  omega

theorem actual_overhead_le_seven_L (edge : E → Bool → V)
    (L Δ : ℕ) (γ : ℚ)
    (hL : overheadCutoff Δ γ ≤ L)
    (hγ : 0 < γ) (hΔ : 0 < Δ)
    (hincident : ∀ v, ∃ e b, edge e b = v)
    (hdegree : ∀ v, SourceItems.degree edge v ≤ Δ) :
    SourceOverheadBounds.overhead (V := V) (E := E) L Δ γ ≤ 7 * L := by
  have h := actual_overhead_le_two_L edge L Δ γ hL hγ hΔ hincident hdegree
  omega

#print axioms actual_overhead_le_two_L
#print axioms actual_overhead_le_seven_L

end Paper2.ParameterCutoff
