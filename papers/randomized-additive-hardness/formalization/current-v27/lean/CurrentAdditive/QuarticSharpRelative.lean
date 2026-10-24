import CurrentAdditive.RandomizedQuarticSchedule
import Paper2.SharpRelative

namespace CurrentAdditive.QuarticSharpRelative

open Paper2 Paper2.RestorationWidthScheduleScratch

variable {V E : Type*} [Fintype V] [Nonempty V] [Fintype E]

/-- A source-only explicit cutoff for a relative quartic overhead error. -/
def cutoff (Δ : ℕ) (γ ε : ℚ) : ℕ :=
  Paper2.LogSquareCutoff.cutoff 0
    (14 * Paper2.SharpRelative.multiplier ε)
    ((64 + RandomizedSchedule.coefficientExponent27 Δ γ) *
      Paper2.SharpRelative.multiplier ε)

theorem relative_overhead27 (edge : E → Bool → V)
    (L Δ : ℕ) (γ ε : ℚ)
    (hL : cutoff Δ γ ε ≤ L)
    (hγ : 0 < γ) (hΔ : 0 < Δ) (hε : 0 < ε)
    (hincident : ∀ v, ∃ e b, edge e b = v)
    (hdegree : ∀ v, SourceItems.degree edge v ≤ Δ) :
    L ≤ RandomizedSchedule.overhead27 (V := V) (E := E) L Δ γ ∧
    (RandomizedSchedule.overhead27 (V := V) (E := E) L Δ γ : ℚ) ≤
      (1 + ε) * L := by
  let K := Paper2.SharpRelative.multiplier ε
  let d := 14 * ell L + 64 + RandomizedSchedule.coefficientExponent27 Δ γ
  have hK : 1 ≤ ε * (K : ℚ) := Paper2.SharpRelative.multiplier_scaled ε hε
  have hL1 : 1 ≤ L := by
    have hc : 0 < cutoff Δ γ ε := by
      unfold cutoff Paper2.LogSquareCutoff.cutoff
      positivity
    omega
  have hraw := RandomizedSchedule.overhead27_bounds (V := V) (E := E)
    edge L Δ γ hL1 hγ hΔ hincident hdegree
  have hlow : L ≤ RandomizedSchedule.overhead27 (V := V) (E := E) L Δ γ := hraw.1
  have hupp : RandomizedSchedule.overhead27 (V := V) (E := E) L Δ γ ≤
      L + d := by
    dsimp [d]
    omega
  have hpoly := Paper2.LogSquareCutoff.quadratic_log_le 0
    (14 * K) ((64 + RandomizedSchedule.coefficientExponent27 Δ γ) * K) L hL
  have hKd : K * d ≤ L := by
    have heq : K * d =
        0 * (ell L) ^ 2 + (14 * K) * ell L +
          (64 + RandomizedSchedule.coefficientExponent27 Δ γ) * K := by
      dsimp [d]
      ring
    rw [heq]
    exact hpoly
  constructor
  · exact hlow
  · have hKdQ : (K : ℚ) * (d : ℚ) ≤ (L : ℚ) := by exact_mod_cast hKd
    have hdQ : (0 : ℚ) ≤ (d : ℚ) := by positivity
    have hLd : (RandomizedSchedule.overhead27 (V := V) (E := E) L Δ γ : ℚ) ≤
        (L : ℚ) + (d : ℚ) := by exact_mod_cast hupp
    have haux : (d : ℚ) ≤ ε * (K : ℚ) * (d : ℚ) := by nlinarith
    have haux2 : ε * (K : ℚ) * (d : ℚ) ≤ ε * (L : ℚ) := by
      nlinarith [mul_le_mul_of_nonneg_left hKdQ hε.le]
    nlinarith

#print axioms relative_overhead27

end CurrentAdditive.QuarticSharpRelative
