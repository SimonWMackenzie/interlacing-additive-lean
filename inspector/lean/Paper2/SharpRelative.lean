import Paper2.SourceOverheadBounds
import Paper2.LogSquareCutoff

/-!
Private proof of an explicit source-faithful relative overhead cutoff.
This uses the actual dyadic public Q, not a surrogate size assumption.
-/

namespace Paper2.SharpRelative

open Paper2.SourceOverheadBounds Paper2.RestorationWidthScheduleScratch

variable {V E : Type*} [Fintype V] [Nonempty V] [Fintype E]

/-- Explicit positive-rational reciprocal multiplier. -/
def multiplier (ε : ℚ) : ℕ := Nat.ceil (1 / ε)

/-- A graph-independent cutoff depending only on `Δ`, `γ`, and `ε`. -/
def cutoff (Δ : ℕ) (γ ε : ℚ) : ℕ :=
  LogSquareCutoff.cutoff (2 * multiplier ε) (6 * multiplier ε)
    ((64 + SourceOverheadBounds.coefficientExponent Δ γ) * multiplier ε)

theorem multiplier_scaled (ε : ℚ) (hε : 0 < ε) :
    1 ≤ ε * (multiplier ε : ℚ) := by
  have hc : 1 / ε ≤ (multiplier ε : ℚ) := Nat.le_ceil _
  have hm := (div_le_iff₀ hε).mp hc
  nlinarith

theorem relative_overhead (edge : E → Bool → V) (L Δ : ℕ) (γ ε : ℚ)
    (hL : cutoff Δ γ ε ≤ L) (hγ : 0 < γ) (hΔ : 0 < Δ)
    (hε : 0 < ε)
    (hincident : ∀ v, ∃ e b, edge e b = v)
    (hdegree : ∀ v, SourceItems.degree edge v ≤ Δ) :
    L ≤ SourceOverheadBounds.overhead (V := V) (E := E) L Δ γ ∧
    (SourceOverheadBounds.overhead (V := V) (E := E) L Δ γ : ℚ) ≤
      (1 + ε) * L := by
  let K := multiplier ε
  let d := 2 * (ell L) ^ 2 + 6 * ell L + 64 +
    SourceOverheadBounds.coefficientExponent Δ γ
  have hK : 1 ≤ ε * (K : ℚ) := multiplier_scaled ε hε
  have hL1 : 1 ≤ L := by
    have hc : 0 < cutoff Δ γ ε := by
      unfold cutoff LogSquareCutoff.cutoff
      positivity
    omega
  have hraw := SourceOverheadBounds.overhead_bounds (V := V) (E := E)
    edge L Δ γ hL1 hγ hΔ hincident hdegree
  have hlow : L ≤ SourceOverheadBounds.overhead (V := V) (E := E) L Δ γ := by
    rcases hraw with ⟨hlo, _⟩
    dsimp [depth] at hlo
    omega
  have hupp : SourceOverheadBounds.overhead (V := V) (E := E) L Δ γ ≤
      L + d := by
    have h := hraw.2
    dsimp [depth] at h
    dsimp [d, depth]
    omega
  have hpoly := LogSquareCutoff.quadratic_log_le
    (2 * K) (6 * K)
    ((64 + SourceOverheadBounds.coefficientExponent Δ γ) * K) L hL
  have hKd : K * d ≤ L := by
    have heq : K * d =
      2 * K * (ell L) ^ 2 + 6 * K * ell L +
        (64 + SourceOverheadBounds.coefficientExponent Δ γ) * K := by
      dsimp [d]
      ring
    rw [heq]
    exact hpoly
  constructor
  · exact hlow
  · have hKdQ : (K : ℚ) * (d : ℚ) ≤ (L : ℚ) := by exact_mod_cast hKd
    have hdQ : (0 : ℚ) ≤ (d : ℚ) := by positivity
    have hLd : (SourceOverheadBounds.overhead (V := V) (E := E) L Δ γ : ℚ) ≤
        (L : ℚ) + (d : ℚ) := by exact_mod_cast hupp
    have haux : (d : ℚ) ≤ ε * (K : ℚ) * (d : ℚ) := by
      nlinarith
    have haux2 : ε * (K : ℚ) * (d : ℚ) ≤ ε * (L : ℚ) := by
      nlinarith [mul_le_mul_of_nonneg_left hKdQ hε.le]
    nlinarith

end Paper2.SharpRelative
