import Paper2.SourceOverheadBounds
import Paper2.WidthDomination

set_option maxRecDepth 2048
set_option maxHeartbeats 1000000

/-!
An effective cutoff for the literal v12 Appendix C `w/4 ≥ t_*` guard.
No exceptional-set count or mass guard is assumed.
-/

namespace Paper2.WidthCoversTStar

open SourceOverheadBounds RestorationWidthScheduleScratch

variable {V E : Type*} [Fintype V] [Nonempty V] [Fintype E]

/-- The coefficient absorbs the dyadic-rounding factor, the factor four in
the guard, and the actual Q exponent's additive constant. -/
def polynomialCoefficient (Δ : ℕ) (γ : ℚ) : ℕ :=
  8192 * (SourceOverheadBounds.coefficientExponent Δ γ + 13)

/-- A concrete public lower threshold, depending only on graph-source
constants, beyond which the restoration width covers the whole small-set
capacity four times over. -/
def cutoff (Δ : ℕ) (γ : ℚ) : ℕ :=
  2 ^ WidthDomination.threshold (polynomialCoefficient Δ γ) 2

private theorem ell_le_L_plus_one (L : ℕ) : ell L ≤ L + 1 := by
  apply (Nat.clog_le_iff_le_pow (by decide)).2
  exact WidthDomination.nat_le_two_pow (L + 1)

private theorem tStar_lt_linear (Q : ℕ) :
    RestorationCoverParameters.tStar Q <
      2048 * (RestorationCoverParameters.b Q + 1) := by
  have hpos : 0 < 1024 * (RestorationCoverParameters.b Q + 1) := by omega
  have h := SourcePadding.powTwoCeil_lt_two_mul hpos
  simpa only [RestorationCoverParameters.tStar,
    show 2 * (1024 * (RestorationCoverParameters.b Q + 1)) =
      2048 * (RestorationCoverParameters.b Q + 1) by ring] using h

private theorem b_bound_poly (b e C L : ℕ)
    (he : e ≤ L + 1)
    (hb : b ≤ e ^ 2 + 2 * e + C + 9) :
    b + 1 ≤ (C + 13) * (L + 1) ^ 2 := by
  have hpow : 1 ≤ (L + 1) ^ 2 := by
    have hp : 0 < (L + 1) ^ 2 := pow_pos (by omega) _
    omega
  have hsquare : e ^ 2 ≤ (L + 1) ^ 2 := by gcongr
  have hlinear : e ≤ (L + 1) ^ 2 := by nlinarith [he, hpow]
  have hconstant : C + 10 ≤ (C + 10) * (L + 1) ^ 2 := by
    nlinarith [Nat.mul_le_mul_left (C + 10) hpow]
  nlinarith

/-- The exact scheduled power-of-two small-set capacity obeys `4*t_*≤w`
for every `L` beyond the displayed source-only cutoff. -/
theorem four_tStar_le_width (edge : E → Bool → V)
    (L Δ : ℕ) (γ : ℚ)
    (hL : cutoff Δ γ ≤ L)
    (hγ : 0 < γ) (hΔ : 0 < Δ)
    (hincident : ∀ v, ∃ e b, edge e b = v)
    (hdegree : ∀ v, SourceItems.degree edge v ≤ Δ) :
    4 * RestorationCoverParameters.tStar
      (SourceOverheadBounds.actualQ (V := V) (E := E) L γ Δ) ≤
      RestorationWidthScheduleScratch.width L := by
  let Q := SourceOverheadBounds.actualQ (V := V) (E := E) L γ Δ
  let b := RestorationCoverParameters.b Q
  let e := ell L
  let C := SourceOverheadBounds.coefficientExponent Δ γ
  have hL1 : 1 ≤ L := by
    have hp : 0 < cutoff Δ γ := by unfold cutoff; positivity
    omega
  have hb : b ≤ e ^ 2 + 2 * e + C + 9 := by
    simpa only [RestorationWidthScheduleScratch.depth] using
      (SourceOverheadBounds.b_upper (V := V) (E := E)
        edge L Δ γ hL1 hγ hΔ hincident hdegree)
  have ht : RestorationCoverParameters.tStar Q < 2048 * (b + 1) :=
    tStar_lt_linear Q
  have he : e ≤ L + 1 := ell_le_L_plus_one L
  have hbpoly : b + 1 ≤ (C + 13) * (L + 1) ^ 2 :=
    b_bound_poly b e C L he hb
  have hw := WidthDomination.polynomial_domination_large_L
    (polynomialCoefficient Δ γ) 2 L hL
  calc
    4 * RestorationCoverParameters.tStar Q ≤ 8192 * (b + 1) := by omega
    _ ≤ 8192 * ((C + 13) * (L + 1) ^ 2) :=
      Nat.mul_le_mul_left _ hbpoly
    _ = polynomialCoefficient Δ γ * (L + 1) ^ 2 := by
      simp only [polynomialCoefficient, C]
      ring
    _ ≤ RestorationWidthScheduleScratch.width L := hw

/-- The manuscript's division form of the same admissibility check. -/
theorem tStar_le_width_div_four (edge : E → Bool → V)
    (L Δ : ℕ) (γ : ℚ)
    (hL : cutoff Δ γ ≤ L)
    (hγ : 0 < γ) (hΔ : 0 < Δ)
    (hincident : ∀ v, ∃ e b, edge e b = v)
    (hdegree : ∀ v, SourceItems.degree edge v ≤ Δ) :
    RestorationCoverParameters.tStar
      (SourceOverheadBounds.actualQ (V := V) (E := E) L γ Δ) ≤
      RestorationWidthScheduleScratch.width L / 4 := by
  exact (Nat.le_div_iff_mul_le (by decide)).2
    (by simpa only [mul_comm] using
      four_tStar_le_width edge L Δ γ hL hγ hΔ hincident hdegree)

#print axioms four_tStar_le_width
#print axioms tStar_le_width_div_four

end Paper2.WidthCoversTStar
