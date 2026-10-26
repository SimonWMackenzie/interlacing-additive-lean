import Paper2.ExceptionalCutoff

set_option maxRecDepth 2048
set_option maxHeartbeats 1000000

/-! A coarse but effective all-larger cutoff for the actual exceptional-mass check. -/

namespace Paper2.ExceptionalCutoffScratch

open RestorationWidthScheduleScratch

variable {V Edges : Type*} [Fintype V] [Nonempty V] [Fintype Edges]

def kCoefficient (Δ : ℕ) (γ : ℚ) : ℕ :=
  19200 * 131072 ^ 2 * bCoefficient Δ γ *
    exceptionalCoefficient Δ γ * reciprocalCoefficient Δ γ

def kCutoff (Δ : ℕ) (γ : ℚ) : ℕ :=
  2 ^ WidthDomination.threshold (kCoefficient Δ γ) 10

private theorem numeric_bound (T r s E D P CE U : ℕ)
    (hU : 1 ≤ U) (hT : T ≤ P * U ^ 2)
    (hr : r ≤ U ^ 2) (hs : s ≤ 131072 * U)
    (hE : E ≤ CE * U ^ 4) :
    16 * (4 * (100 * T) * (r + 2) * s) * E * s * D ≤
      (19200 * 131072 ^ 2 * P * CE * D) * U ^ 10 := by
  have hU2 : 1 ≤ U ^ 2 := by
    have hp : 0 < U ^ 2 := pow_pos (by omega) _
    omega
  have hr3 : r + 2 ≤ 3 * U ^ 2 := by omega
  calc
    _ ≤ 16 * (4 * (100 * (P * U ^ 2)) * (3 * U ^ 2) * (131072 * U)) *
        (CE * U ^ 4) * (131072 * U) * D := by gcongr
    _ = (19200 * 131072 ^ 2 * P * CE * D) * U ^ 10 := by ring

private theorem eta_times_source_reciprocal_ge_one
    (edge : Edges → Bool → V) (L Δ : ℕ) (γ : ℚ)
    (hγ : 0 < γ) (hΔ : 0 < Δ)
    (hincident : ∀ v, ∃ e b, edge e b = v)
    (hdegree : ∀ v, SourceItems.degree edge v ≤ Δ) :
    (1 : ℚ) ≤
      SourceRationalScheduleScratch.eta (V := V) (E := Edges) L γ Δ *
      SourceProfileParameters.width L * reciprocalCoefficient Δ γ := by
  let c := SourceDensityScheduleScratch.etaConstant Δ γ
  let D := reciprocalCoefficient Δ γ
  let s := SourceProfileParameters.width L
  let η := SourceRationalScheduleScratch.eta (V := V) (E := Edges) L γ Δ
  have hc : 0 < c := SourceDensityScheduleScratch.etaConstant_pos Δ γ hΔ hγ
  have hs : (0 : ℚ) < s := by dsimp [s, SourceProfileParameters.width]; positivity
  have hη : c / s ≤ η :=
    (SourceDensityScheduleScratch.eta_bounds edge L Δ γ hγ hΔ hincident hdegree).1
  have hcs : c ≤ η * s := (div_le_iff₀ hs).mp hη
  have hD : (1 : ℚ) / c ≤ D := Nat.le_ceil _
  have h1 : (1 : ℚ) ≤ c * D := by
    have h := (div_le_iff₀ hc).mp hD
    nlinarith
  have hDnonneg : (0 : ℚ) ≤ D := by exact_mod_cast Nat.zero_le D
  have hmul := mul_le_mul_of_nonneg_right hcs hDnonneg
  exact h1.trans hmul

private theorem rational_mass_transfer (K η E s D w : ℚ)
    (hK : 0 ≤ K) (hη : 0 ≤ η) (hE : 0 ≤ E)
    (hηsd : 1 ≤ η * s * D)
    (hnum : 16 * K * E * s * D ≤ w) :
    K * E ≤ η * w / 16 := by
  apply (le_div_iff₀ (by norm_num : (0 : ℚ) < 16)).2
  have hnonneg : 0 ≤ 16 * K * E := by positivity
  calc
    K * E * 16 = 16 * K * E := by ring
    _ ≤ (16 * K * E) * (η * s * D) :=
      le_mul_of_one_le_right hnonneg hηsd
    _ = η * (16 * K * E * s * D) := by ring
    _ ≤ η * w := mul_le_mul_of_nonneg_left hnum hη

theorem actual_kCheck (edge : Edges → Bool → V)
    (L Δ : ℕ) (γ : ℚ) (hL : kCutoff Δ γ ≤ L)
    (hγ : 0 < γ) (hΔ : 0 < Δ)
    (hincident : ∀ v, ∃ e b, edge e b = v)
    (hdegree : ∀ v, SourceItems.degree edge v ≤ Δ) :
    RationalCoverSchedule.kCheck L (depth L) (width L)
      (SourceOverheadBounds.actualQ (V := V) (E := Edges) L γ Δ)
      (SourceRationalScheduleScratch.eta (V := V) (E := Edges) L γ Δ) := by
  let Q := SourceOverheadBounds.actualQ (V := V) (E := Edges) L γ Δ
  let η := SourceRationalScheduleScratch.eta (V := V) (E := Edges) L γ Δ
  let T := RestorationCoverParameters.b Q + 1
  let P := bCoefficient Δ γ
  let CE := exceptionalCoefficient Δ γ
  let D := reciprocalCoefficient Δ γ
  let s := SourceProfileParameters.width L
  let E₀ := RationalCoverSchedule.E Q η
  let U := L + 1
  have hL1 : 1 ≤ L := by
    have hp : 0 < kCutoff Δ γ := by unfold kCutoff; positivity
    omega
  have hU : 1 ≤ U := by dsimp [U]; omega
  have hb : RestorationCoverParameters.b Q ≤
      (ell L) ^ 2 + 2 * ell L +
        SourceOverheadBounds.coefficientExponent Δ γ + 9 := by
    simpa only [RestorationWidthScheduleScratch.depth] using
      (SourceOverheadBounds.b_upper (V := V) (E := Edges)
        edge L Δ γ hL1 hγ hΔ hincident hdegree)
  have hT : T ≤ P * U ^ 2 :=
    b_bound_poly _ _ _ _ (ell_le_L_plus_one L) hb
  have hr : depth L ≤ U ^ 2 := by
    simpa only [depth, U] using
      (Nat.pow_le_pow_left (ell_le_L_plus_one L) 2)
  have hs : s ≤ 131072 * U := source_width_le_linear L
  have hE : E₀ ≤ CE * U ^ 4 :=
    actual_exceptional_polynomial_bound edge L Δ γ hL1 hγ hΔ
      hincident hdegree
  have hnum := numeric_bound T (depth L) s E₀ D P CE U hU hT hr hs hE
  have hw := WidthDomination.polynomial_domination_large_L
    (kCoefficient Δ γ) 10 L hL
  have hnat : 16 * (4 * (100 * T) * (depth L + 2) * s) * E₀ * s * D ≤
      width L := by
    exact hnum.trans (by simpa only [kCoefficient, P, CE, D, U] using hw)
  have hηsd : (1 : ℚ) ≤ η * s * D :=
    eta_times_source_reciprocal_ge_one edge L Δ γ hγ hΔ hincident hdegree
  have hηpos : (0 : ℚ) < η := by
    have hc := SourceDensityScheduleScratch.etaConstant_pos Δ γ hΔ hγ
    have hspos : (0 : ℚ) < s := by dsimp [s, SourceProfileParameters.width]; positivity
    exact lt_of_lt_of_le (div_pos hc hspos)
      (SourceDensityScheduleScratch.eta_bounds edge L Δ γ hγ hΔ hincident hdegree).1
  have hK : RationalCoverSchedule.Kstar L (depth L) Q =
      (4 * RestorationCoverParameters.B2 Q * (depth L + 2) * s : ℕ) := by
    unfold RationalCoverSchedule.Kstar
    push_cast
    ring
  have hB2 : RestorationCoverParameters.B2 Q = 100 * T := rfl
  have hnumq : (16 : ℚ) * RationalCoverSchedule.Kstar L (depth L) Q *
      E₀ * s * D ≤ width L := by
    rw [hK, hB2]
    exact_mod_cast hnat
  have hKnonneg : (0 : ℚ) ≤ RationalCoverSchedule.Kstar L (depth L) Q := by
    rw [hK]
    exact_mod_cast Nat.zero_le (4 * RestorationCoverParameters.B2 Q * (depth L + 2) * s)
  unfold RationalCoverSchedule.kCheck
  have hE0nonneg : (0 : ℚ) ≤ E₀ := by exact_mod_cast Nat.zero_le E₀
  exact rational_mass_transfer _ _ _ _ _ _ hKnonneg hηpos.le
    hE0nonneg hηsd hnumq


end Paper2.ExceptionalCutoffScratch

