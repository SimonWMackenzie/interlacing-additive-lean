import Paper2.SourceOverheadBounds
import Paper2.WidthDomination
import Paper2.RationalCoverSchedule

set_option maxRecDepth 2048
set_option maxHeartbeats 1000000

/-!
An explicit graph-derived polynomial bound and all-larger width cutoff for
the actual frozen v12 exceptional-destination count. The rational ceilings
and small-set dyadic offset are the production definitions.
-/

namespace Paper2.ExceptionalCutoffScratch

open RestorationWidthScheduleScratch

variable {V Edges : Type*} [Fintype V] [Nonempty V] [Fintype Edges]

def reciprocalCoefficient (Δ : ℕ) (γ : ℚ) : ℕ :=
  Nat.ceil (1 / SourceDensityScheduleScratch.etaConstant Δ γ)

def bCoefficient (Δ : ℕ) (γ : ℚ) : ℕ :=
  SourceOverheadBounds.coefficientExponent Δ γ + 13

def exceptionalCoefficient (Δ : ℕ) (γ : ℚ) : ℕ :=
  3 * (12288 * (bCoefficient Δ γ) ^ 2 +
    131072 * reciprocalCoefficient Δ γ * bCoefficient Δ γ +
    200 * bCoefficient Δ γ)

def cutoff (Δ : ℕ) (γ : ℚ) : ℕ :=
  2 ^ WidthDomination.threshold (4 * exceptionalCoefficient Δ γ) 4

theorem ell_le_L_plus_one (L : ℕ) : ell L ≤ L + 1 := by
  apply (Nat.clog_le_iff_le_pow (by decide)).2
  exact WidthDomination.nat_le_two_pow (L + 1)

theorem b_bound_poly (b e C L : ℕ)
    (he : e ≤ L + 1) (hb : b ≤ e ^ 2 + 2 * e + C + 9) :
    b + 1 ≤ (C + 13) * (L + 1) ^ 2 := by
  have hpow : 1 ≤ (L + 1) ^ 2 := by
    have hp : 0 < (L + 1) ^ 2 := pow_pos (by omega) _
    omega
  have hsquare : e ^ 2 ≤ (L + 1) ^ 2 := by gcongr
  have hlinear : e ≤ (L + 1) ^ 2 := by nlinarith [he, hpow]
  have hconstant : C + 10 ≤ (C + 10) * (L + 1) ^ 2 := by
    nlinarith [Nat.mul_le_mul_left (C + 10) hpow]
  nlinarith

theorem source_width_le_linear (L : ℕ) :
    SourceProfileParameters.width L ≤ 131072 * (L + 1) := by
  have hpos : 0 < 65536 * (L + 1) := by omega
  have h := SourcePadding.powTwoCeil_lt_two_mul hpos
  change SourceProfileParameters.width L < 2 * (65536 * (L + 1)) at h
  omega

private theorem small_offset_bound (Q : ℕ) :
    2 ^ (RestorationCoverParameters.tExponent Q - 1) +
      RestorationCoverParameters.tExponent Q - 2 ≤
      3072 * (RestorationCoverParameters.b Q + 1) := by
  let T := RestorationCoverParameters.b Q + 1
  let N := 1024 * T
  have hN : 0 < N := by dsimp [N, T]; omega
  have hm : RestorationCoverParameters.tExponent Q ≤ N := by
    apply (Nat.clog_le_iff_le_pow (by decide)).2
    exact WidthDomination.nat_le_two_pow N
  have ht : RestorationCoverParameters.tStar Q < 2 * N := by
    exact SourcePadding.powTwoCeil_lt_two_mul hN
  have hp : 2 ^ (RestorationCoverParameters.tExponent Q - 1) ≤
      RestorationCoverParameters.tStar Q := by
    rw [RestorationCoverParameters.tStar_pow]
    exact Nat.pow_le_pow_right (by decide) (Nat.sub_le _ _)
  dsimp [N, T] at *
  omega

private theorem B1_le_reciprocal (Q s D : ℕ) (η c : ℚ)
    (hc : 0 < c) (hs : 0 < s) (hη : c / s ≤ η)
    (hD : (1 : ℚ) / c ≤ D) :
    RationalCoverSchedule.B1 Q η ≤
      (RestorationCoverParameters.b Q + 1) * s * D := by
  have hηpos : 0 < η := lt_of_lt_of_le (div_pos hc (by exact_mod_cast hs)) hη
  have hcs : c ≤ η * s := (div_le_iff₀ (by exact_mod_cast hs)).mp hη
  have h1 : (1 : ℚ) ≤ c * D := by
    have h := (div_le_iff₀ hc).mp hD
    nlinarith
  have hηsd : (1 : ℚ) ≤ η * s * D := by
    have hmul := mul_le_mul_of_nonneg_right hcs (by positivity : (0 : ℚ) ≤ D)
    nlinarith
  have hq : (((RestorationCoverParameters.b Q + 1 : ℕ) : ℚ) / η) ≤
      (((RestorationCoverParameters.b Q + 1) * s * D : ℕ) : ℚ) := by
    apply (div_le_iff₀ hηpos).2
    push_cast
    have hT : (0 : ℚ) ≤ RestorationCoverParameters.b Q + 1 := by positivity
    have hm := mul_le_mul_of_nonneg_left hηsd hT
    nlinarith
  exact (Nat.ceil_le).2 hq

private theorem ceiling16seven_le_three (n : ℕ) :
    Nat.ceil (16 * (n : ℚ) / 7) ≤ 3 * n := by
  apply (Nat.ceil_le).2
  push_cast
  nlinarith

private theorem exception_poly_in_T (Q s D : ℕ) (η : ℚ)
    (hB1 : RationalCoverSchedule.B1 Q η ≤
      (RestorationCoverParameters.b Q + 1) * s * D) :
    RationalCoverSchedule.E Q η ≤
      3 * (12288 * (RestorationCoverParameters.b Q + 1) ^ 2 +
        (RestorationCoverParameters.b Q + 1) * s * D +
        200 * (RestorationCoverParameters.b Q + 1)) := by
  let T := RestorationCoverParameters.b Q + 1
  let H := 2 ^ (RestorationCoverParameters.tExponent Q - 1) +
    RestorationCoverParameters.tExponent Q - 2
  let e₀ := RationalCoverSchedule.e0 Q η
  have hH : H ≤ 3072 * T := small_offset_bound Q
  have h0 : RestorationCoverParameters.B0 Q - 1 ≤ 4 * T := by
    dsimp [RestorationCoverParameters.B0, T]
    omega
  have h2 : RestorationCoverParameters.B2 Q - 1 ≤ 100 * T := by
    dsimp [RestorationCoverParameters.B2, T]
    omega
  have hfirst : (RestorationCoverParameters.B0 Q - 1) * H ≤
      12288 * T ^ 2 := by
    calc
      _ ≤ (4 * T) * (3072 * T) := Nat.mul_le_mul h0 hH
      _ = 12288 * T ^ 2 := by ring
  have he0 : e₀ ≤ 12288 * T ^ 2 + T * s * D + 200 * T := by
    have hB1tail : RationalCoverSchedule.B1 Q η - 1 ≤ T * s * D :=
      (Nat.sub_le _ _).trans hB1
    have hB2tail : 2 * (RestorationCoverParameters.B2 Q - 1) ≤ 200 * T := by
      omega
    change (RestorationCoverParameters.B0 Q - 1) * H +
      (RationalCoverSchedule.B1 Q η - 1) +
      2 * (RestorationCoverParameters.B2 Q - 1) ≤ _
    omega
  have hE : RationalCoverSchedule.E Q η ≤ 3 * e₀ := by
    exact ceiling16seven_le_three e₀
  exact hE.trans (Nat.mul_le_mul_left _ he0)

theorem actual_exceptional_polynomial_bound (edge : Edges → Bool → V)
    (L Δ : ℕ) (γ : ℚ) (hL : 1 ≤ L)
    (hγ : 0 < γ) (hΔ : 0 < Δ)
    (hincident : ∀ v, ∃ e b, edge e b = v)
    (hdegree : ∀ v, SourceItems.degree edge v ≤ Δ) :
    RationalCoverSchedule.E
      (SourceOverheadBounds.actualQ (V := V) (E := Edges) L γ Δ)
      (SourceRationalScheduleScratch.eta (V := V) (E := Edges) L γ Δ) ≤
      exceptionalCoefficient Δ γ * (L + 1) ^ 4 := by
  let Q := SourceOverheadBounds.actualQ (V := V) (E := Edges) L γ Δ
  let η := SourceRationalScheduleScratch.eta (V := V) (E := Edges) L γ Δ
  let c := SourceDensityScheduleScratch.etaConstant Δ γ
  let D := reciprocalCoefficient Δ γ
  let T := RestorationCoverParameters.b Q + 1
  let P := bCoefficient Δ γ
  let s := SourceProfileParameters.width L
  let U := L + 1
  have hc : 0 < c := SourceDensityScheduleScratch.etaConstant_pos Δ γ hΔ hγ
  have hs : 0 < s := by dsimp [s, SourceProfileParameters.width]; positivity
  have hη : c / s ≤ η :=
    (SourceDensityScheduleScratch.eta_bounds edge L Δ γ hγ hΔ hincident hdegree).1
  have hD : (1 : ℚ) / c ≤ D := by
    exact Nat.le_ceil _
  have hB1 : RationalCoverSchedule.B1 Q η ≤ T * s * D :=
    B1_le_reciprocal Q s D η c hc hs hη hD
  have hraw := exception_poly_in_T Q s D η hB1
  have hb : RestorationCoverParameters.b Q ≤
      (ell L) ^ 2 + 2 * ell L +
        SourceOverheadBounds.coefficientExponent Δ γ + 9 := by
    simpa only [RestorationWidthScheduleScratch.depth] using
      (SourceOverheadBounds.b_upper (V := V) (E := Edges)
        edge L Δ γ hL hγ hΔ hincident hdegree)
  have hT : T ≤ P * U ^ 2 :=
    b_bound_poly _ _ _ _ (ell_le_L_plus_one L) hb
  have hsU : s ≤ 131072 * U := source_width_le_linear L
  have hU1 : 1 ≤ U := by dsimp [U]; omega
  have hU2 : U ^ 2 ≤ U ^ 4 :=
    Nat.pow_le_pow_right hU1 (by omega)
  have hU3 : U ^ 3 ≤ U ^ 4 :=
    Nat.pow_le_pow_right hU1 (by omega)
  have hT2 : T ^ 2 ≤ P ^ 2 * U ^ 4 := by
    calc
      _ ≤ (P * U ^ 2) ^ 2 := by gcongr
      _ = P ^ 2 * U ^ 4 := by ring
  have hTs : T * s * D ≤ 131072 * D * P * U ^ 4 := by
    calc
      _ ≤ (P * U ^ 2) * (131072 * U) * D := by gcongr
      _ = 131072 * D * P * U ^ 3 := by ring
      _ ≤ 131072 * D * P * U ^ 4 := by gcongr
  have hT4 : T ≤ P * U ^ 4 := hT.trans (by gcongr)
  calc
    _ ≤ 3 * (12288 * T ^ 2 + T * s * D + 200 * T) := hraw
    _ ≤ 3 * (12288 * (P ^ 2 * U ^ 4) +
      131072 * D * P * U ^ 4 + 200 * (P * U ^ 4)) := by gcongr
    _ = exceptionalCoefficient Δ γ * (L + 1) ^ 4 := by
      dsimp [exceptionalCoefficient, P, U]
      ring

theorem actual_exceptional_quarter_check (edge : Edges → Bool → V)
    (L Δ : ℕ) (γ : ℚ) (hL : cutoff Δ γ ≤ L)
    (hγ : 0 < γ) (hΔ : 0 < Δ)
    (hincident : ∀ v, ∃ e b, edge e b = v)
    (hdegree : ∀ v, SourceItems.degree edge v ≤ Δ) :
    RationalCoverSchedule.quarterCheck
      (RestorationWidthScheduleScratch.width L)
      (SourceOverheadBounds.actualQ (V := V) (E := Edges) L γ Δ)
      (SourceRationalScheduleScratch.eta (V := V) (E := Edges) L γ Δ) := by
  have hL1 : 1 ≤ L := by
    have hp : 0 < cutoff Δ γ := by unfold cutoff; positivity
    omega
  have hE := actual_exceptional_polynomial_bound edge L Δ γ hL1
    hγ hΔ hincident hdegree
  have hw := WidthDomination.polynomial_domination_large_L
    (4 * exceptionalCoefficient Δ γ) 4 L hL
  unfold RationalCoverSchedule.quarterCheck
  calc
    4 * RationalCoverSchedule.E
        (SourceOverheadBounds.actualQ (V := V) (E := Edges) L γ Δ)
        (SourceRationalScheduleScratch.eta (V := V) (E := Edges) L γ Δ) ≤
      4 * (exceptionalCoefficient Δ γ * (L + 1) ^ 4) :=
        Nat.mul_le_mul_left 4 hE
    _ = (4 * exceptionalCoefficient Δ γ) * (L + 1) ^ 4 := by ring
    _ ≤ RestorationWidthScheduleScratch.width L := hw


end Paper2.ExceptionalCutoffScratch

