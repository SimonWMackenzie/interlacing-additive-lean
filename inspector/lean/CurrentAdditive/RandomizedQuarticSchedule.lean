import CurrentAdditive.RandomizedSchedule
import Paper2.ExceptionalCutoff
import Paper2.RationalCoverSchedule
import Paper2.PublicScheduleAllLarge

set_option maxRecDepth 2048
set_option maxHeartbeats 1000000

namespace CurrentAdditive.QuarticSchedule

open Paper2
open Paper2.SourceProfileParameters Paper2.SourceDensityScheduleScratch
  Paper2.SourceRationalScheduleScratch Paper2.RestorationCoverParameters
  Paper2.RestorationWidthScheduleScratch

variable {V Edges : Type*} [Fintype V] [Nonempty V] [Fintype Edges]

private theorem ell_succ_le_pow (e : ℕ) : e + 1 ≤ 2 ^ e := by
  induction e with
  | zero => norm_num
  | succ e ih =>
      rw [pow_succ]
      have hp : 1 ≤ 2 ^ e := by omega
      omega

private theorem quartic_pow_step (e : ℕ) (he : 20 ≤ e) :
    (e + 2) ^ 4 ≤ 2 * (e + 1) ^ 4 := by
  nlinarith [sq_nonneg (e : ℤ), sq_nonneg ((e : ℤ) ^ 2),
    sq_nonneg ((e : ℤ) ^ 2 - 2 * e)]

private theorem quartic_le_pow (e : ℕ) (he : 20 ≤ e) :
    (e + 1) ^ 4 ≤ 2 ^ e := by
  induction e, he using Nat.le_induction with
  | base => norm_num
  | succ e he ih =>
      calc
        (e + 1 + 1) ^ 4 ≤ 2 * (e + 1) ^ 4 := quartic_pow_step e he
        _ ≤ 2 * 2 ^ e := Nat.mul_le_mul_left 2 ih
        _ = 2 ^ (e + 1) := by ring

private theorem cubic_domination (C e : ℕ)
    (he20 : 20 ≤ e) (heC : C ≤ e) :
    C * (e + 1) ^ 3 ≤ 2 ^ e := by
  calc
    C * (e + 1) ^ 3 ≤ (e + 1) * (e + 1) ^ 3 := by gcongr; omega
    _ = (e + 1) ^ 4 := by ring
    _ ≤ 2 ^ e := quartic_le_pow e he20

def bCoefficient27 (Δ : ℕ) (γ : ℚ) : ℕ :=
  RandomizedSchedule.coefficientExponent27 Δ γ + 16

def reciprocalCoefficient27 (Δ : ℕ) (γ : ℚ) : ℕ :=
  Nat.ceil (1 / etaConstant Δ γ)

def exceptionalCoefficient27 (Δ : ℕ) (γ : ℚ) : ℕ :=
  3 * (204900 * (bCoefficient27 Δ γ) ^ 2 +
    65536 * bCoefficient27 Δ γ * reciprocalCoefficient27 Δ γ +
    0)

/-- Exact v27 Section 5 exceptional cover size. -/
def e027 (Q : ℕ) (η : ℚ) : ℕ :=
  (RationalCoverSchedule.B1 Q η - 1) +
    (tStar Q / 4 + 1) * (B2 Q - 1)

def E27 (Q : ℕ) (η : ℚ) : ℕ := Nat.ceil ((16 * (e027 Q η : ℚ)) / 7)

def quarterCheck27Prop (w Q : ℕ) (η : ℚ) : Prop := 4 * E27 Q η ≤ w

def kCheck27Prop (L r w Q : ℕ) (η : ℚ) : Prop :=
  RationalCoverSchedule.Kstar L r Q * E27 Q η ≤ η * w / 16

def kCoefficient27 (Δ : ℕ) (γ : ℚ) : ℕ :=
  16 * 4 * 100 * 6 * 65536 ^ 2 *
    bCoefficient27 Δ γ * exceptionalCoefficient27 Δ γ *
      reciprocalCoefficient27 Δ γ

def cutoffExponent27 (Δ : ℕ) (γ : ℚ) : ℕ :=
  max 20 (max (kCoefficient27 Δ γ)
    (max (4 * exceptionalCoefficient27 Δ γ)
      (8192 * bCoefficient27 Δ γ)))

def cutoff27 (Δ : ℕ) (γ : ℚ) : ℕ :=
  2 ^ cutoffExponent27 Δ γ

theorem b27_upper (edge : Edges → Bool → V)
    (L Δ : ℕ) (γ : ℚ)
    (hL : 1 ≤ L) (hγ : 0 < γ) (hΔ : 0 < Δ)
    (hincident : ∀ v, ∃ e b, edge e b = v)
    (hdegree : ∀ v, SourceItems.degree edge v ≤ Δ) :
    b (RandomizedSchedule.Q27 (V := V) (E := Edges) L γ Δ) ≤
      6 * ell L + RandomizedSchedule.coefficientExponent27 Δ γ + 9 := by
  have hpow : 320 * RandomizedSchedule.Q27 (V := V) (E := Edges) L γ Δ ≤
      2 ^ (RandomizedSchedule.q27 (V := V) (E := Edges) L γ Δ + 9) := by
    rw [RandomizedSchedule.Q27_dyadic]
    rw [pow_add]
    norm_num
    omega
  have hb : b (RandomizedSchedule.Q27 (V := V) (E := Edges) L γ Δ) ≤
      RandomizedSchedule.q27 (V := V) (E := Edges) L γ Δ + 9 :=
    (Nat.clog_le_iff_le_pow (by decide)).2 hpow
  have hq := RandomizedSchedule.q27_upper edge L Δ γ hL hγ hΔ hincident hdegree
  exact hb.trans (by omega)

private theorem b_plus_one_linear (e C b0 : ℕ)
    (h : b0 ≤ 6 * e + C + 9) :
    b0 + 1 ≤ (C + 16) * (e + 1) := by
  nlinarith

private theorem B1_le_reciprocal (Q s D : ℕ) (η c : ℚ)
    (hc : 0 < c) (hs : 0 < s) (hη : c / s ≤ η)
    (hD : (1 : ℚ) / c ≤ D) :
    RationalCoverSchedule.B1 Q η ≤ (b Q + 1) * s * D := by
  have hηpos : 0 < η := lt_of_lt_of_le (div_pos hc (by exact_mod_cast hs)) hη
  have hcs : c ≤ η * s := (div_le_iff₀ (by exact_mod_cast hs)).mp hη
  have h1 : (1 : ℚ) ≤ c * D := by
    have h := (div_le_iff₀ hc).mp hD
    nlinarith
  have hηsd : (1 : ℚ) ≤ η * s * D := by
    have hmul := mul_le_mul_of_nonneg_right hcs (by positivity : (0 : ℚ) ≤ D)
    nlinarith
  have hq : (((b Q + 1 : ℕ) : ℚ) / η) ≤ (((b Q + 1) * s * D : ℕ) : ℚ) := by
    apply (div_le_iff₀ hηpos).2
    push_cast
    have hT : (0 : ℚ) ≤ b Q + 1 := by positivity
    have hm := mul_le_mul_of_nonneg_left hηsd hT
    nlinarith
  exact (Nat.ceil_le).2 hq

private theorem ceiling16seven_le_three (n : ℕ) :
    Nat.ceil (16 * (n : ℚ) / 7) ≤ 3 * n := by
  apply (Nat.ceil_le).2
  push_cast
  nlinarith

private theorem exception_poly_in_T (Q s D : ℕ) (η : ℚ)
    (hB1 : RationalCoverSchedule.B1 Q η ≤ (b Q + 1) * s * D) :
    E27 Q η ≤
      3 * (204900 * (b Q + 1) ^ 2 + (b Q + 1) * s * D) := by
  let T := b Q + 1
  let e₀ := e027 Q η
  have hN : 0 < 1024 * T := by dsimp [T]; omega
  have ht : tStar Q < 2048 * T := by
    have hh := SourcePadding.powTwoCeil_lt_two_mul hN
    change tStar Q < 2 * (1024 * T) at hh
    have hr : 2 * (1024 * T) = 2048 * T := by ring
    rw [hr] at hh
    exact hh
  have hm : tStar Q / 4 + 1 ≤ 2049 * T := by
    have hdiv : tStar Q / 4 ≤ tStar Q := Nat.div_le_self _ _
    dsimp [T]
    omega
  have h2 : B2 Q - 1 ≤ 100 * T := by dsimp [B2, T]; omega
  have hfirst : (tStar Q / 4 + 1) * (B2 Q - 1) ≤ 204900 * T ^ 2 := by
    calc
      _ ≤ (2049 * T) * (100 * T) := Nat.mul_le_mul hm h2
      _ = 204900 * T ^ 2 := by ring
  have he0 : e₀ ≤ 204900 * T ^ 2 + T * s * D := by
    have hB1tail : RationalCoverSchedule.B1 Q η - 1 ≤ T * s * D :=
      (Nat.sub_le _ _).trans hB1
    change (RationalCoverSchedule.B1 Q η - 1) +
      (tStar Q / 4 + 1) * (B2 Q - 1) ≤ _
    omega
  have hE : E27 Q η ≤ 3 * e₀ := by
    exact ceiling16seven_le_three e₀
  exact hE.trans (Nat.mul_le_mul_left _ he0)

theorem exceptional27_bound (edge : Edges → Bool → V)
    (L Δ : ℕ) (γ : ℚ)
    (hL : 1 ≤ L) (hγ : 0 < γ) (hΔ : 0 < Δ)
    (hincident : ∀ v, ∃ e b, edge e b = v)
    (hdegree : ∀ v, SourceItems.degree edge v ≤ Δ) :
    E27
      (RandomizedSchedule.Q27 (V := V) (E := Edges) L γ Δ)
      (SourceRationalScheduleScratch.eta (V := V) (E := Edges) L γ Δ) ≤
      exceptionalCoefficient27 Δ γ * 2 ^ ell L * (ell L + 1) := by
  let Q := RandomizedSchedule.Q27 (V := V) (E := Edges) L γ Δ
  let η := SourceRationalScheduleScratch.eta (V := V) (E := Edges) L γ Δ
  let c := etaConstant Δ γ
  let D := reciprocalCoefficient27 Δ γ
  let T := b Q + 1
  let P := bCoefficient27 Δ γ
  let s := SourceProfileParameters.width L
  let e := ell L
  let U := e + 1
  have hc : 0 < c := etaConstant_pos Δ γ hΔ hγ
  have hs : 0 < s := by dsimp [s, SourceProfileParameters.width]; positivity
  have hη : c / s ≤ η :=
    (SourceDensityScheduleScratch.eta_bounds edge L Δ γ hγ hΔ hincident hdegree).1
  have hD : (1 : ℚ) / c ≤ D := Nat.le_ceil _
  have hB1 : RationalCoverSchedule.B1 Q η ≤ T * s * D :=
    B1_le_reciprocal Q s D η c hc hs hη hD
  have hraw := exception_poly_in_T Q s D η hB1
  have hb := b27_upper edge L Δ γ hL hγ hΔ hincident hdegree
  have hT : T ≤ P * U := by
    exact b_plus_one_linear e
      (RandomizedSchedule.coefficientExponent27 Δ γ) (b Q) hb
  have hsU : s ≤ 65536 * 2 ^ e := SourceOverheadBounds.source_width_le L
  have hU : U ≤ 2 ^ e := ell_succ_le_pow e
  have hPow : 0 < 2 ^ e := by positivity
  have hT2 : T ^ 2 ≤ P ^ 2 * 2 ^ e * U := by
    calc
      T ^ 2 ≤ (P * U) ^ 2 := by gcongr
      _ = P ^ 2 * U * U := by ring
      _ ≤ P ^ 2 * 2 ^ e * U := by gcongr
  have hTs : T * s * D ≤ 65536 * P * D * 2 ^ e * U := by
    calc
      _ ≤ (P * U) * (65536 * 2 ^ e) * D := by gcongr
      _ = _ := by ring
  calc
    _ ≤ 3 * (204900 * T ^ 2 + T * s * D) := hraw
    _ ≤ 3 * (204900 * (P ^ 2 * 2 ^ e * U) +
      65536 * P * D * 2 ^ e * U) := by gcongr
    _ = exceptionalCoefficient27 Δ γ * 2 ^ ell L * (ell L + 1) := by
      dsimp [exceptionalCoefficient27, P, D, e, U]
      ring

private theorem k_numeric_bound (T e s E D P CE : ℕ)
    (hT : T ≤ P * (e + 1))
    (hs : s ≤ 65536 * 2 ^ e)
    (hE : E ≤ CE * 2 ^ e * (e + 1)) :
    16 * (4 * (100 * T) * (4 * e + 2) * s) * E * s * D ≤
      (16 * 4 * 100 * 6 * 65536 ^ 2 * P * CE * D) *
        2 ^ (3 * e) * (e + 1) ^ 3 := by
  have hr : 4 * e + 2 ≤ 6 * (e + 1) := by omega
  calc
    _ ≤ 16 * (4 * (100 * (P * (e + 1))) * (6 * (e + 1)) *
      (65536 * 2 ^ e)) * (CE * 2 ^ e * (e + 1)) *
      (65536 * 2 ^ e) * D := by gcongr
    _ = (16 * 4 * 100 * 6 * 65536 ^ 2 * P * CE * D) *
      2 ^ (3 * e) * (e + 1) ^ 3 := by
        rw [show 3 * e = e + e + e by omega, pow_add, pow_add]
        ring

private theorem eta_times_reciprocal_ge_one
    (edge : Edges → Bool → V) (L Δ : ℕ) (γ : ℚ)
    (hγ : 0 < γ) (hΔ : 0 < Δ)
    (hincident : ∀ v, ∃ e b, edge e b = v)
    (hdegree : ∀ v, SourceItems.degree edge v ≤ Δ) :
    (1 : ℚ) ≤
      SourceRationalScheduleScratch.eta (V := V) (E := Edges) L γ Δ *
      SourceProfileParameters.width L * reciprocalCoefficient27 Δ γ := by
  let c := etaConstant Δ γ
  let D := reciprocalCoefficient27 Δ γ
  let s := SourceProfileParameters.width L
  let η := SourceRationalScheduleScratch.eta (V := V) (E := Edges) L γ Δ
  have hc : 0 < c := etaConstant_pos Δ γ hΔ hγ
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

private theorem cutoff_ell (L Δ : ℕ) (γ : ℚ)
    (hL : cutoff27 Δ γ ≤ L) :
    cutoffExponent27 Δ γ ≤ ell L := by
  have hp : 2 ^ cutoffExponent27 Δ γ ≤ L + 1 := by
    exact (show cutoff27 Δ γ ≤ L from hL).trans (Nat.le_succ L)
  have hc := Nat.clog_mono_right 2 hp
  simpa only [ell, Nat.clog_pow 2 _ (by decide)] using hc

theorem kCheck27 (edge : Edges → Bool → V)
    (L Δ : ℕ) (γ : ℚ) (hL : cutoff27 Δ γ ≤ L)
    (hγ : 0 < γ) (hΔ : 0 < Δ)
    (hincident : ∀ v, ∃ e b, edge e b = v)
    (hdegree : ∀ v, SourceItems.degree edge v ≤ Δ) :
    kCheck27Prop L (4 * ell L)
      (RandomizedSchedule.width27 L)
      (RandomizedSchedule.Q27 (V := V) (E := Edges) L γ Δ)
      (SourceRationalScheduleScratch.eta (V := V) (E := Edges) L γ Δ) := by
  let Q := RandomizedSchedule.Q27 (V := V) (E := Edges) L γ Δ
  let η := SourceRationalScheduleScratch.eta (V := V) (E := Edges) L γ Δ
  let T := b Q + 1
  let P := bCoefficient27 Δ γ
  let CE := exceptionalCoefficient27 Δ γ
  let D := reciprocalCoefficient27 Δ γ
  let s := SourceProfileParameters.width L
  let E₀ := E27 Q η
  let e := ell L
  have he : cutoffExponent27 Δ γ ≤ e := cutoff_ell L Δ γ hL
  have he20 : 20 ≤ e := (le_max_left _ _).trans he
  have heC : kCoefficient27 Δ γ ≤ e :=
    (le_max_left _ _).trans ((le_max_right _ _).trans he)
  have hL1 : 1 ≤ L := by
    have hp : 0 < cutoff27 Δ γ := by unfold cutoff27; positivity
    omega
  have hb := b27_upper edge L Δ γ hL1 hγ hΔ hincident hdegree
  have hT : T ≤ P * (e + 1) :=
    b_plus_one_linear e (RandomizedSchedule.coefficientExponent27 Δ γ) (b Q) hb
  have hs : s ≤ 65536 * 2 ^ e := SourceOverheadBounds.source_width_le L
  have hE : E₀ ≤ CE * 2 ^ e * (e + 1) :=
    exceptional27_bound edge L Δ γ hL1 hγ hΔ hincident hdegree
  have hnum := k_numeric_bound T e s E₀ D P CE hT hs hE
  have hdom : kCoefficient27 Δ γ * (e + 1) ^ 3 ≤ 2 ^ e :=
    cubic_domination _ _ he20 heC
  have hnat : 16 * (4 * (100 * T) * (4 * e + 2) * s) * E₀ * s * D ≤
      RandomizedSchedule.width27 L := by
    calc
      _ ≤ kCoefficient27 Δ γ * 2 ^ (3 * e) * (e + 1) ^ 3 := by
        simpa only [kCoefficient27, P, CE, D] using hnum
      _ = (kCoefficient27 Δ γ * (e + 1) ^ 3) * 2 ^ (3 * e) := by ring
      _ ≤ 2 ^ e * 2 ^ (3 * e) := Nat.mul_le_mul_right _ hdom
      _ = RandomizedSchedule.width27 L := by
        dsimp [RandomizedSchedule.width27, e]
        rw [← pow_add]
        congr 1
        omega
  have hηsd : (1 : ℚ) ≤ η * s * D :=
    eta_times_reciprocal_ge_one edge L Δ γ hγ hΔ hincident hdegree
  have hηpos : (0 : ℚ) < η := by
    have hc := etaConstant_pos Δ γ hΔ hγ
    have hspos : (0 : ℚ) < s := by dsimp [s, SourceProfileParameters.width]; positivity
    exact lt_of_lt_of_le (div_pos hc hspos)
      (SourceDensityScheduleScratch.eta_bounds edge L Δ γ hγ hΔ hincident hdegree).1
  have hK : RationalCoverSchedule.Kstar L (4 * e) Q =
      (4 * B2 Q * (4 * e + 2) * s : ℕ) := by
    unfold RationalCoverSchedule.Kstar
    push_cast
    ring
  have hB2 : B2 Q = 100 * T := rfl
  have hnumq : (16 : ℚ) * RationalCoverSchedule.Kstar L (4 * e) Q *
      E₀ * s * D ≤ RandomizedSchedule.width27 L := by
    rw [hK, hB2]
    exact_mod_cast hnat
  have hKnonneg : (0 : ℚ) ≤ RationalCoverSchedule.Kstar L (4 * e) Q := by
    rw [hK]
    exact_mod_cast Nat.zero_le (4 * B2 Q * (4 * e + 2) * s)
  unfold kCheck27Prop
  have hE0nonneg : (0 : ℚ) ≤ E₀ := by exact_mod_cast Nat.zero_le E₀
  exact rational_mass_transfer _ _ _ _ _ _ hKnonneg hηpos.le
    hE0nonneg hηsd hnumq

theorem quarterCheck27 (edge : Edges → Bool → V)
    (L Δ : ℕ) (γ : ℚ) (hL : cutoff27 Δ γ ≤ L)
    (hγ : 0 < γ) (hΔ : 0 < Δ)
    (hincident : ∀ v, ∃ e b, edge e b = v)
    (hdegree : ∀ v, SourceItems.degree edge v ≤ Δ) :
    quarterCheck27Prop
      (RandomizedSchedule.width27 L)
      (RandomizedSchedule.Q27 (V := V) (E := Edges) L γ Δ)
      (SourceRationalScheduleScratch.eta (V := V) (E := Edges) L γ Δ) := by
  let e := ell L
  let U := e + 1
  let CE := exceptionalCoefficient27 Δ γ
  have he := cutoff_ell L Δ γ hL
  have he20 : 20 ≤ e := (le_max_left _ _).trans he
  have heC : 4 * CE ≤ e := by
    exact (le_max_left _ _).trans
      ((le_max_right _ _).trans ((le_max_right _ _).trans he))
  have hL1 : 1 ≤ L := by
    have hp : 0 < cutoff27 Δ γ := by unfold cutoff27; positivity
    omega
  have hE := exceptional27_bound edge L Δ γ hL1 hγ hΔ hincident hdegree
  have hdom : 4 * CE * U ^ 3 ≤ 2 ^ e := cubic_domination _ _ he20 heC
  have hU : U ≤ U ^ 3 := by
    have hU1 : 1 ≤ U := by dsimp [U]; omega
    calc
      U = U ^ 1 := by ring
      _ ≤ U ^ 3 := Nat.pow_le_pow_right hU1 (by decide : 1 ≤ 3)
  have hsmall : 4 * CE * U ≤ 2 ^ e :=
    (Nat.mul_le_mul_left _ hU).trans hdom
  have hpow : 2 ^ e ≤ 2 ^ (3 * e) :=
    Nat.pow_le_pow_right (by decide) (by omega)
  unfold quarterCheck27Prop
  calc
    4 * E27
        (RandomizedSchedule.Q27 (V := V) (E := Edges) L γ Δ)
        (SourceRationalScheduleScratch.eta (V := V) (E := Edges) L γ Δ) ≤
      4 * (CE * 2 ^ e * U) := Nat.mul_le_mul_left 4 hE
    _ = (4 * CE * U) * 2 ^ e := by ring
    _ ≤ 2 ^ e * 2 ^ e := Nat.mul_le_mul_right _ hsmall
    _ ≤ 2 ^ (3 * e) * 2 ^ e := Nat.mul_le_mul_right _ hpow
    _ = RandomizedSchedule.width27 L := by
      dsimp [RandomizedSchedule.width27, e]
      rw [← pow_add]
      congr 1
      omega

theorem tStar27_quarter (edge : Edges → Bool → V)
    (L Δ : ℕ) (γ : ℚ) (hL : cutoff27 Δ γ ≤ L)
    (hγ : 0 < γ) (hΔ : 0 < Δ)
    (hincident : ∀ v, ∃ e b, edge e b = v)
    (hdegree : ∀ v, SourceItems.degree edge v ≤ Δ) :
    4 * tStar (RandomizedSchedule.Q27 (V := V) (E := Edges) L γ Δ) ≤
      RandomizedSchedule.width27 L := by
  let Q := RandomizedSchedule.Q27 (V := V) (E := Edges) L γ Δ
  let e := ell L
  let U := e + 1
  let P := bCoefficient27 Δ γ
  have he := cutoff_ell L Δ γ hL
  have he20 : 20 ≤ e := (le_max_left _ _).trans he
  have heC : 8192 * P ≤ e := by
    exact (le_max_right _ _).trans
      ((le_max_right _ _).trans ((le_max_right _ _).trans he))
  have hL1 : 1 ≤ L := by
    have hp : 0 < cutoff27 Δ γ := by unfold cutoff27; positivity
    omega
  have hb := b27_upper edge L Δ γ hL1 hγ hΔ hincident hdegree
  have hT : b Q + 1 ≤ P * U :=
    b_plus_one_linear e (RandomizedSchedule.coefficientExponent27 Δ γ) (b Q) hb
  have hN : 0 < 1024 * (b Q + 1) := by omega
  have ht : tStar Q < 2048 * (b Q + 1) := by
    have hh := SourcePadding.powTwoCeil_lt_two_mul hN
    change tStar Q < 2 * (1024 * (b Q + 1)) at hh
    have hr : 2 * (1024 * (b Q + 1)) = 2048 * (b Q + 1) := by ring
    rw [hr] at hh
    exact hh
  have hdom : 8192 * P * U ^ 3 ≤ 2 ^ e :=
    cubic_domination _ _ he20 heC
  have hU : U ≤ U ^ 3 := by
    have hU1 : 1 ≤ U := by dsimp [U]; omega
    calc
      U = U ^ 1 := by ring
      _ ≤ U ^ 3 := Nat.pow_le_pow_right hU1 (by decide : 1 ≤ 3)
  have hsmall : 8192 * P * U ≤ 2 ^ e :=
    (Nat.mul_le_mul_left _ hU).trans hdom
  have hpow : 2 ^ e ≤ RandomizedSchedule.width27 L := by
    dsimp [RandomizedSchedule.width27, e]
    exact Nat.pow_le_pow_right (by decide) (by omega)
  calc
    4 * tStar Q ≤ 8192 * (b Q + 1) := by omega
    _ ≤ 8192 * (P * U) := Nat.mul_le_mul_left _ hT
    _ = 8192 * P * U := by ring
    _ ≤ 2 ^ e := hsmall
    _ ≤ RandomizedSchedule.width27 L := hpow

theorem width27_le_old (L : ℕ) (he : 4 ≤ ell L) :
    RandomizedSchedule.width27 L ≤ RestorationWidthScheduleScratch.width L := by
  unfold RandomizedSchedule.width27 RestorationWidthScheduleScratch.width
    RestorationWidthScheduleScratch.depth
  apply Nat.pow_le_pow_right (by decide)
  nlinarith

theorem allowance27_checks (edge : Edges → Bool → V)
    (L Δ : ℕ) (γ : ℚ)
    (hL : AllowanceSmallnessScratch.cutoff Δ γ ≤ L)
    (he : 4 ≤ ell L)
    (hγ : 0 < γ) (hΔ : 0 < Δ)
    (hincident : ∀ v, ∃ e b, edge e b = v)
    (hdegree : ∀ v, SourceItems.degree edge v ≤ Δ) :
    let q₂ := outerWidth L
    let w := RandomizedSchedule.width27 L
    let η := (SourceRationalScheduleScratch.eta (V := V) (E := Edges) L γ Δ : ℝ)
    2 * (w : ℝ) * x L + η / (16 * (127 / 128 : ℝ)) < 1 ∧
    2 * (w : ℝ) ^ 2 * x L ≤ η / (16 * (127 / 128 : ℝ)) ∧
    4 * (1 / 256 : ℝ) * w * q₂ * x L ≤ η / 32 ∧
    4 * (1 / 256 : ℝ) * w / q₂ ≤ η / 32 := by
  dsimp only
  have hW := width27_le_old L he
  have hWR : (RandomizedSchedule.width27 L : ℝ) ≤
      RestorationWidthScheduleScratch.width L := by exact_mod_cast hW
  have hx : 0 ≤ x L := (x_pos L).le
  have hq : (0 : ℝ) < outerWidth L := by
    exact_mod_cast (show 0 < outerWidth L by unfold outerWidth; positivity)
  have hOld := AllowanceSmallnessScratch.allowance_checks (V := V) (E := Edges)
    edge L Δ γ hγ hΔ hincident hdegree hL
  dsimp only at hOld
  constructor
  · have hh : 2 * (RandomizedSchedule.width27 L : ℝ) * x L ≤
        2 * (RestorationWidthScheduleScratch.width L : ℝ) * x L := by
      gcongr
    linarith [hOld.1]
  constructor
  · have hh : 2 * (RandomizedSchedule.width27 L : ℝ) ^ 2 * x L ≤
        2 * (RestorationWidthScheduleScratch.width L : ℝ) ^ 2 * x L := by
      have hsq : (RandomizedSchedule.width27 L : ℝ) ^ 2 ≤
          (RestorationWidthScheduleScratch.width L : ℝ) ^ 2 := by
        exact pow_le_pow_left₀ (by exact_mod_cast Nat.zero_le (RandomizedSchedule.width27 L)) hWR _
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hsq (by norm_num)) hx
    exact hh.trans hOld.2.1
  constructor
  · have hh : 4 * (1 / 256 : ℝ) * RandomizedSchedule.width27 L *
        outerWidth L * x L ≤
        4 * (1 / 256 : ℝ) * RestorationWidthScheduleScratch.width L *
          outerWidth L * x L := by
      have hc : 0 ≤ (4 * (1 / 256 : ℝ)) * outerWidth L * x L := by
        exact mul_nonneg (mul_nonneg (by norm_num)
          (by exact_mod_cast Nat.zero_le (outerWidth L))) hx
      have hm := mul_le_mul_of_nonneg_right hWR hc
      calc
        _ = (RandomizedSchedule.width27 L : ℝ) *
            ((4 * (1 / 256 : ℝ)) * outerWidth L * x L) := by ring
        _ ≤ (RestorationWidthScheduleScratch.width L : ℝ) *
            ((4 * (1 / 256 : ℝ)) * outerWidth L * x L) := hm
        _ = _ := by ring
    exact hh.trans hOld.2.2.1
  · have hh : 4 * (1 / 256 : ℝ) * RandomizedSchedule.width27 L /
        outerWidth L ≤
        4 * (1 / 256 : ℝ) * RestorationWidthScheduleScratch.width L /
          outerWidth L := by
      have hc : 0 ≤ (4 * (1 / 256 : ℝ)) / outerWidth L := by
        exact div_nonneg (by norm_num) hq.le
      have hm := mul_le_mul_of_nonneg_right hWR hc
      calc
        _ = (RandomizedSchedule.width27 L : ℝ) *
            ((4 * (1 / 256 : ℝ)) / outerWidth L) := by ring
        _ ≤ (RestorationWidthScheduleScratch.width L : ℝ) *
            ((4 * (1 / 256 : ℝ)) / outerWidth L) := hm
        _ = _ := by ring
    exact hh.trans hOld.2.2.2

def Checks27 (L Δ : ℕ) (γ : ℚ) : Prop :=
  let s := SourceProfileParameters.width L
  let q₂ := SourceProfileParameters.outerWidth L
  let w := RandomizedSchedule.width27 L
  let Q := RandomizedSchedule.Q27 (V := V) (E := Edges) L γ Δ
  let η := SourceRationalScheduleScratch.eta (V := V) (E := Edges) L γ Δ
  SourceRepetitionScratch.coordinateAdmissible L Edges ∧
  2 * (Fintype.card V + s - 3) ≤ q₂ ∧
  (4 : ℚ) * s ^ 2 * CompletePublicScheduleScratch.rhoQ L ≤ 1 ∧
  (s : ℚ) * CompletePublicScheduleScratch.rhoQ L ≤ 1 / 1000 ∧
  (q₂ : ℚ) * CompletePublicScheduleScratch.xQ L ≤ 1 / 10000 ∧
  (s : ℚ) * CompletePublicScheduleScratch.xQ L ≤ 1 / 10000 ∧
  (w : ℚ) * CompletePublicScheduleScratch.xQ L ≤ 1 / 10000 ∧
  (10 * L : ℚ) ≤ (q₂ : ℚ) / 4096 ∧
  ((8 * s * (s - 2) : ℕ) : ℚ) ≤
    SourceRationalScheduleScratch.witnessDensity γ * q₂ / 16 ∧
  (2 : ℚ) * q₂ * CompletePublicScheduleScratch.xQ L ≤ 1 / 8 ∧
  (2 : ℚ) * s * CompletePublicScheduleScratch.xQ L ≤ 1 / 1000 ∧
  4 * tStar Q ≤ w ∧
  (2 : ℚ) * w * CompletePublicScheduleScratch.xQ L +
    η / (16 * CompletePublicScheduleScratch.gQ) < 1 ∧
  (2 : ℚ) * w ^ 2 * CompletePublicScheduleScratch.xQ L ≤
    η / (16 * CompletePublicScheduleScratch.gQ) ∧
  (w : ℚ) ^ 2 * q₂ * CompletePublicScheduleScratch.xQ L ≤ 1 ∧
  (4 : ℚ) * CompletePublicScheduleScratch.muQ * w * q₂ *
    CompletePublicScheduleScratch.xQ L ≤ η / 32 ∧
  (4 : ℚ) * CompletePublicScheduleScratch.muQ * w / q₂ ≤ η / 32 ∧
  quarterCheck27Prop w Q η ∧
  kCheck27Prop L (4 * ell L) w Q η ∧
  RandomizedSchedule.overhead27 (V := V) (E := Edges) L Δ γ ≤ 7 * L ∧
  16 ≤ L ∧
  LookupSeed.exponent L + 1 ≤ L

def allCutoff27 (Δ : ℕ) (γ : ℚ) : ℕ :=
  max (cutoff27 Δ γ) (CompletePublicScheduleScratch.cutoff Δ γ)

theorem overhead27_le_two_L (edge : Edges → Bool → V)
    (L Δ : ℕ) (γ : ℚ)
    (hL : ParameterCutoff.overheadCutoff Δ γ ≤ L)
    (hγ : 0 < γ) (hΔ : 0 < Δ)
    (hincident : ∀ v, ∃ e b, edge e b = v)
    (hdegree : ∀ v, SourceItems.degree edge v ≤ Δ) :
    RandomizedSchedule.overhead27 (V := V) (E := Edges) L Δ γ ≤ 2 * L := by
  have hL1 : 1 ≤ L := by
    have hp : 0 < ParameterCutoff.overheadCutoff Δ γ := by
      unfold ParameterCutoff.overheadCutoff LogSquareCutoff.cutoff
      positivity
    omega
  have hpoly := LogSquareCutoff.quadratic_log_le 2 6
    (64 + SourceOverheadBounds.coefficientExponent Δ γ) L hL
  have h16pow : 2 ^ 16 ≤ L + 1 := by
    have hc : 16 ≤ 2 + 6 + (64 + SourceOverheadBounds.coefficientExponent Δ γ) + 16 := by omega
    have hp := Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) hc
    unfold ParameterCutoff.overheadCutoff LogSquareCutoff.cutoff at hL
    omega
  have he16 : 16 ≤ ell L := by
    have hc := Nat.clog_mono_right 2 h16pow
    simpa only [ell, Nat.clog_pow 2 16 (by decide)] using hc
  have hquad_gen (e : ℕ) (he : 4 ≤ e) : 14 * e ≤ 2 * e ^ 2 + 6 * e := by
    nlinarith only [he, Nat.zero_le e]
  have hquad : 14 * ell L ≤ 2 * (ell L) ^ 2 + 6 * ell L := by
    exact hquad_gen _ (by omega)
  have hb := (RandomizedSchedule.overhead27_bounds (V := V) (E := Edges)
    edge L Δ γ hL1 hγ hΔ hincident hdegree).2
  have hc : RandomizedSchedule.coefficientExponent27 Δ γ =
      SourceOverheadBounds.coefficientExponent Δ γ := rfl
  rw [hc] at hb
  omega

theorem all_large_checks27 (edge : Edges → Bool → V)
    (L Δ : ℕ) (γ : ℚ)
    (hL : allCutoff27 Δ γ ≤ L)
    (hγ : 0 < γ) (hΔ : 0 < Δ)
    (hincident : ∀ v, ∃ e b, edge e b = v)
    (hdegree : ∀ v, SourceItems.degree edge v ≤ Δ)
    (hsize : Fintype.card V ≤ 2 ^ L) :
    Checks27 (V := V) (Edges := Edges) L Δ γ := by
  have hcore : cutoff27 Δ γ ≤ L := (le_max_left _ _).trans hL
  have hOldCut : CompletePublicScheduleScratch.cutoff Δ γ ≤ L :=
    (le_max_right _ _).trans hL
  have he : 4 ≤ ell L := by
    have hh := cutoff_ell L Δ γ hcore
    have h20 : 20 ≤ cutoffExponent27 Δ γ := le_max_left _ _
    omega
  have hW := width27_le_old L he
  have hWq : (RandomizedSchedule.width27 L : ℚ) ≤
      RestorationWidthScheduleScratch.width L := by exact_mod_cast hW
  have hallowCut : AllowanceSmallnessScratch.cutoff Δ γ ≤ L := by
    simp only [CompletePublicScheduleScratch.cutoff, max_le_iff] at hOldCut
    exact hOldCut.2.2.2.2.2.2
  have hoverCut : ParameterCutoff.overheadCutoff Δ γ ≤ L := by
    simp only [CompletePublicScheduleScratch.cutoff, max_le_iff] at hOldCut
    exact hOldCut.2.2.2.2.2.1
  have hOld := CompletePublicScheduleScratch.all_large_checks (V := V) (E := Edges)
    edge L Δ γ hOldCut hγ hΔ hincident hdegree hsize
  dsimp only [CompletePublicScheduleScratch.Checks] at hOld
  rcases hOld with ⟨hcoord, hitem, hscale, hinner, houter, href, hrest,
    hdensity, hwitness, htwoouter, htworef, _, _, _, hscaleOld, _, _,
    _, _, _, h16, hseed⟩
  have hallow := allowance27_checks edge L Δ γ hallowCut he hγ hΔ hincident hdegree
  dsimp only at hallow
  have hxq : 0 ≤ CompletePublicScheduleScratch.xQ L := by
    unfold CompletePublicScheduleScratch.xQ
    positivity
  have hq2 : (0 : ℚ) ≤ outerWidth L := by exact_mod_cast Nat.zero_le (outerWidth L)
  have hrestNew : (RandomizedSchedule.width27 L : ℚ) *
      CompletePublicScheduleScratch.xQ L ≤ 1 / 10000 := by
    exact (mul_le_mul_of_nonneg_right hWq hxq).trans hrest
  have hWsq : (RandomizedSchedule.width27 L : ℚ) ^ 2 ≤
      (RestorationWidthScheduleScratch.width L : ℚ) ^ 2 :=
    pow_le_pow_left₀ (by exact_mod_cast Nat.zero_le (RandomizedSchedule.width27 L)) hWq _
  have hscaleNew : (RandomizedSchedule.width27 L : ℚ) ^ 2 * outerWidth L *
      CompletePublicScheduleScratch.xQ L ≤ 1 := by
    have hm : (RandomizedSchedule.width27 L : ℚ) ^ 2 *
        ((outerWidth L : ℚ) * CompletePublicScheduleScratch.xQ L) ≤
        (RestorationWidthScheduleScratch.width L : ℚ) ^ 2 *
          ((outerWidth L : ℚ) * CompletePublicScheduleScratch.xQ L) :=
      mul_le_mul_of_nonneg_right hWsq (mul_nonneg hq2 hxq)
    have hh : (RandomizedSchedule.width27 L : ℚ) ^ 2 * outerWidth L *
        CompletePublicScheduleScratch.xQ L ≤
        (RestorationWidthScheduleScratch.width L : ℚ) ^ 2 * outerWidth L *
          CompletePublicScheduleScratch.xQ L := by
      calc
        _ = (RandomizedSchedule.width27 L : ℚ) ^ 2 *
            ((outerWidth L : ℚ) * CompletePublicScheduleScratch.xQ L) := by ring
        _ ≤ _ := hm
        _ = _ := by ring
    exact hh.trans hscaleOld
  have ha1 : (2 : ℚ) * RandomizedSchedule.width27 L *
      CompletePublicScheduleScratch.xQ L +
      SourceRationalScheduleScratch.eta (V := V) (E := Edges) L γ Δ /
        (16 * CompletePublicScheduleScratch.gQ) < 1 := by
    apply (Rat.cast_lt (K := ℝ)).mp
    norm_num only [Rat.cast_add, Rat.cast_mul, Rat.cast_natCast,
      Rat.cast_div, Rat.cast_ofNat, CompletePublicScheduleScratch.xQ_cast,
      CompletePublicScheduleScratch.gQ]
    simpa only [show (16 : ℝ) * (127 / 128) = 127 / 8 by norm_num]
      using hallow.1
  have ha2 : (2 : ℚ) * RandomizedSchedule.width27 L ^ 2 *
      CompletePublicScheduleScratch.xQ L ≤
      SourceRationalScheduleScratch.eta (V := V) (E := Edges) L γ Δ /
        (16 * CompletePublicScheduleScratch.gQ) := by
    apply (Rat.cast_le (K := ℝ)).mp
    norm_num only [Rat.cast_mul, Rat.cast_pow, Rat.cast_natCast,
      Rat.cast_div, Rat.cast_ofNat, CompletePublicScheduleScratch.xQ_cast,
      CompletePublicScheduleScratch.gQ]
    simpa only [show (16 : ℝ) * (127 / 128) = 127 / 8 by norm_num]
      using hallow.2.1
  have ha3 : (4 : ℚ) * CompletePublicScheduleScratch.muQ *
      RandomizedSchedule.width27 L * outerWidth L *
      CompletePublicScheduleScratch.xQ L ≤
      SourceRationalScheduleScratch.eta (V := V) (E := Edges) L γ Δ / 32 := by
    apply (Rat.cast_le (K := ℝ)).mp
    norm_num only [Rat.cast_mul, Rat.cast_natCast,
      Rat.cast_div, Rat.cast_ofNat, CompletePublicScheduleScratch.xQ_cast,
      CompletePublicScheduleScratch.muQ]
    simpa only [show (4 : ℝ) * (1 / 256) = 1 / 64 by norm_num]
      using hallow.2.2.1
  have ha4 : (4 : ℚ) * CompletePublicScheduleScratch.muQ *
      RandomizedSchedule.width27 L / outerWidth L ≤
      SourceRationalScheduleScratch.eta (V := V) (E := Edges) L γ Δ / 32 := by
    apply (Rat.cast_le (K := ℝ)).mp
    norm_num only [Rat.cast_mul, Rat.cast_natCast,
      Rat.cast_div, Rat.cast_ofNat, CompletePublicScheduleScratch.muQ]
    simpa only [show (4 : ℝ) * (1 / 256) = 1 / 64 by norm_num]
      using hallow.2.2.2
  dsimp only [Checks27]
  refine ⟨hcoord, hitem, hscale, hinner, houter, href, hrestNew,
    hdensity, hwitness, htwoouter, htworef, ?_, ha1, ha2, hscaleNew,
    ha3, ha4, ?_, ?_, ?_, h16, hseed⟩
  · exact tStar27_quarter edge L Δ γ hcore hγ hΔ hincident hdegree
  · exact quarterCheck27 edge L Δ γ hcore hγ hΔ hincident hdegree
  · exact kCheck27 edge L Δ γ hcore hγ hΔ hincident hdegree
  · have hh := overhead27_le_two_L edge L Δ γ hoverCut hγ hΔ hincident hdegree
    omega

#print axioms exceptional27_bound
#print axioms kCheck27
#print axioms quarterCheck27
#print axioms tStar27_quarter
#print axioms allowance27_checks
#print axioms all_large_checks27

end CurrentAdditive.QuarticSchedule
