import CurrentAdditive.V39ScalarProgram
import CurrentAdditive.V39SourceFieldWidths

noncomputable section
namespace CurrentAdditive.V39ScalarSetup

open Turing EthInapproximability.CurrentPaper
open CurrentAdditive.FiniteFieldConstructor
open CurrentAdditive.FiniteFieldConstructor.CanonicalAmbient
open CurrentAdditive.V39SourceOutputSize CurrentAdditive.V39SourceFieldWidths
open CurrentAdditive.V38Encoded CurrentAdditive.V38Clock CurrentAdditive.SmallBias
open Paper2.YaoSourceCodec Paper2.YaoMachine

set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

def scalarMagnitude (t v b H d : ℕ) : ℕ :=
  v + b + H + d + H ^ (2 ^ (t - 1)) + (2 ^ d) ^ 2 + 1

theorem scalarBudget_le_magnitude (t v b H d : ℕ) :
    scalarBudget t v b H d ≤
      (1024 * (2 ^ (t - 1) + t + 1)) * scalarMagnitude t v b H d ^ 2 := by
  let A := scalarMagnitude t v b H d
  have hA : 1 ≤ A := by dsimp [A, scalarMagnitude]; omega
  have hv : v ≤ A := by dsimp [A, scalarMagnitude]; omega
  have hb : b ≤ A := by dsimp [A, scalarMagnitude]; omega
  have hH : H ≤ A := by dsimp [A, scalarMagnitude]; omega
  have hd : d ≤ A := by dsimp [A, scalarMagnitude]; omega
  have hcap : H ^ (2 ^ (t - 1)) ≤ A := by dsimp [A, scalarMagnitude]; omega
  have hR : (2 ^ d) ^ 2 ≤ A := by dsimp [A, scalarMagnitude]; omega
  have hA2 : 1 ≤ A ^ 2 := Nat.one_le_pow _ _ hA
  have hAA : A ≤ A ^ 2 := Nat.le_self_pow (by decide) A
  have hsel : MatrixWeightedPower.powerBound H (2 ^ (t - 1)) ≤
      32 * (2 ^ (t - 1) + 1) * A ^ 2 := by
    calc
      _ ≤ (2 ^ (t - 1) + 1) *
          (3 * (H ^ (2 ^ (t - 1)) + 1) * H +
            5 * (H ^ (2 ^ (t - 1)) + 1) + 7) :=
        MatrixWeightedPower.powerBound_polynomial _ _
      _ ≤ (2 ^ (t - 1) + 1) * (3 * (A + 1) * A + 5 * (A + 1) + 7) := by gcongr
      _ ≤ (2 ^ (t - 1) + 1) * (32 * A ^ 2) :=
        Nat.mul_le_mul_left _ (by nlinarith)
      _ = _ := by ring
  have hsq : MatrixWeightedPower.powerBound 4 d ≤ 100 * A ^ 2 := by
    have h := MatrixWeightedPower.powerBound_polynomial 4 d
    rw [CanonicalFieldSquare.four_pow_eq_field_square] at h
    calc
      _ ≤ (d + 1) * (3 * ((2 ^ d) ^ 2 + 1) * 4 +
          5 * ((2 ^ d) ^ 2 + 1) + 7) := h
      _ ≤ (A + 1) * (3 * (A + 1) * 4 + 5 * (A + 1) + 7) := by gcongr
      _ ≤ _ := by nlinarith
  have hvcap : v * H ^ (2 ^ (t - 1)) ≤ A ^ 2 := by
    simpa [pow_two] using Nat.mul_le_mul hv hcap
  have hHR : H * (2 ^ d) ^ 2 ≤ A ^ 2 := by
    simpa [pow_two] using Nat.mul_le_mul hH hR
  have hqHR := Nat.mul_le_mul_left (2 ^ (t - 1)) hHR
  have hqH := Nat.mul_le_mul_left (2 ^ (t - 1)) (hH.trans hAA)
  have hq := Nat.mul_le_mul_left (2 ^ (t - 1)) hA2
  have ht := Nat.mul_le_mul_left t hA2
  unfold scalarBudget selectorBudget squareBudget dimensionsBudget dimensionCopyBudget
    thresholdBudget MatrixAddressMachine.exactTime
  change _ ≤ (1024 * (2 ^ (t - 1) + t + 1)) * A ^ 2
  generalize 2 ^ (t - 1) = q at *
  generalize H ^ q = cap at *
  generalize (2 ^ d) ^ 2 = R2 at *
  generalize MatrixWeightedPower.powerBound H q = ps at *
  generalize MatrixWeightedPower.powerBound 4 d = pq at *
  nlinarith

def magnitudeCoefficient (t : ℕ) : ℕ :=
  7 + 2 ^ (14 * t) * 2 ^ 5 + 2 ^ (2 ^ (t - 1)) +
    (2 ^ (14 * t)) ^ 2 * 2 ^ 10
def magnitudeDegree (t : ℕ) : ℕ := 2 ^ (t - 1) + 10
def scalarClockCoefficient (t : ℕ) : ℕ :=
  (1024 * (2 ^ (t - 1) + t + 1)) * magnitudeCoefficient t ^ 2
def scalarClockDegree (t : ℕ) : ℕ := magnitudeDegree t * 2

theorem source_magnitude_bound {t : ℕ} (src : YaoSource t) :
    scalarMagnitude t src.1 (edgeBits src.2.1) (2 ^ edgeBits src.2.1)
        (v38FieldDegree (edgeBits src.2.1) t) ≤
      magnitudeCoefficient t * ((encode src).length + 1) ^ magnitudeDegree t := by
  let N := (encode src).length + 1
  have hN : 1 ≤ N := by dsimp [N]; omega
  have hv : src.1 ≤ N := by have h := source_headers_le src; dsimp [N]; omega
  have hH : 2 ^ edgeBits src.2.1 ≤ 2 * N := source_capacity_le src
  have hb : edgeBits src.2.1 ≤ 2 * N := (Nat.lt_two_pow_self).le.trans hH
  have hd : v38FieldDegree (edgeBits src.2.1) t ≤
      (2 ^ (14 * t) * 2 ^ 5) * N ^ 5 := by
    calc
      _ ≤ 2 ^ v38FieldDegree (edgeBits src.2.1) t := (Nat.lt_two_pow_self).le
      _ = 2 ^ (14 * t) * (2 ^ edgeBits src.2.1) ^ 5 := by
        rw [field_order_exact, target_fixed_t]
      _ ≤ 2 ^ (14 * t) * (2 * N) ^ 5 :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hH _)
      _ = _ := by rw [mul_pow]; ring
  have hcap : (2 ^ edgeBits src.2.1) ^ (2 ^ (t - 1)) ≤
      2 ^ (2 ^ (t - 1)) * N ^ (2 ^ (t - 1)) := by
    simpa only [mul_pow] using Nat.pow_le_pow_left hH (2 ^ (t - 1))
  have hR := field_label_count_le src
  change (2 ^ v38FieldDegree (edgeBits src.2.1) t) ^ 2 ≤
    ((2 ^ (14 * t)) ^ 2 * 2 ^ 10) * N ^ 10 at hR
  have hlin : N ≤ N ^ magnitudeDegree t :=
    Nat.le_self_pow (Nat.ne_of_gt (lt_of_lt_of_le
      (by decide : 0 < 10) (Nat.le_add_left 10 _))) _
  have h5 : N ^ 5 ≤ N ^ magnitudeDegree t :=
    Nat.pow_le_pow_right hN ((by decide : 5 ≤ 10).trans (Nat.le_add_left 10 _))
  have hq : N ^ (2 ^ (t - 1)) ≤ N ^ magnitudeDegree t :=
    Nat.pow_le_pow_right hN (Nat.le_add_right _ 10)
  have h10 : N ^ 10 ≤ N ^ magnitudeDegree t :=
    Nat.pow_le_pow_right hN (Nat.le_add_left 10 _)
  have hv' := hv.trans hlin
  have hb' := hb.trans (Nat.mul_le_mul_left 2 hlin)
  have hH' := hH.trans (Nat.mul_le_mul_left 2 hlin)
  have hd' := hd.trans (Nat.mul_le_mul_left _ h5)
  have hcap' := hcap.trans (Nat.mul_le_mul_left _ hq)
  have hR' := hR.trans (Nat.mul_le_mul_left _ h10)
  have hpos : 1 ≤ N ^ magnitudeDegree t := Nat.one_le_pow _ _ hN
  unfold scalarMagnitude magnitudeCoefficient
  change _ ≤ _ * N ^ magnitudeDegree t
  nlinarith

theorem scalarBudget_source_bound {t : ℕ} (src : YaoSource t) :
    scalarBudget t src.1 (edgeBits src.2.1) (2 ^ edgeBits src.2.1)
        (v38FieldDegree (edgeBits src.2.1) t) ≤
      scalarClockCoefficient t * ((encode src).length + 1) ^ scalarClockDegree t := by
  calc
    _ ≤ (1024 * (2 ^ (t - 1) + t + 1)) *
        scalarMagnitude t src.1 (edgeBits src.2.1) (2 ^ edgeBits src.2.1)
          (v38FieldDegree (edgeBits src.2.1) t) ^ 2 := scalarBudget_le_magnitude _ _ _ _ _
    _ ≤ (1024 * (2 ^ (t - 1) + t + 1)) *
        (magnitudeCoefficient t * ((encode src).length + 1) ^ magnitudeDegree t) ^ 2 :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (source_magnitude_bound src) _)
    _ = _ := by
      unfold scalarClockCoefficient scalarClockDegree
      rw [mul_pow, ← pow_mul]
      ring

/-- Source-code bound for the separate field team's *complete* installation
budget. The coefficient 108 includes unary preparation; the earlier 88
partial bound is deliberately not used in a source/renderer aggregate. -/
theorem complete_install_budget_source_bound {t : ℕ} (src : YaoSource t) :
    108 * v38FieldTarget (edgeBits src.2.1) t ^ 5 ≤
      ((108 * (2 ^ (14 * t)) ^ 5) * 2 ^ 25) *
        ((encode src).length + 1) ^ 25 := by
  calc
    _ = (108 * (2 ^ (14 * t)) ^ 5) * (2 ^ edgeBits src.2.1) ^ 25 := by
      rw [target_fixed_t]
      ring
    _ ≤ (108 * (2 ^ (14 * t)) ^ 5) *
        (2 * ((encode src).length + 1)) ^ 25 :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (source_capacity_le src) _)
    _ = _ := by rw [mul_pow]; ring

#print axioms scalarBudget_le_magnitude
#print axioms source_magnitude_bound
#print axioms scalarBudget_source_bound
#print axioms complete_install_budget_source_bound

end CurrentAdditive.V39ScalarSetup
