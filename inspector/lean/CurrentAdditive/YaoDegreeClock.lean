import CurrentAdditive.YaoDegreeMachine
import CurrentAdditive.SmallBiasFieldSize

/-! An explicit polynomial clock in the unary public prelude size H=2^b.
For fixed t, the coefficients below are constants and the degree constructor
uses at most degree four in H. -/

namespace CurrentAdditive.SmallBias.YaoDegreeClock

open YaoDegreeMachine
open EthInapproximability.CurrentPaper

def testCap (t H : ℕ) : ℕ :=
  100 * (2 ^ (2 * t) + 2 ^ t + 3 * t + 3)^2 * (H + 1)^2

def aCap (t H : ℕ) : ℕ := H + 2 * t + 1
def qCap (t H : ℕ) : ℕ := 4 * 2 ^ t * (aCap t H + t)

def setupCap (t H : ℕ) : ℕ :=
  ((2 * H + 2) + ((2 ^ t + 1) * H + 2) + 1) +
  ((2 * H + 2) + (2 * t + 1) + 1) + 1

def polynomial (t H : ℕ) : ℕ :=
  setupCap t H +
    (aCap t H * (aCap t H * (testCap t H + 4) + 1) + 1) + 1 +
    ((3 * aCap t H + 4) + (4 * qCap t H + 5 * aCap t H + 7) + 1) +
    ((2 * qCap t H + 2) + (2 * H + 2) + (3 * t + 3 + 1) + 2) + 2

theorem scan_bound (b t : ℕ) :
    YaoCutScanLoop.scanBound
      (fun j => YaoCutTester.timeBound j t (2 ^ (t + b - 3)))
      (sourcePairDepth b t) ≤
    sourcePairDepth b t * (testCap t (2 ^ b) + 4) := by
  unfold YaoCutScanLoop.scanBound
  calc
    Finset.sum (Finset.range (sourcePairDepth b t))
        (fun j => YaoCutTester.timeBound (j + 1) t (2 ^ (t + b - 3)) + 4) ≤
      Finset.sum (Finset.range (sourcePairDepth b t))
        (fun _ => testCap t (2 ^ b) + 4) := by
          apply Finset.sum_le_sum
          intro j hj
          have hj' : j + 1 ≤ sourcePairDepth b t := by
            have := Finset.mem_range.mp hj
            omega
          have ht := YaoCutTester.timeBound_public b t (j + 1) hj'
          simpa only [testCap] using Nat.add_le_add_right ht 4
    _ = sourcePairDepth b t * (testCap t (2 ^ b) + 4) := by simp

theorem setup_bound (b t : ℕ) :
    YaoDegreeSetupScan.setupBound b t ≤ setupCap t (2 ^ b) := by
  have hb : b ≤ 2 ^ b := Nat.le_of_lt Nat.lt_two_pow_self
  have hp : 2 ^ (t - 3) ≤ 2 ^ t :=
    pow_le_pow_right₀ (by decide : (1 : ℕ) ≤ 2) (by omega)
  have hcoeff : SourceAffineUnary.vertexCoefficient
      (YaoThreshold.coefficient t) ≤ 2 ^ t := by
    rw [YaoThreshold.coefficient_value]
    exact hp
  have hm := Nat.mul_le_mul_right (2 ^ b) (Nat.add_le_add_right hcoeff 1)
  dsimp [YaoDegreeSetupScan.setupBound, YaoThreshold.affineTime,
    YaoDepthFuel.fixedExtra, setupCap]
  omega

theorem a_bound (b t : ℕ) :
    sourcePairDepth b t ≤ aCap t (2 ^ b) := by
  have hb : b ≤ 2 ^ b := Nat.le_of_lt Nat.lt_two_pow_self
  unfold sourcePairDepth aCap
  omega

theorem q_bound (b t : ℕ) (ht : 4 ≤ t) :
    2 ^ sourceSuffixDepth b t ≤ qCap t (2 ^ b) := by
  have hq := source_suffix_size_bound b t ht
  have ha := a_bound b t
  have hin : sourcePairDepth b t + t - 1 ≤ aCap t (2 ^ b) + t := by omega
  have hmul := Nat.mul_le_mul_left (4 * 2 ^ t) hin
  unfold qCap
  omega

theorem timeBound_polynomial (b t : ℕ) (ht : 4 ≤ t) :
    YaoDegreeMachine.timeBound b t ≤ polynomial t (2 ^ b) := by
  let H := 2 ^ b
  let A := aCap t H
  let Q := qCap t H
  let C := testCap t H
  let a := sourcePairDepth b t
  let i := sourceCutIndex b t
  let h := sourceSuffixDepth b t
  have ha : a ≤ A := a_bound b t
  have hi : i ≤ a := Nat.le_of_lt (sourceCutIndex_spec b t ht).2.1
  have hh : h ≤ a := Nat.sub_le _ _
  have hq : 2 ^ h ≤ Q := q_bound b t ht
  have hs : YaoDegreeSetupScan.setupBound b t ≤ setupCap t H := setup_bound b t
  have hscan := scan_bound b t
  have hscanBound : YaoCutPhysical.bound b t ≤
      A * (A * (C + 4) + 1) + 1 := by
    dsimp [YaoCutPhysical.bound]
    calc
      a * (YaoCutScanLoop.scanBound
          (fun j => YaoCutTester.timeBound j t (2 ^ (t + b - 3))) a + 1) + 1 ≤
        a * (a * (C + 4) + 1) + 1 := by
          gcongr
      _ ≤ A * (A * (C + 4) + 1) + 1 := by gcongr
  have hsetup : YaoDegreeSetupScan.totalBound b t ≤
      setupCap t H + (A * (A * (C + 4) + 1) + 1) + 1 := by
    dsimp [YaoDegreeSetupScan.totalBound]
    omega
  change YaoDegreeSetupScan.totalBound b t +
      ((3 * i + 4) + (4 * 2 ^ h + 5 * h + 7) + 1) +
      ((2 * 2 ^ h + 2) + (2 * b + 2) +
        (YaoDegreePrinter.fixedPart t + 1) + 2) + 2 ≤
    setupCap t H + (A * (A * (C + 4) + 1) + 1) + 1 +
      ((3 * A + 4) + (4 * Q + 5 * A + 7) + 1) +
      ((2 * Q + 2) + (2 * H + 2) + (3 * t + 3 + 1) + 2) + 2
  have hb : b ≤ H := Nat.le_of_lt Nat.lt_two_pow_self
  unfold YaoDegreePrinter.fixedPart
  omega

#print axioms timeBound_polynomial

end CurrentAdditive.SmallBias.YaoDegreeClock
