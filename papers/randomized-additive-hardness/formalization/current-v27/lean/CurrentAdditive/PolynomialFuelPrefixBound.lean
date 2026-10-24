import CurrentAdditive.PolynomialFuelPrefix
import Mathlib.Tactic

set_option maxHeartbeats 2000000

/-! A uniform polynomial bound for the checked fixed twelfth-power writer. -/

namespace CurrentAdditive.PolynomialFuelPrefixBound

open EthInapproximability.CurrentPaper

theorem rawTime_le (bits : List Bool) :
    PolynomialFuelPrefix.rawTime bits ≤
      1000000 * (bits.length+1)^13 := by
  let n := bits.length
  let q := n+1
  let b := n+2
  have hq : 0 < q := by omega
  have hb : b ≤ 2*q := by omega
  have hq1 : q ≤ q^13 := by
    simpa only [pow_one] using
      (Nat.pow_le_pow_right hq (show 1 ≤ 13 by omega))
  have hq12 : q^12 ≤ q^13 :=
    Nat.pow_le_pow_right hq (show 12 ≤ 13 by omega)
  have hb12 : b^12 ≤ 4096*q^12 := by
    calc
      b^12 ≤ (2*q)^12 := Nat.pow_le_pow_left hb 12
      _ = 4096*q^12 := by ring
  have hb13 : b^13 ≤ 8192*q^13 := by
    calc
      b^13 ≤ (2*q)^13 := Nat.pow_le_pow_left hb 13
      _ = 8192*q^13 := by ring
  have hb12q : b^12 ≤ 4096*q^13 := by
    exact hb12.trans (Nat.mul_le_mul_left 4096 hq12)
  have hbq : b ≤ 2*q^13 := by omega
  have hpower := MatrixWeightedPower.powerBound_polynomial b 12
  have hpower' : MatrixWeightedPower.powerBound b 12 ≤
      13 * (3*b^13 + 3*b + 5*b^12 + 12) := by
    calc
      MatrixWeightedPower.powerBound b 12 ≤
        (12+1) * (3*(b^12+1)*b + 5*(b^12+1)+7) := hpower
      _ = 13 * (3*b^13 + 3*b + 5*b^12 + 12) := by ring
  have hterms : 3*b^13 + 3*b + 5*b^12 + 12 ≤
      45074*q^13 := by
    omega
  have hpower'' : MatrixWeightedPower.powerBound b 12 ≤
      585962*q^13 := by
    calc
      MatrixWeightedPower.powerBound b 12 ≤
        13 * (3*b^13 + 3*b + 5*b^12 + 12) := hpower'
      _ ≤ 13 * (45074*q^13) := Nat.mul_le_mul_left 13 hterms
      _ = 585962*q^13 := by ring
  have hnq : n ≤ q^13 := by omega
  have hone : 1 ≤ q^13 := by omega
  change (3*n+4)+15+MatrixWeightedPower.powerBound b 12+
    (2*n+2*b^12+5) ≤ 1000000*q^13
  omega

#print axioms rawTime_le

end CurrentAdditive.PolynomialFuelPrefixBound
