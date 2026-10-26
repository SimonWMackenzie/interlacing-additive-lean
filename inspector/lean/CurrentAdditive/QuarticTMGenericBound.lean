import CurrentAdditive.QuarticTMThresholdBound

set_option maxHeartbeats 16000000
set_option maxRecDepth 16384

namespace Paper2.CurrentAdditive.QuarticTMClockRepair

open EthInapproximability.CurrentPaper

theorem tmBd_generic (k L V0 : ℕ) (vv : Fin 5 → ℕ)
    (hV02 : 2 ≤ V0) (hV032 : 2 ^ 32 ≤ V0)
    (hc0 : UnaryBinaryEncoding.coefficient + 6 ≤ V0)
    (hv0 : ∀ i, vv i ≤ V0) (hL0 : L ≤ V0)
    (hThr : 2 ^ TMFront.thrVal k vv ≤ V0 ^ (220 * k + 45)) :
    TMFront.tmBd k vv L ≤ (V0 ^ (266 * (k + 1))) ^ 8 := by
  let V := V0 ^ (266 * (k + 1))
  have hV01 : 1 ≤ V0 := by omega
  have hV0V : V0 ≤ V := by
    have h := Nat.pow_le_pow_right hV01
      (show 1 ≤ 266 * (k + 1) by omega)
    simpa only [pow_one, V] using h
  have hV32 : 2 ^ 32 ≤ V := hV032.trans hV0V
  have hc : UnaryBinaryEncoding.coefficient + 6 ≤ V := hc0.trans hV0V
  have hv : ∀ i, vv i ≤ V := fun i => (hv0 i).trans hV0V
  have hk : k ≤ V := by
    have h2k : k ≤ 2 ^ k := (Nat.lt_two_pow_self).le
    have hpow : 2 ^ k ≤ V0 ^ k := Nat.pow_le_pow_left hV02 k
    have hhigh : V0 ^ k ≤ V := by
      dsimp [V]
      exact Nat.pow_le_pow_right hV01 (by omega)
    omega
  have hL : L ≤ V := hL0.trans hV0V
  have hHigh : V0 ^ (220 * k + 45) ≤ V := by
    dsimp [V]
    exact Nat.pow_le_pow_right hV01 (by omega)
  have hThrV : 2 ^ TMFront.thrVal k vv ≤ V := hThr.trans hHigh
  have hB : 2 ^ (TMFront.thrVal k vv - 1) ≤ V :=
    (Nat.pow_le_pow_right (by norm_num) (Nat.sub_le _ _)).trans hThrV
  have hP : 2 ^ (k + TMFront.thrVal k vv - 1) ≤ V := by
    have h1 : 2 ^ (k + TMFront.thrVal k vv - 1) ≤
        2 ^ k * 2 ^ TMFront.thrVal k vv := by
      rw [← pow_add]
      exact Nat.pow_le_pow_right (by norm_num) (Nat.sub_le _ _)
    have h2 := Nat.mul_le_mul (Nat.pow_le_pow_left hV02 k) hThr
    have h3 : V0 ^ k * V0 ^ (220 * k + 45) = V0 ^ (221 * k + 45) := by
      rw [← pow_add]
      congr 1
      omega
    rw [h3] at h2
    have h4 : V0 ^ (221 * k + 45) ≤ V := by
      dsimp [V]
      exact Nat.pow_le_pow_right hV01 (by omega)
    exact h1.trans (h2.trans h4)
  exact Paper2.FrontClock13.tmBd_le k vv L V hV32 hc hv hk hL
    ((Nat.lt_two_pow_self).le.trans hThrV) hB hP

#print axioms tmBd_generic

end Paper2.CurrentAdditive.QuarticTMClockRepair
