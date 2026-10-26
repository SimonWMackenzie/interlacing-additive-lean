import Paper2.FrontClockC

/-! Unit 3, lane a-success-table-13, segment (3), part D: the whole `fullBd` from atom bounds. Pure arithmetic. -/

set_option maxHeartbeats 16000000
set_option maxRecDepth 100000

namespace Paper2.FrontClock13

open EthInapproximability.CurrentPaper
open Paper2.FullFront (pV sV q2V wV q1V QV Lg eg Zv mXV mYV LB LC fullBd gBd)

theorem zv_le (bb k V : ℕ) (hV : 2 ^ 32 ≤ V) (hB : 2 ^ (bb - 1) ≤ V) (hP : 2 ^ (k + bb - 1) ≤ V) :
    Zv bb k ≤ 2 * V ^ 4 := by
  have hV1 : 1 ≤ V := by omega
  unfold Zv
  generalize 2 ^ (bb - 1) = B at *
  generalize 2 ^ (k + bb - 1) = P at *
  have hBB : B * (B + 1) ≤ 2 * V ^ 2 := by
    have := Nat.mul_le_mul hB (show B + 1 ≤ 2 * V by omega)
    calc _ ≤ V * (2 * V) := this
      _ = 2 * V ^ 2 := by ring
  have p23 : 4 * V ^ 2 ≤ V ^ 3 := cV (by omega)
  have h2BB : 2 + B * (B + 1) ≤ V ^ 3 := by
    have : 1 ≤ V ^ 2 := one_le_pw hV1
    omega
  have hZP : (2 + B * (B + 1)) * P ≤ V ^ 4 := mulb h2BB (pow1 hP)
  have : V ≤ V ^ 4 := by have := pw (i := 1) (j := 4) hV1 (by omega); simpa using this
  omega

theorem arith_full (E G T k p s q2 w Q L q1 n MX Y W Z V : ℕ) (hV : 2 ^ 32 ≤ V) (hE : E + 1 ≤ V)
    (hG : G ≤ V ^ 44) (hT : T ≤ V ^ 8) (hk : k ≤ V) (hp : p ≤ V) (hs : s ≤ V) (hq2 : q2 ≤ V) (hw : w ≤ V)
    (hQ : Q ≤ V) (hL : L ≤ V) (hq1 : q1 ≤ V) (hn : n ≤ V) (hZ : Z ≤ 2 * V ^ 4) (hMX : MX ≤ L + Z)
    (hY : Y = Z + Z) (hW : W ≤ V) :
    (2 * E + 2) + G + 1 + (7 * (2 * (k + p + s + q2 + w + Q + L) + 3) + 1) + T +
      (11 * (2 * (q2 + q1 + s + n + w + Q + p + k + MX + Y + W) + 3) + 1) + 3 ≤ V ^ 45 := by
  have hV1 : 1 ≤ V := by omega
  have p14 : V ≤ V ^ 4 := by have := pw (i := 1) (j := 4) hV1 (by omega); simpa using this
  have p444 : V ^ 4 ≤ V ^ 44 := pw hV1 (by omega)
  have p844 : V ^ 8 ≤ V ^ 44 := pw hV1 (by omega)
  have c45 : 1000 * V ^ 44 ≤ V ^ 45 := cV (by omega)
  have one4 : 1 ≤ V ^ 4 := one_le_pw hV1
  subst hY
  omega

end Paper2.FrontClock13

#print axioms Paper2.FrontClock13.zv_le
#print axioms Paper2.FrontClock13.arith_full
