import CurrentAdditive.RoundedCleanDraw

namespace EthInapproximability.CurrentPaper.RoundedCleanClock

noncomputable section

def coefficient : ℕ := 111 + RoundedCleanDraw.clearCount *
  (3 + 109 * RoundedCleanDraw.pushConstant)

theorem clock_quadratic (source word : List Bool) :
    RoundedCleanDraw.clock source word ≤ coefficient *
      (source.length + word.length + EncodedCommunication.bitsValue source + 2) ^ 2 := by
  let Q := source.length + word.length + EncodedCommunication.bitsValue source + 2
  have hQ : 1 ≤ Q := by dsimp [Q]; omega
  have hQQ : Q ≤ Q ^ 2 := Nat.le_self_pow (by norm_num) Q
  have h1 : source.length + word.length + 2 ≤ Q := by dsimp [Q]; omega
  have h1sq : (source.length + word.length + 2) ^ 2 ≤ Q ^ 2 := by gcongr
  have ha : EncodedCommunication.bitsValue source + 1 ≤ Q := by dsimp [Q]; omega
  have hb : 4 * (source.length + 2 * word.length) + 5 ≤ 8 * Q := by dsimp [Q]; omega
  have hprod := Nat.mul_le_mul ha hb
  have hdraw : RoundedCleanDraw.drawClock source word ≤ 109 * Q ^ 2 := by
    unfold RoundedCleanDraw.drawClock
    nlinarith
  have hbase : source.length + word.length + EncodedCommunication.bitsValue source + 1 ≤
      2 * Q ^ 2 := by dsimp [Q] at hQQ ⊢; omega
  have hclean := Nat.mul_le_mul_left RoundedCleanDraw.clearCount
    (Nat.add_le_add hbase (Nat.mul_le_mul_left RoundedCleanDraw.pushConstant hdraw))
  have hC := Nat.mul_le_mul_left RoundedCleanDraw.clearCount (hQ.trans hQQ)
  have htwo := Nat.mul_le_mul_left 2 (hQ.trans hQQ)
  change RoundedCleanDraw.drawClock source word +
    RoundedCleanDraw.clearCount *
      (source.length + word.length + EncodedCommunication.bitsValue source + 1 +
        RoundedCleanDraw.pushConstant * RoundedCleanDraw.drawClock source word) +
        RoundedCleanDraw.clearCount + 2 ≤ coefficient * Q ^ 2
  calc
    _ ≤ 109 * Q ^ 2 + RoundedCleanDraw.clearCount *
        (2 * Q ^ 2 + RoundedCleanDraw.pushConstant * (109 * Q ^ 2)) +
        RoundedCleanDraw.clearCount * Q ^ 2 + 2 * Q ^ 2 := by omega
    _ = coefficient * Q ^ 2 := by unfold coefficient; ring

theorem clock_length (source word other : List Bool) (h : word.length = other.length) :
    RoundedCleanDraw.clock source word = RoundedCleanDraw.clock source other := by
  simp only [RoundedCleanDraw.clock, RoundedCleanDraw.drawClock, h]

end
end EthInapproximability.CurrentPaper.RoundedCleanClock
