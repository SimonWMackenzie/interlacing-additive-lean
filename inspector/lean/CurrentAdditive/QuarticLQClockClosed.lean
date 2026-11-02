import CurrentAdditive.QuarticCopyBound

/-! The complete fixed quartic L/Q front has a graph-polynomial clock. -/

set_option maxHeartbeats 4000000
set_option maxRecDepth 16384

namespace Paper2.CurrentAdditive.QuarticLQClockClosed

open CurrentAdditive.RandomizedSchedule
open Paper2.CurrentAdditive.QuarticNumericFront

noncomputable def coefficient (Δ : ℕ) (γ : ℚ) : ℕ :=
  SeedT45.SeedClock.seedC +
    8 * (2 + 65536 + 100) + 15 + QuarticQClockBound.coefficient Δ γ ^ 21

theorem lq_clock_poly27 (Δ n m : ℕ) (γ : ℚ) (hm : m ≤ Δ * n) :
    LQ27.clock n m Δ γ ≤ coefficient Δ γ * (n + 2) ^ 336 := by
  let N := n + 2
  let X := N ^ 336
  let D := 2 + 65536 + 100
  let Q := QuarticQClockBound.coefficient Δ γ ^ 21
  have hN : 1 ≤ N := by dsimp [N]; omega
  have hPow : N ^ 16 ≤ X := by
    dsimp [X]
    exact Nat.pow_le_pow_right hN (by omega)
  have hSeed : WidthFromN.clock n ≤ SeedT45.SeedClock.seedC * X :=
    (WidthFromN.clock_poly n).trans (by
      simpa only [N] using (Nat.mul_le_mul_left SeedT45.SeedClock.seedC hPow))
  have hCopy : LQ27.copyBound n ≤ D * X :=
    (QuarticCopyBound.copyBound_poly27 n).trans (by
      simpa only [N, D] using (Nat.mul_le_mul_left D hPow))
  have hQ : QProducer.qBd γ.num.toNat γ.den Δ n m (Nat.clog 2 n)
      (SourceProfileParameters.width (Nat.clog 2 n))
      (width27 (Nat.clog 2 n)) ≤ Q * X := by
    simpa only [N, X, Q] using QuarticQClockBound.qBd_poly27 Δ n m γ hm
  have hOne : 1 ≤ X := by dsimp [X]; exact Nat.one_le_pow _ _ hN
  have hCopy8 : 8 * LQ27.copyBound n ≤ 8 * (D * X) :=
    Nat.mul_le_mul_left _ hCopy
  have h15 : 15 ≤ 15 * X := Nat.le_mul_of_pos_right _ hOne
  have hClockEq : LQ27.clock n m Δ γ =
      WidthFromN.clock n + 8 * LQ27.copyBound n + 15 +
        QProducer.qBd γ.num.toNat γ.den Δ n m (Nat.clog 2 n)
          (SourceProfileParameters.width (Nat.clog 2 n))
          (width27 (Nat.clog 2 n)) := by
    unfold LQ27.clock
    omega
  rw [hClockEq]
  calc
    WidthFromN.clock n + 8 * LQ27.copyBound n + 15 +
        QProducer.qBd γ.num.toNat γ.den Δ n m (Nat.clog 2 n)
          (SourceProfileParameters.width (Nat.clog 2 n))
          (width27 (Nat.clog 2 n)) ≤
      SeedT45.SeedClock.seedC * X + 8 * (D * X) + 15 * X + Q * X :=
        Nat.add_le_add (Nat.add_le_add (Nat.add_le_add hSeed hCopy8) h15) hQ
    _ = coefficient Δ γ * (n + 2) ^ 336 := by
      change SeedT45.SeedClock.seedC * X + 8 * (D * X) + 15 * X + Q * X =
        (SeedT45.SeedClock.seedC + 8 * D + 15 + Q) * X
      simp only [add_mul, mul_assoc]

#print axioms lq_clock_poly27

end Paper2.CurrentAdditive.QuarticLQClockClosed
