import CurrentAdditive.QuarticQClockBound
import CurrentAdditive.QuarticLQFront

/-! Polynomial clock for the full fixed unary-count-to-quartic-L/Q program. -/

set_option maxHeartbeats 8000000
set_option maxRecDepth 16384

namespace Paper2.CurrentAdditive.QuarticCopyBound

open CurrentAdditive.RandomizedSchedule
open Paper2.CurrentAdditive.QuarticNumericFront

noncomputable def coefficient (Δ : ℕ) (γ : ℚ) : ℕ :=
  SeedT45.SeedClock.seedC +
    8 * (2 + 65536 + 100) + 15 + QuarticQClockBound.coefficient Δ γ ^ 21

theorem copyBound_poly27 (n : ℕ) :
    LQ27.copyBound n ≤ (2 + 65536 + 100) * (n + 2) ^ 16 := by
  let N := n + 2
  let L := Nat.clog 2 n
  let e := RestorationWidthScheduleScratch.ell L
  have hN : 2 ≤ N := by dsimp [N]; omega
  have hN1 : 1 ≤ N := by omega
  have hL : L ≤ n := by
    dsimp [L]
    exact Nat.clog_le_of_le_pow (Nat.lt_two_pow_self).le
  have hN16 : N ≤ N ^ 16 := by
    calc N = N ^ 1 := by simp
      _ ≤ N ^ 16 := Nat.pow_le_pow_right hN1 (by omega)
  have hpow : 2 ^ e ≤ (L + 3) ^ 2 := by
    simpa [e, RestorationWidthScheduleScratch.ell] using
      (Paper2.A3Assembly.Clock.two_pow_clog_le (L + 1))
  have hL3 : L + 3 ≤ 2 * N := by dsimp [N]; omega
  have h2N : 2 * N ≤ N ^ 2 := by nlinarith
  have h2e : 2 ^ e ≤ N ^ 4 := calc
    2 ^ e ≤ (L + 3) ^ 2 := hpow
    _ ≤ (2 * N) ^ 2 := Nat.pow_le_pow_left hL3 2
    _ ≤ (N ^ 2) ^ 2 := Nat.pow_le_pow_left h2N 2
    _ = N ^ 4 := by ring
  have hs4 : SourceProfileParameters.width L ≤ 65536 * N ^ 4 := by
    rw [Paper2.LProducer.s_eq, pow_add]
    change 65536 * 2 ^ e ≤ 65536 * N ^ 4
    exact Nat.mul_le_mul_left 65536 h2e
  have hN4 : N ^ 4 ≤ N ^ 16 := Nat.pow_le_pow_right hN1 (by omega)
  have hs : SourceProfileParameters.width L ≤ 65536 * N ^ 16 :=
    hs4.trans (Nat.mul_le_mul_left _ hN4)
  have hwClock := QuarticNumericFront.width_clock_poly n
  have hw0 : width27 L ≤ WidthMachine.clock e := by
    dsimp [width27, WidthMachine.clock, e]
    omega
  have hw : width27 L ≤ 100 * N ^ 16 :=
    hw0.trans (by simpa [N, L, e] using hwClock)
  have hn : n ≤ N ^ 16 := by omega
  have hL' : L ≤ N ^ 16 := hL.trans hn
  change n + L + SourceProfileParameters.width L + width27 L ≤
    (2 + 65536 + 100) * N ^ 16
  calc
    n + L + SourceProfileParameters.width L + width27 L ≤
        N ^ 16 + N ^ 16 + 65536 * N ^ 16 + 100 * N ^ 16 := by omega
    _ = (2 + 65536 + 100) * N ^ 16 := by ring
#print axioms copyBound_poly27

end Paper2.CurrentAdditive.QuarticCopyBound
