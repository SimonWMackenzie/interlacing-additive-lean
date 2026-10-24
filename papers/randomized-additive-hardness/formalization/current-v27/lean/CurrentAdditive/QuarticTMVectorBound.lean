import CurrentAdditive.QuarticPacketClockBound
import CurrentAdditive.QuarticQValue
import Paper2.SmallRatClock
import Paper2.FrontClockF

/-! The generic physical threshold/sample-dimension clock at the literal
quartic numeric vector is polynomial in the source graph size and parameter k. -/

set_option maxHeartbeats 64000000
set_option maxRecDepth 16384

namespace Paper2.CurrentAdditive.QuarticTMClockRepair

open EthInapproximability.CurrentPaper
open CurrentAdditive.RandomizedSchedule
open Paper2.CurrentAdditive.QuarticNumericFront

noncomputable def baseCoefficient (Δ : ℕ) (γ : ℚ) : ℕ :=
  2 ^ 32 + 65536 + 100 + QuarticQClockBound.coefficient Δ γ ^ 21 +
    UnaryBinaryEncoding.coefficient + 7

noncomputable def baseExponent (Δ : ℕ) (γ : ℚ) : ℕ :=
  baseCoefficient Δ γ + 337

noncomputable def clockExponent (Δ : ℕ) (γ : ℚ) : ℕ :=
  baseExponent Δ γ * 2128

theorem vector_bound27 (Δ n m : ℕ) (γ : ℚ) (hγ : 0 < γ)
    (hΔ : 0 < Δ) (hn : 0 < n) (hmpos : 0 < m)
    (hm : m ≤ Δ * n) :
    ∀ i, vector27 n m (Nat.clog 2 n) Δ γ i ≤
      (n + 2) ^ (baseExponent Δ γ) := by
  let N := n + 2
  let L := Nat.clog 2 n
  let e := RestorationWidthScheduleScratch.ell L
  let K := baseCoefficient Δ γ
  let V0 := N ^ baseExponent Δ γ
  have hN : 2 ≤ N := by dsimp [N]; omega
  have hN1 : 1 ≤ N := by omega
  have h2e0 : 2 ^ e ≤ (L + 3) ^ 2 := by
    simpa [e, RestorationWidthScheduleScratch.ell] using
      (Paper2.A3Assembly.Clock.two_pow_clog_le (L + 1))
  have hL : L ≤ n := by
    dsimp [L]
    exact Nat.clog_le_of_le_pow (Nat.lt_two_pow_self).le
  have hL3 : L + 3 ≤ 2 * N := by dsimp [N]; omega
  have h2N : 2 * N ≤ N ^ 2 := by nlinarith
  have h2e : 2 ^ e ≤ N ^ 4 := calc
    2 ^ e ≤ (L + 3) ^ 2 := h2e0
    _ ≤ (2 * N) ^ 2 := Nat.pow_le_pow_left hL3 2
    _ ≤ (N ^ 2) ^ 2 := Nat.pow_le_pow_left h2N 2
    _ = N ^ 4 := by ring
  have h2L : 2 ^ L ≤ N ^ 2 := by
    have h := Paper2.A3Assembly.Clock.two_pow_clog_le n
    dsimp [L, N]
    exact h
  have hp : LookupSeed.width L ≤ 64 * N ^ 4 := by
    rw [Paper2.LProducer.p_eq]
    change 2 ^ (6 + e) ≤ 64 * N ^ 4
    rw [pow_add]
    exact Nat.mul_le_mul_left _ h2e
  have hs : SourceProfileParameters.width L ≤ 65536 * N ^ 4 := by
    rw [Paper2.LProducer.s_eq, pow_add]
    change 65536 * 2 ^ e ≤ 65536 * N ^ 4
    exact Nat.mul_le_mul_left _ h2e
  have hq2 : SourceProfileParameters.outerWidth L ≤ 2 ^ 32 * N ^ 10 := by
    rw [Paper2.LProducer.q₂_eq]
    change 2 ^ (32 + (e + (e + L))) ≤ 2 ^ 32 * N ^ 10
    rw [pow_add, pow_add, pow_add]
    have h := Nat.mul_le_mul h2e (Nat.mul_le_mul h2e h2L)
    have heq : N ^ 4 * (N ^ 4 * N ^ 2) = N ^ 10 := by ring
    rw [heq] at h
    exact Nat.mul_le_mul_left _ h
  have hw : width27 L ≤ 100 * N ^ 16 := by
    have h0 : width27 L ≤ WidthMachine.clock e := by
      dsimp [width27, WidthMachine.clock, e]
      omega
    exact h0.trans (by simpa [N, L, e] using width_clock_poly n)
  have hQ : Q27 (V := Fin n) (E := Fin m) L γ Δ ≤
      QuarticQClockBound.coefficient Δ γ ^ 21 * N ^ 336 := by
    have hqBd := QuarticQClockBound.qBd_poly27 Δ n m γ hm
    have hqVal := SmallRatClock.qBd_four γ.num.toNat γ.den Δ n m L
      (SourceProfileParameters.width L) (width27 L)
    rw [qVal_quartic_eq_Q27 n m L Δ γ hγ hΔ hn hmpos] at hqVal
    have hq : Q27 (V := Fin n) (E := Fin m) L γ Δ ≤
        QProducer.qBd γ.num.toNat γ.den Δ n m L
          (SourceProfileParameters.width L) (width27 L) := by omega
    exact hq.trans (by simpa only [L, N] using hqBd)
  have hN4 : N ^ 4 ≤ N ^ 336 := Nat.pow_le_pow_right hN1 (by omega)
  have hN10 : N ^ 10 ≤ N ^ 336 := Nat.pow_le_pow_right hN1 (by omega)
  have hN16 : N ^ 16 ≤ N ^ 336 := Nat.pow_le_pow_right hN1 (by omega)
  have hK64 : 64 ≤ K := by dsimp [K, baseCoefficient]; omega
  have hK65536 : 65536 ≤ K := by dsimp [K, baseCoefficient]; omega
  have hKq2 : 2 ^ 32 ≤ K := by dsimp [K, baseCoefficient]; omega
  have hK100 : 100 ≤ K := by dsimp [K, baseCoefficient]; omega
  have hKQ : QuarticQClockBound.coefficient Δ γ ^ 21 ≤ K := by
    dsimp [K, baseCoefficient]
    omega
  have hV0 : K * N ^ 336 ≤ V0 := by
    have hKN : K ≤ N ^ K :=
      (Nat.lt_two_pow_self).le.trans (Nat.pow_le_pow_left hN K)
    have h := Nat.mul_le_mul_right (N ^ 336) hKN
    have heq : N ^ K * N ^ 336 = N ^ (K + 336) := by rw [← pow_add]
    rw [heq] at h
    exact h.trans (by
      dsimp [V0, baseExponent]
      exact Nat.pow_le_pow_right hN1 (by omega))
  have hp' : LookupSeed.width L ≤ V0 :=
    hp.trans ((Nat.mul_le_mul hK64 hN4).trans hV0)
  have hs' : SourceProfileParameters.width L ≤ V0 :=
    hs.trans ((Nat.mul_le_mul hK65536 hN4).trans hV0)
  have hq2' : SourceProfileParameters.outerWidth L ≤ V0 :=
    hq2.trans ((Nat.mul_le_mul hKq2 hN10).trans hV0)
  have hw' : width27 L ≤ V0 :=
    hw.trans ((Nat.mul_le_mul hK100 hN16).trans hV0)
  have hQ' : Q27 (V := Fin n) (E := Fin m) L γ Δ ≤ V0 :=
    hQ.trans ((Nat.mul_le_mul_right _ hKQ).trans hV0)
  simpa only [V0, N, L, vector27] using
    (Paper2.FrontClock13.vec5_le _ _ _ _ _ _ hp' hs' hq2' hw' hQ')


#print axioms vector_bound27
end Paper2.CurrentAdditive.QuarticTMClockRepair
