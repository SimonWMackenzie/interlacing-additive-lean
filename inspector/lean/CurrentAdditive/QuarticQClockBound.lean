import Paper2.FrontClockB
import Paper2.LIdent
import CurrentAdditive.QuarticWidthClock

/-! Graph-polynomial bound for the existing fixed Q-producer when it is fed
the literal quartic width, rather than the old restoration width. -/

set_option maxHeartbeats 8000000
set_option maxRecDepth 16384

namespace Paper2.CurrentAdditive.QuarticQClockBound

open EthInapproximability.CurrentPaper
open CurrentAdditive.RandomizedSchedule

noncomputable def coefficient (Δ : ℕ) (γ : ℚ) : ℕ :=
  2 ^ 32 + UnaryBinaryEncoding.coefficient + 6 + γ.num.toNat +
    2 * γ.den * Δ + 6144 * γ.den + 100 + 65536 + Δ + 3

/-- A fixed graph-polynomial bound on the actual Q-producer runtime at
`width27 (clog₂ n)`. Only the degree-density inequality is used. -/
theorem qBd_poly27 (Δ n m : ℕ) (γ : ℚ) (hm : m ≤ Δ * n) :
    QProducer.qBd γ.num.toNat γ.den Δ n m (Nat.clog 2 n)
      (SourceProfileParameters.width (Nat.clog 2 n))
      (width27 (Nat.clog 2 n)) ≤
        coefficient Δ γ ^ 21 * (n + 2) ^ 336 := by
  let N := n + 2
  let L := Nat.clog 2 n
  let e := RestorationWidthScheduleScratch.ell L
  let K := coefficient Δ γ
  let V := K * N ^ 16
  have hN : 2 ≤ N := by dsimp [N]; omega
  have hN1 : 1 ≤ N := by omega
  have hN16 : 1 ≤ N ^ 16 := Nat.one_le_pow _ _ hN1
  have hK : 2 ^ 32 ≤ K := by dsimp [K, coefficient]; omega
  have hKV : K ≤ V := by
    dsimp [V]
    exact Nat.le_mul_of_pos_right K hN16
  have hV : 2 ^ 32 ≤ V := hK.trans hKV
  have hc : UnaryBinaryEncoding.coefficient + 6 ≤ V := by
    apply le_trans _ hKV
    dsimp [K, coefficient]
    omega
  have ha : γ.num.toNat ≤ V := by
    apply le_trans _ hKV
    dsimp [K, coefficient]
    omega
  have hbΔ : 2 * γ.den * Δ ≤ V := by
    apply le_trans _ hKV
    dsimp [K, coefficient]
    omega
  have hb : 6144 * γ.den ≤ V := by
    apply le_trans _ hKV
    dsimp [K, coefficient]
    omega
  have hNpow : N ≤ N ^ 16 := by
    calc N = N ^ 1 := by simp
      _ ≤ N ^ 16 := Nat.pow_le_pow_right hN1 (by omega)
  have hn : n ≤ V := by
    have hn' : n ≤ N ^ 16 := by dsimp [N] at *; omega
    have hK1 : 1 ≤ K := by omega
    exact hn'.trans (by
      simpa only [one_mul] using (Nat.mul_le_mul_right (N ^ 16) hK1))
  have hmV : m ≤ V := by
    have hn' : n ≤ N ^ 16 := by dsimp [N] at *; omega
    have hmul := Nat.mul_le_mul_left Δ hn'
    have hΔK : Δ ≤ K := by dsimp [K, coefficient]; omega
    have hmul2 := Nat.mul_le_mul_right (N ^ 16) hΔK
    dsimp [V]
    exact hm.trans (hmul.trans hmul2)
  have hL : L ≤ V := by
    have hLn : L ≤ n := by
      dsimp [L]
      exact Nat.clog_le_of_le_pow (Nat.lt_two_pow_self).le
    exact hLn.trans hn
  have hpow : 2 ^ e ≤ (L + 3) ^ 2 := by
    simpa [e, RestorationWidthScheduleScratch.ell] using
      (Paper2.A3Assembly.Clock.two_pow_clog_le (L + 1))
  have hL3 : L + 3 ≤ 2 * N := by
    have hLn : L ≤ n := by
      dsimp [L]
      exact Nat.clog_le_of_le_pow (Nat.lt_two_pow_self).le
    dsimp [N]
    omega
  have h2N : 2 * N ≤ N ^ 2 := by nlinarith
  have h2e : 2 ^ e ≤ N ^ 4 := calc
    2 ^ e ≤ (L + 3) ^ 2 := hpow
    _ ≤ (2 * N) ^ 2 := Nat.pow_le_pow_left hL3 2
    _ ≤ (N ^ 2) ^ 2 := Nat.pow_le_pow_left h2N 2
    _ = N ^ 4 := by ring
  have hsN : SourceProfileParameters.width L ≤ 65536 * N ^ 4 := by
    rw [Paper2.LProducer.s_eq, pow_add]
    change 65536 * 2 ^ e ≤ 65536 * N ^ 4
    exact Nat.mul_le_mul_left 65536 h2e
  have hN4 : N ^ 4 ≤ N ^ 16 := Nat.pow_le_pow_right hN1 (by omega)
  have hs : SourceProfileParameters.width L ≤ V := by
    calc SourceProfileParameters.width L ≤ 65536 * N ^ 4 := hsN
      _ ≤ 65536 * N ^ 16 := Nat.mul_le_mul_left _ hN4
      _ ≤ K * N ^ 16 := Nat.mul_le_mul_right _ (by dsimp [K, coefficient]; omega)
      _ = V := rfl
  have hwClock := Paper2.CurrentAdditive.QuarticNumericFront.width_clock_poly n
  have hw0 : width27 L ≤ Paper2.CurrentAdditive.QuarticNumericFront.WidthMachine.clock e := by
    dsimp [width27, Paper2.CurrentAdditive.QuarticNumericFront.WidthMachine.clock, e]
    omega
  have hw100 : width27 L ≤ 100 * N ^ 16 := by
    exact hw0.trans (by simpa [N, L, e] using hwClock)
  have hw : width27 L ≤ V := by
    exact hw100.trans (Nat.mul_le_mul_right _ (by dsimp [K, coefficient]; omega))
  have hq := Paper2.FrontClock13.qBd_le γ.num.toNat γ.den Δ n m L
    (SourceProfileParameters.width L) (width27 L) V
    hV hc ha hbΔ hb hn hmV hL hs hw
  have hV21 : V ^ 21 = K ^ 21 * N ^ 336 := by
    dsimp [V]
    rw [mul_pow, ← pow_mul]
  simpa only [L, N, K, hV21] using hq

#print axioms qBd_poly27

end Paper2.CurrentAdditive.QuarticQClockBound
