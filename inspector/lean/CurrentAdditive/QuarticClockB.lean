import CurrentAdditive.QuarticNoneRun
import CurrentAdditive.QuarticNoPreloadClock
import CurrentAdditive.QuarticClockCaps
import Paper2.A3H3ClockB

set_option maxHeartbeats 4000000
set_option maxRecDepth 16384

namespace Paper2.CurrentAdditive.QuarticClockB

open EthInapproximability.CurrentPaper
open Paper2.SourceProfileParameters Paper2.ParameterizedCanonicalSource
open Paper2.A3Assembly.Clock Paper2.A3Assembly.Clocks
open CurrentAdditive.RandomizedSchedule

theorem probe_clock_HA3_27 {n m : ℕ} [NeZero n] (Δ : ℕ) (γ : ℚ)
    (hc : CurrentAdditive.QuarticSchedule.Checks27
      (V := Fin n) (Edges := Fin m) (Nat.clog 2 n) Δ γ) (k : ℕ) :
    SamplerFallbackJoin.clock n (LookupSeed.width (Nat.clog 2 n))
      (width (Nat.clog 2 n)) (width (Nat.clog 2 n) - 2)
      (outerWidth (Nat.clog 2 n)) (width27 (Nat.clog 2 n))
      (Q27 (V := Fin n) (E := Fin m) (Nat.clog 2 n) γ Δ) k
      (SourceRecursiveNoSampling.sourceRows (Nat.clog 2 n) ((4 * RestorationWidthScheduleScratch.ell (Nat.clog 2 n)))
        ((q27 (V := Fin n) (E := Fin m) (Nat.clog 2 n) γ Δ)) k)
      (SourceRecursiveNoSampling.sourceCols (Nat.clog 2 n) ((4 * RestorationWidthScheduleScratch.ell (Nat.clog 2 n)))
        ((q27 (V := Fin n) (E := Fin m) (Nat.clog 2 n) γ Δ)) k) ≤
      1 * (n + 2) ^ ((2 * FallbackNoPreloadRun.noPreloadExponent) * (k + 1)) := by
  have h := QuarticNoPreloadClock.no_preload_clock27
    (n := n) (m := m) (Nat.clog 2 n) Δ γ hc k
  have hc2 := Paper2.A3Assembly.Clock.clock_convert 1 FallbackNoPreloadRun.noPreloadExponent k n
  omega

/-- The source budget at the actual schedule is at most `2^(29(k+1)L)`. -/
theorem budget_cap27 {n m : ℕ} [NeZero n] (Δ : ℕ) (γ : ℚ)
    (hc : CurrentAdditive.QuarticSchedule.Checks27
      (V := Fin n) (Edges := Fin m) (Nat.clog 2 n) Δ γ) (k : ℕ) :
    SourceRecursiveNoSampling.sourceBudget (Nat.clog 2 n) ((4 * RestorationWidthScheduleScratch.ell (Nat.clog 2 n)))
        ((q27 (V := Fin n) (E := Fin m) (Nat.clog 2 n) γ Δ)) k ≤ 2 ^ (29 * ((k + 1) * Nat.clog 2 n)) := by
  obtain ⟨hn, hp, hs, hq₁, hq₂, hw, hQ, hm, hL⟩ :=
    QuarticClockCaps.scalar_caps27 (n := n) (m := m) (Nat.clog 2 n) Δ γ hc
  dsimp [Paper2.GeneratorPublicCap.publicCap] at hn hp hs hq₁ hq₂ hw hQ hm
  have hthr := QuarticConstructor.threshold27_eq_budget n m Δ γ k
  dsimp only at hthr
  rw [← hthr]
  have hXv : ThrProducer.Xv ![LookupSeed.width (Nat.clog 2 n),
      width (Nat.clog 2 n), outerWidth (Nat.clog 2 n),
      width27 (Nat.clog 2 n), Q27 (V := Fin n) (E := Fin m) (Nat.clog 2 n) γ Δ] ≤
      5 * 2 ^ (7 * Nat.clog 2 n) :=
    Paper2.SuccessClock2Pre.Xv_le _ _ (by intro i; fin_cases i <;> simp <;> omega)
  have hcp := Paper2.SuccessClock2Pre.clog_le (LookupSeed.width (Nat.clog 2 n))
  have hk : k < 2 ^ k := Nat.lt_two_pow_self
  have hkX := Nat.mul_le_mul hk.le hXv
  have hA : 1 ≤ 2 ^ k := Nat.one_le_two_pow
  have hB : 1 ≤ 2 ^ (7 * Nat.clog 2 n) := Nat.one_le_two_pow
  have e : 2 ^ k * (5 * 2 ^ (7 * Nat.clog 2 n)) ≤ 2 ^ (k + 3 + 7 * Nat.clog 2 n) := by
    calc 2 ^ k * (5 * 2 ^ (7 * Nat.clog 2 n)) ≤ 2 ^ k * (8 * 2 ^ (7 * Nat.clog 2 n)) :=
          Nat.mul_le_mul_left _ (by omega)
      _ = 2 ^ (k + 3 + 7 * Nat.clog 2 n) := by rw [pow_add, pow_add]; ring
  have e2 : 2 * 2 ^ (7 * Nat.clog 2 n) ≤ 2 ^ (k + 3 + 7 * Nat.clog 2 n) := by
    have := Nat.pow_le_pow_right (show 0 < 2 by norm_num)
      (show 7 * Nat.clog 2 n + 1 ≤ k + 3 + 7 * Nat.clog 2 n by omega)
    rw [pow_succ] at this; omega
  have e3 : 2 * 2 ^ (k + 3 + 7 * Nat.clog 2 n) ≤ 2 ^ (29 * ((k + 1) * Nat.clog 2 n)) := by
    have := Nat.pow_le_pow_right (show 0 < 2 by norm_num)
      (show k + 3 + 7 * Nat.clog 2 n + 1 ≤ 29 * ((k + 1) * Nat.clog 2 n) by nlinarith)
    rw [pow_succ] at this; omega
  omega

/-- **(S-none, header)** The admitted header `HeaderA.prog` on `(mX, mY, sourceBudget)` at the
actual schedule, in H_A3 shape. -/
theorem none_header_HA3_27 {n m : ℕ} [NeZero n] (Δ : ℕ) (γ : ℚ)
    (hc : CurrentAdditive.QuarticSchedule.Checks27
      (V := Fin n) (Edges := Fin m) (Nat.clog 2 n) Δ γ) (k : ℕ) :
    headerClock
      (SourceRecursiveNoSampling.sourceRows (Nat.clog 2 n) ((4 * RestorationWidthScheduleScratch.ell (Nat.clog 2 n)))
        ((q27 (V := Fin n) (E := Fin m) (Nat.clog 2 n) γ Δ)) k)
      (SourceRecursiveNoSampling.sourceCols (Nat.clog 2 n) ((4 * RestorationWidthScheduleScratch.ell (Nat.clog 2 n)))
        ((q27 (V := Fin n) (E := Fin m) (Nat.clog 2 n) γ Δ)) k)
      (SourceRecursiveNoSampling.sourceBudget (Nat.clog 2 n) ((4 * RestorationWidthScheduleScratch.ell (Nat.clog 2 n)))
        ((q27 (V := Fin n) (E := Fin m) (Nat.clog 2 n) γ Δ)) k) ≤
      (12 * UnaryBinaryEncoding.coefficient + 23) * (n + 2) ^ (116 * (k + 1)) := by
  obtain ⟨hmX, hmY⟩ := QuarticClockCaps.dims_cap27 (n := n) (m := m) (Nat.clog 2 n) Δ γ hc k
  rw [Nat.mul_assoc] at hmX hmY
  have hb := budget_cap27 (n := n) (m := m) Δ γ hc k
  have hY1 : 1 ≤ 2 ^ (29 * ((k + 1) * Nat.clog 2 n)) := Nat.one_le_two_pow
  have h := headerClock_le _ _ _ _ hmX hmY hb hY1
  have hconv : 2 ^ (29 * ((k + 1) * Nat.clog 2 n)) ≤ (n + 2) ^ (58 * (k + 1)) := by
    have h29 := Paper2.A3Assembly.Clock.two_pow_mul_clog_le 29 k n
    rw [show 2 * 29 * (k + 1) = 58 * (k + 1) by ring] at h29
    rw [show 29 * ((k + 1) * Nat.clog 2 n) = 29 * (k + 1) * Nat.clog 2 n by ring]
    exact h29
  have hsq : (2 ^ (29 * ((k + 1) * Nat.clog 2 n))) ^ 2 ≤ (n + 2) ^ (116 * (k + 1)) := by
    have h2 := Nat.pow_le_pow_left hconv 2
    have e : ((n + 2) ^ (58 * (k + 1))) ^ 2 = (n + 2) ^ (116 * (k + 1)) := by
      rw [← pow_mul, show 58 * (k + 1) * 2 = 116 * (k + 1) by ring]
    exact h2.trans (le_of_eq e)
  exact h.trans (Nat.mul_le_mul_left _ hsq)


end Paper2.CurrentAdditive.QuarticClockB

#print axioms Paper2.CurrentAdditive.QuarticClockB.probe_clock_HA3_27
#print axioms Paper2.CurrentAdditive.QuarticClockB.budget_cap27
#print axioms Paper2.CurrentAdditive.QuarticClockB.none_header_HA3_27
