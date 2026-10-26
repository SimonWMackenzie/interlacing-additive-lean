import Paper2.SC2Pre
import Paper2.A3Clock
import Paper2.FallbackFiniteClock
import Paper2.FallbackNoPreloadEndpoint
import Paper2.HeaderOut

/-!
# Unit 3 endpoint (H_A3 closure), segment 2: the branch clocks in H_A3 shape

Lane `owner:a-h-a3-assembly-3` (private, 26 September 2026). Pure arithmetic; no machine.

Every clock below is put into the H_A3 shape `C·(n+2)^(E·(k+1))` with absolute `C`, `E`
(depending only on the fixed public data `Δ, γ` where stated):

* (S) success chain: the literal clock of `ThrJoin.success_run_full` (via `SuccessClock2Pre.full_split`,
  lane a-success-clock-owner-2 segment 4, recompiled here against the production `Paper2.ThrMain` as
  `A3H3Pre`) is `≤ 1·(n+2)^(ES(k+1))`, `ES = 2(noPreloadExponent + preExponent + entryExponent 2601 + 65)`,
  from `SC2Close.success_clock_HA3` with `hpre` discharged by `SuccessClock2Pre.pre_sched`;
* (S-none) generator-outcome probe `SamplerFallbackJoin.clock` (the admitted all-outcomes program of
  `FallbackNoPreloadEndpoint`) `≤ 1·(n+2)^((2·noPreloadExponent)(k+1))`, and the admitted header
  `HeaderA.prog` clock on `(mX, mY, sourceBudget)` `≤ (12·coef + 23)·(n+2)^(116(k+1))`;
* (U) failed schedule: the admitted `FallbackFiniteClock` coefficient times `2^(3k)`
  `≤ coefficient·(n+2)^(3(k+1))`, and the header on `(rows k, cols k, 0)`
  `≤ (12·coef + 23)·(n+2)^(2(k+1))`;
* generic `poly_add` / `poly_mono` to sum named polynomial clocks (front, dispatch, copies).
-/

set_option maxHeartbeats 4000000
set_option maxRecDepth 16384

namespace Paper2.A3Assembly.Clocks

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.EncodedCommunication
open Paper2.GeneratorCode Paper2.GeneratorSerialization Paper2.GeneratorSource
  Paper2.RecursiveLabelCodecScratch Paper2.RecursiveEntries Paper2.ParameterizedCanonicalSource
  Paper2.SourceProfileParameters

/-! ## Generic polynomial bookkeeping -/

theorem poly_mono {N A A' a a' k x : ℕ} (hN : 1 ≤ N) (hA : A ≤ A') (ha : a ≤ a')
    (hx : x ≤ A * N ^ (a * (k + 1))) : x ≤ A' * N ^ (a' * (k + 1)) := by
  have h1 : N ^ (a * (k + 1)) ≤ N ^ (a' * (k + 1)) :=
    Nat.pow_le_pow_right hN (Nat.mul_le_mul_right _ ha)
  exact hx.trans (Nat.mul_le_mul hA h1)

theorem poly_add {N A B a b k x y : ℕ} (hN : 1 ≤ N)
    (hx : x ≤ A * N ^ (a * (k + 1))) (hy : y ≤ B * N ^ (b * (k + 1))) :
    x + y ≤ (A + B) * N ^ (max a b * (k + 1)) := by
  have h1 := poly_mono (A' := A) (a' := max a b) hN le_rfl (le_max_left a b) hx
  have h2 := poly_mono (A' := B) (a' := max a b) hN le_rfl (le_max_right a b) hy
  rw [Nat.add_mul]
  omega

theorem poly_const {N c a k : ℕ} (hN : 1 ≤ N) : c ≤ c * N ^ (a * (k + 1)) :=
  Nat.le_mul_of_pos_right _ (pow_pos hN _)

/-! ## (S-none) the generator-outcome probe and the false-table header -/

/-- The admitted header clock of `HeaderA.prog` (`HeaderOut.header_outputBits`). -/
noncomputable def headerClock (r c t : ℕ) : ℕ :=
  UnaryBinaryEncoding.coefficient * (r + 1) ^ 2 + UnaryBinaryEncoding.coefficient * (c + 1) ^ 2 +
    UnaryBinaryEncoding.coefficient * (t + 1) ^ 2 +
    (2 * (natField r ++ natField c ++ natField t).length + 2) + 3

theorem headerClock_le (r c t Y : ℕ) (hr : r ≤ Y) (hc : c ≤ Y) (ht : t ≤ Y) (hY : 1 ≤ Y) :
    headerClock r c t ≤ (12 * UnaryBinaryEncoding.coefficient + 23) * Y ^ 2 := by
  have sq : ∀ x, x ≤ Y → (x + 1) ^ 2 ≤ 4 * Y ^ 2 := by
    intro x hx
    have : (x + 1) ^ 2 ≤ (2 * Y) ^ 2 := Nat.pow_le_pow_left (by omega) 2
    simpa [mul_pow] using this
  have a1 := Nat.mul_le_mul_left UnaryBinaryEncoding.coefficient (sq r hr)
  have a2 := Nat.mul_le_mul_left UnaryBinaryEncoding.coefficient (sq c hc)
  have a3 := Nat.mul_le_mul_left UnaryBinaryEncoding.coefficient (sq t ht)
  have n1 := Paper2.SuccessClock2Pre.natField_len r
  have n2 := Paper2.SuccessClock2Pre.natField_len c
  have n3 := Paper2.SuccessClock2Pre.natField_len t
  have hY2 : Y ≤ Y ^ 2 := by nlinarith
  have hY1 : 1 ≤ Y ^ 2 := by nlinarith
  unfold headerClock
  simp only [List.length_append]
  have e : (12 * UnaryBinaryEncoding.coefficient + 23) * Y ^ 2 =
      UnaryBinaryEncoding.coefficient * (4 * Y ^ 2) + UnaryBinaryEncoding.coefficient * (4 * Y ^ 2) +
        UnaryBinaryEncoding.coefficient * (4 * Y ^ 2) + 23 * Y ^ 2 := by ring
  rw [e]
  omega

/-- **(S-none, probe)** The admitted all-outcomes program `SamplerFallbackJoin.program`
(`FallbackNoPreloadEndpoint`) at the actual schedule, in H_A3 shape. -/
theorem probe_clock_HA3 {n m : ℕ} [NeZero n] (Δ : ℕ) (γ : ℚ)
    (hc : Paper2.CompletePublicScheduleScratch.Checks
      (V := Fin n) (E := Fin m) (Nat.clog 2 n) Δ γ) (k : ℕ) :
    SamplerFallbackJoin.clock n (LookupSeed.width (Nat.clog 2 n))
      (width (Nat.clog 2 n)) (width (Nat.clog 2 n) - 2)
      (outerWidth (Nat.clog 2 n)) (restorationWidth (Nat.clog 2 n))
      (coverWidth n m (Nat.clog 2 n) Δ γ) k
      (SourceRecursiveNoSampling.sourceRows (Nat.clog 2 n) (restorationDepth (Nat.clog 2 n))
        (coverDepth n m (Nat.clog 2 n) Δ γ) k)
      (SourceRecursiveNoSampling.sourceCols (Nat.clog 2 n) (restorationDepth (Nat.clog 2 n))
        (coverDepth n m (Nat.clog 2 n) Δ γ) k) ≤
      1 * (n + 2) ^ ((2 * FallbackNoPreloadRun.noPreloadExponent) * (k + 1)) := by
  have h := Paper2.FallbackNoPreloadEndpoint.scheduled_no_preload_clock_le
    (n := n) (m := m) (Nat.clog 2 n) Δ γ hc k
  have hc2 := Paper2.A3Assembly.Clock.clock_convert 1 FallbackNoPreloadRun.noPreloadExponent k n
  omega

/-- The source budget at the actual schedule is at most `2^(29(k+1)L)`. -/
theorem budget_cap {n m : ℕ} [NeZero n] (Δ : ℕ) (γ : ℚ)
    (hc : Paper2.CompletePublicScheduleScratch.Checks
      (V := Fin n) (E := Fin m) (Nat.clog 2 n) Δ γ) (k : ℕ) :
    SourceRecursiveNoSampling.sourceBudget (Nat.clog 2 n) (restorationDepth (Nat.clog 2 n))
        (coverDepth n m (Nat.clog 2 n) Δ γ) k ≤ 2 ^ (29 * ((k + 1) * Nat.clog 2 n)) := by
  obtain ⟨hn, hp, hs, hq₁, hq₂, hw, hQ, hm, hL⟩ :=
    Paper2.SuccessClock.scalar_caps (n := n) (m := m) (Nat.clog 2 n) Δ γ hc
  have hthr := ThrJoin.budget_eq n m Δ γ k
  dsimp only at hthr
  rw [← hthr]
  have hXv : ThrProducer.Xv ![LookupSeed.width (Nat.clog 2 n),
      width (Nat.clog 2 n), outerWidth (Nat.clog 2 n),
      restorationWidth (Nat.clog 2 n), coverWidth n m (Nat.clog 2 n) Δ γ] ≤
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
theorem none_header_HA3 {n m : ℕ} [NeZero n] (Δ : ℕ) (γ : ℚ)
    (hc : Paper2.CompletePublicScheduleScratch.Checks
      (V := Fin n) (E := Fin m) (Nat.clog 2 n) Δ γ) (k : ℕ) :
    headerClock
      (SourceRecursiveNoSampling.sourceRows (Nat.clog 2 n) (restorationDepth (Nat.clog 2 n))
        (coverDepth n m (Nat.clog 2 n) Δ γ) k)
      (SourceRecursiveNoSampling.sourceCols (Nat.clog 2 n) (restorationDepth (Nat.clog 2 n))
        (coverDepth n m (Nat.clog 2 n) Δ γ) k)
      (SourceRecursiveNoSampling.sourceBudget (Nat.clog 2 n) (restorationDepth (Nat.clog 2 n))
        (coverDepth n m (Nat.clog 2 n) Δ γ) k) ≤
      (12 * UnaryBinaryEncoding.coefficient + 23) * (n + 2) ^ (116 * (k + 1)) := by
  obtain ⟨hmX, hmY⟩ := Paper2.SuccessClock.dims_cap (n := n) (m := m) (Nat.clog 2 n) Δ γ hc k
  have hb := budget_cap (n := n) (m := m) Δ γ hc k
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

/-! ## (U) the failed-schedule branch -/

/-- **(U, table)** The admitted `FallbackFiniteClock` clock in H_A3 shape. -/
theorem fallback_clock_HA3 (Δ : ℕ) (γ : ℚ) (n k : ℕ) :
    FallbackFiniteClock.coefficient (CompletePublicScheduleScratch.sizeThreshold Δ γ) Δ *
        2 ^ (3 * k) ≤
      FallbackFiniteClock.coefficient (CompletePublicScheduleScratch.sizeThreshold Δ γ) Δ *
        (n + 2) ^ (3 * (k + 1)) := by
  apply Nat.mul_le_mul_left
  calc 2 ^ (3 * k) ≤ (n + 2) ^ (3 * k) := Nat.pow_le_pow_left (by omega) _
    _ ≤ (n + 2) ^ (3 * (k + 1)) := Nat.pow_le_pow_right (by omega) (by omega)

theorem fallback_dims_le (k : ℕ) (hk : 1 ≤ k) :
    FiniteFallbackOutput.rows k ≤ 2 ^ k ∧ FiniteFallbackOutput.cols k ≤ 2 ^ k := by
  match k, hk with
  | 1, _ => exact ⟨by decide, by decide⟩
  | j + 2, _ =>
    have h : 2 ^ (j + 1) ≤ 2 ^ (j + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
    exact ⟨by simpa [FiniteFallbackOutput.rows] using h,
      by simpa [FiniteFallbackOutput.cols] using h⟩

/-- **(U, header)** The admitted header on `(rows k, cols k, 0)` in H_A3 shape. -/
theorem fallback_header_HA3 (n k : ℕ) (hk : 1 ≤ k) :
    headerClock (FiniteFallbackOutput.rows k) (FiniteFallbackOutput.cols k) 0 ≤
      (12 * UnaryBinaryEncoding.coefficient + 23) * (n + 2) ^ (2 * (k + 1)) := by
  obtain ⟨hr, hc⟩ := fallback_dims_le k hk
  have hY : 2 ^ k ≤ (n + 2) ^ (k + 1) :=
    (Nat.pow_le_pow_left (by omega) k).trans (Nat.pow_le_pow_right (by omega) (by omega))
  have h1 : 1 ≤ (n + 2) ^ (k + 1) := Nat.one_le_pow _ _ (by omega)
  have h := headerClock_le _ _ 0 ((n + 2) ^ (k + 1)) (hr.trans hY) (hc.trans hY) (by omega) h1
  rw [← pow_mul, show (k + 1) * 2 = 2 * (k + 1) by ring] at h
  exact h

end Paper2.A3Assembly.Clocks

#print axioms Paper2.A3Assembly.Clocks.poly_add
#print axioms Paper2.A3Assembly.Clocks.headerClock_le
#print axioms Paper2.A3Assembly.Clocks.probe_clock_HA3
#print axioms Paper2.A3Assembly.Clocks.budget_cap
#print axioms Paper2.A3Assembly.Clocks.none_header_HA3
#print axioms Paper2.A3Assembly.Clocks.fallback_clock_HA3
#print axioms Paper2.A3Assembly.Clocks.fallback_header_HA3
