import CurrentAdditive.QuarticFairCap
import CurrentAdditive.QuarticConstructor
import Paper2.TotalFiniteResources

/-! Literal v27 fair-bit input and selected-output size bounds. -/

set_option maxHeartbeats 2000000
set_option maxRecDepth 8192

namespace Paper2.CurrentAdditive.QuarticInputSize

open Paper2.SourceProfileParameters Paper2.SourceRecursiveNoSampling
open CurrentAdditive.RandomizedSchedule
open Paper2.CurrentAdditive.QuarticConstructor

theorem inputBitCount_le27 {n m : ℕ} [NeZero n]
    (L Δ : ℕ) (γ : ℚ)
    (hc : CurrentAdditive.QuarticSchedule.Checks27
      (V := Fin n) (Edges := Fin m) L Δ γ) (k : ℕ) :
    RecursiveSamplingMaterialization.inputBitCount (Fin n)
      (width L) (width L - 2) (outerWidth L)
      (width27 L) (Q27 (V := Fin n) (E := Fin m) L γ Δ)
      (LookupSeed.width L) k
      (sourceRows L (4 * RestorationWidthScheduleScratch.ell L)
        (q27 (V := Fin n) (E := Fin m) L γ Δ) k)
      (sourceCols L (4 * RestorationWidthScheduleScratch.ell L)
        (q27 (V := Fin n) (E := Fin m) L γ Δ) k) ≤
      2 ^ (80 * (k + 1) * L) := by
  have hL : 16 ≤ L := by
    rcases hc with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hL, _⟩
    exact hL
  exact Paper2.FairBitCap.inputBitCount_le_of_caps (Fin n)
    (width L) (width L - 2) (outerWidth L)
    (width27 L) (Q27 (V := Fin n) (E := Fin m) L γ Δ)
    (LookupSeed.width L) k
    (sourceRows L (4 * RestorationWidthScheduleScratch.ell L)
      (q27 (V := Fin n) (E := Fin m) L γ Δ) k)
    (sourceCols L (4 * RestorationWidthScheduleScratch.ell L)
      (q27 (V := Fin n) (E := Fin m) L γ Δ) k)
    L (k + 1) (by omega) hL
    (QuarticFairCap.drawCap_le27 L Δ γ hc k)
    (by simpa only [Fintype.card_fin] using QuarticFairCap.bitWidth_le27 L Δ γ hc)

theorem tapeBits_length27 {n m : ℕ} (hn : 0 < n)
    (edge : Fin m → Bool → Fin n) (Δ : ℕ) (γ : ℚ) (k : ℕ) :
    ∀ t : (select27 hn edge Δ γ k).Tape,
      ((select27 hn edge Δ γ k).tapeBits t).length =
        (select27 hn edge Δ γ k).inputBits := by
  by_cases hc : CurrentAdditive.QuarticSchedule.Checks27
      (V := Fin n) (Edges := Fin m) (Nat.clog 2 n) Δ γ
  · rw [select27_good hn edge Δ γ k hc]
    intro t
    exact t.property
  · rw [select27_bad hn edge Δ γ k hc]
    intro t
    rfl

private theorem dyadic_le_base_square (n : ℕ) (hn : 0 < n) :
    2 ^ Nat.clog 2 n ≤ (n + 2) ^ 2 := by
  have h := CappedSampler.ticketSize_le_twice n hn
  change 2 ^ Nat.clog 2 n ≤ 2 * n at h
  nlinarith

private theorem scheduled_pow_le (n k c : ℕ) (hn : 0 < n)
    (hc : 2 * c ≤ 160) :
    2 ^ (c * (k + 1) * Nat.clog 2 n) ≤
      TotalFiniteResourcesScratch.resourceBound n k := by
  have hbase := dyadic_le_base_square n hn
  have hpow := Nat.pow_le_pow_left hbase (c * (k + 1))
  calc
    _ = (2 ^ Nat.clog 2 n) ^ (c * (k + 1)) := by
      rw [← pow_mul]
      congr 1
      ring
    _ ≤ ((n + 2) ^ 2) ^ (c * (k + 1)) := hpow
    _ = (n + 2) ^ (2 * (c * (k + 1))) := by rw [← pow_mul]
    _ ≤ TotalFiniteResourcesScratch.resourceBound n k := by
      dsimp [TotalFiniteResourcesScratch.resourceBound]
      exact pow_le_pow_right₀ (by omega) (by nlinarith)

/-- Both branches of the literal v27 selector announce counts bounded by
the same fixed polynomial. -/
theorem selected_announced_counts_le27 {n m : ℕ} (hn : 0 < n)
    (edge : Fin m → Bool → Fin n) (Δ : ℕ) (γ : ℚ)
    (k : ℕ) (hk : 1 ≤ k) :
    let o := select27 hn edge Δ γ k
    o.rows * o.cols ≤ TotalFiniteResourcesScratch.resourceBound n k ∧
      o.inputBits ≤ TotalFiniteResourcesScratch.resourceBound n k := by
  dsimp only
  by_cases hc : CurrentAdditive.QuarticSchedule.Checks27
      (V := Fin n) (Edges := Fin m) (Nat.clog 2 n) Δ γ
  · letI : NeZero n := ⟨Nat.ne_of_gt hn⟩
    rw [select27_good hn edge Δ γ k hc]
    constructor
    · obtain ⟨hx, hy⟩ := QuarticClockCaps.dims_cap27
        (n := n) (m := m) (Nat.clog 2 n) Δ γ hc k
      rw [Nat.mul_assoc] at hx hy
      have hxy := Nat.mul_le_mul hx hy
      change rows27 n m (Nat.clog 2 n) Δ γ k *
          cols27 n m (Nat.clog 2 n) Δ γ k ≤ _
      calc
        _ ≤ (2 ^ (29 * (k + 1) * Nat.clog 2 n)) ^ 2 := by
          simpa only [pow_two, rows27, cols27, Nat.mul_assoc] using hxy
        _ = 2 ^ (58 * (k + 1) * Nat.clog 2 n) := by
          rw [← pow_mul]
          congr 1
          ring
        _ ≤ TotalFiniteResourcesScratch.resourceBound n k :=
          scheduled_pow_le n k 58 hn (by norm_num)
    · change RecursiveSamplingMaterialization.inputBitCount (Fin n)
        (width (Nat.clog 2 n)) (width (Nat.clog 2 n) - 2)
        (outerWidth (Nat.clog 2 n)) (width27 (Nat.clog 2 n))
        (Q27 (V := Fin n) (E := Fin m) (Nat.clog 2 n) γ Δ)
        (LookupSeed.width (Nat.clog 2 n)) k
        (rows27 n m (Nat.clog 2 n) Δ γ k)
        (cols27 n m (Nat.clog 2 n) Δ γ k) ≤ _
      exact (inputBitCount_le27 (Nat.clog 2 n) Δ γ hc k).trans
        (scheduled_pow_le n k 80 hn (by norm_num))
  · rw [select27_bad hn edge Δ γ k hc]
    constructor
    · have hsize := FiniteFallbackOutput.fallback_bits_length_le edge k hk
      rw [FiniteFallbackOutput.fallbackTable_bits_length] at hsize
      have hbase : 2 ≤ n + 2 := by omega
      have hpow : 2 ^ (2 * k) ≤ (n + 2) ^ (2 * k) :=
        Nat.pow_le_pow_left hbase _
      have hexp : 2 * k ≤ 160 * (k + 1) := by omega
      simpa only [TotalFiniteConstructorScratch.fallbackOutput] using
        hsize.trans (hpow.trans (by
          dsimp [TotalFiniteResourcesScratch.resourceBound]
          exact pow_le_pow_right₀ (by omega) hexp))
    · simp [TotalFiniteConstructorScratch.fallbackOutput,
        TotalFiniteResourcesScratch.resourceBound]

#print axioms inputBitCount_le27
#print axioms tapeBits_length27
#print axioms selected_announced_counts_le27

end Paper2.CurrentAdditive.QuarticInputSize
