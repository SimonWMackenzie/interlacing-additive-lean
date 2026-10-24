import Paper2.SharpRelative
import Paper2.ScheduledOutputBounds

/-!
Explicit leading-six finite upper bound for the frozen v12 printed rectangle.
The target is its actual row/column count, not generator running time.
-/

namespace Paper2.SharpOutputSize

open Paper2.SourceProfileParameters Paper2.SourceRecursiveNoSampling
  Paper2.ParameterizedCanonicalSource

set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

def lengthCutoff (Δ : ℕ) (γ ε : ℚ) : ℕ :=
  max (SharpRelative.cutoff Δ γ (ε / 12)) (max 16 (Nat.ceil (8 / ε)))

def iterationCutoff (ε : ℚ) : ℕ := Nat.ceil (28 / ε)

/-- The actual final printed-entry count is at most `2^(6B+2k+14)`;
`B` is the public source budget, not an assumed optimum. -/
theorem entries_le_sharp_budget (L r q k : ℕ) (hL : 1 ≤ L) :
    sourceRows L r q k * sourceCols L r q k ≤
      2 ^ (6 * sourceBudget L r q k + 2 * k + 14) := by
  let B := sourceBudget L r q k
  let H := sourceCost L r q k
  have hH : H = B + k := by
    dsimp [H, B, sourceCost, sourceBudget]
    ring
  have hraw := ReductionDimensions.entries_le_pow B H L hL
  have hT : sourceRows L r q k * sourceCols L r q k ≤
      2 ^ (4 * B + 2 * H + 14) := by
    simpa only [ReductionDimensions.entries, sourceRows, sourceCols,
      sourceRank] using hraw
  have heq : 4 * B + 2 * H + 14 = 6 * B + 2 * k + 14 := by omega
  simpa only [B, heq] using hT

/-- For every positive rational accuracy, explicit graph-uniform and
iteration cutoffs preserve the manuscript's leading six in the actual
rectangular printed-entry count. The public `Checks` supplies the seed
budget guard; it does not encode a source promise. -/
theorem printed_entries_le_six_plus (n m L Δ k : ℕ) [NeZero n]
    (γ ε : ℚ) (edge : Fin m → Bool → Fin n)
    (hγ : 0 < γ) (hΔ : 0 < Δ) (hε : 0 < ε)
    (hincident : ∀ v, ∃ e b, edge e b = v)
    (hdegree : ∀ v, SourceItems.degree edge v ≤ Δ)
    (hc : CompletePublicScheduleScratch.Checks
      (V := Fin n) (E := Fin m) L Δ γ)
    (hL : lengthCutoff Δ γ ε ≤ L)
    (hk : iterationCutoff ε ≤ k) :
    (Nat.clog 2 (sourceRows L (restorationDepth L)
      (coverDepth n m L Δ γ) k *
      sourceCols L (restorationDepth L)
        (coverDepth n m L Δ γ) k) : ℚ) ≤
      (6 + ε) * (k : ℚ) * (L : ℚ) := by
  let h := Paper2.SourceOverheadBounds.overhead
    (V := Fin n) (E := Fin m) L Δ γ
  let d₀ := LookupSeed.exponent L + 1
  let B := sourceBudget L (restorationDepth L) (coverDepth n m L Δ γ) k
  let T := sourceRows L (restorationDepth L) (coverDepth n m L Δ γ) k *
    sourceCols L (restorationDepth L) (coverDepth n m L Δ γ) k
  have hL16 : 16 ≤ L := by
    unfold lengthCutoff at hL
    omega
  have hL1 : 1 ≤ L := by omega
  have hseed : d₀ ≤ L := by
    rcases hc with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
      _, _, hseed⟩
    exact hseed
  have hB : B = d₀ + k * h := by
    dsimp [B, sourceBudget, d₀, h, restorationDepth, coverDepth,
      Paper2.SourceOverheadBounds.overhead]
  have hδpos : 0 < ε / 12 := by positivity
  have hδ : (h : ℚ) ≤ (1 + ε / 12) * (L : ℚ) := by
    have hcut : SharpRelative.cutoff Δ γ (ε / 12) ≤ L := by
      unfold lengthCutoff at hL
      omega
    exact (SharpRelative.relative_overhead (V := Fin n) (E := Fin m)
      edge L Δ γ (ε / 12) hcut hγ hΔ hδpos hincident hdegree).2
  have hK : (28 : ℚ) ≤ ε * (k : ℚ) := by
    have hc : (28 : ℚ) / ε ≤ (iterationCutoff ε : ℚ) := Nat.le_ceil _
    have hn : (iterationCutoff ε : ℚ) ≤ (k : ℚ) := by exact_mod_cast hk
    have h := (div_le_iff₀ hε).mp (hc.trans hn)
    nlinarith
  have hLε : (8 : ℚ) ≤ ε * (L : ℚ) := by
    have hn : Nat.ceil ((8 : ℚ) / ε) ≤ L := by
      unfold lengthCutoff at hL
      omega
    have hc : (8 : ℚ) / ε ≤ (Nat.ceil ((8 : ℚ) / ε) : ℚ) := Nat.le_ceil _
    have hnq : (Nat.ceil ((8 : ℚ) / ε) : ℚ) ≤ (L : ℚ) := by exact_mod_cast hn
    have h := (div_le_iff₀ hε).mp (hc.trans hnq)
    nlinarith
  have hBound := entries_le_sharp_budget L (restorationDepth L)
    (coverDepth n m L Δ γ) k hL1
  have hclogNat : Nat.clog 2 T ≤ 6 * B + 2 * k + 14 := by
    exact Nat.clog_le_of_le_pow hBound
  have hclog : (Nat.clog 2 T : ℚ) ≤ 6 * (B : ℚ) + 2 * (k : ℚ) + 14 := by
    exact_mod_cast hclogNat
  have hBq : (B : ℚ) ≤ (L : ℚ) + (k : ℚ) * ((1 + ε / 12) * (L : ℚ)) := by
    have hseedq : (d₀ : ℚ) ≤ (L : ℚ) := by exact_mod_cast hseed
    have hkh := mul_le_mul_of_nonneg_left hδ (Nat.cast_nonneg k : (0 : ℚ) ≤ k)
    rw [hB]
    push_cast
    linarith
  have hLq : (14 : ℚ) ≤ (L : ℚ) := by exact_mod_cast (show 14 ≤ L by omega)
  have hKq : (0 : ℚ) ≤ k := Nat.cast_nonneg k
  have hLq0 : (0 : ℚ) ≤ L := Nat.cast_nonneg L
  have hseedTerm : 7 * (L : ℚ) ≤ (ε / 4) * (k : ℚ) * (L : ℚ) := by
    nlinarith [mul_le_mul_of_nonneg_right hK hLq0]
  have hextraTerm : 2 * (k : ℚ) ≤ (ε / 4) * (k : ℚ) * (L : ℚ) := by
    nlinarith [mul_le_mul_of_nonneg_left hLε hKq]
  change (Nat.clog 2 T : ℚ) ≤ (6 + ε) * (k : ℚ) * (L : ℚ)
  nlinarith

/-- One explicit source-size cutoff supplies both the public admissibility
check and the logarithmic-overhead cutoff for every eligible graph. -/
def graphSizeCutoff (Δ : ℕ) (γ ε : ℚ) : ℕ :=
  max (CompletePublicScheduleScratch.sizeThreshold Δ γ)
    (2 ^ lengthCutoff Δ γ ε)

theorem at_graph_size_printed_entries_le_six_plus (n m Δ k : ℕ) [NeZero n]
    (γ ε : ℚ) (edge : Fin m → Bool → Fin n)
    (hγ : 0 < γ) (hΔ : 0 < Δ) (hε : 0 < ε)
    (hincident : ∀ v, ∃ e b, edge e b = v)
    (hdegree : ∀ v, SourceItems.degree edge v ≤ Δ)
    (hn : graphSizeCutoff Δ γ ε ≤ n)
    (hk : iterationCutoff ε ≤ k) :
    (Nat.clog 2 (sourceRows (Nat.clog 2 n)
      (restorationDepth (Nat.clog 2 n))
      (coverDepth n m (Nat.clog 2 n) Δ γ) k *
      sourceCols (Nat.clog 2 n)
        (restorationDepth (Nat.clog 2 n))
        (coverDepth n m (Nat.clog 2 n) Δ γ) k) : ℚ) ≤
      (6 + ε) * (k : ℚ) * (Nat.clog 2 n : ℚ) := by
  have hsize : CompletePublicScheduleScratch.sizeThreshold Δ γ ≤ n := by
    unfold graphSizeCutoff at hn
    omega
  have hL : lengthCutoff Δ γ ε ≤ Nat.clog 2 n := by
    have hpow : 2 ^ lengthCutoff Δ γ ε ≤ n := by
      unfold graphSizeCutoff at hn
      omega
    have hc := Nat.clog_mono_right 2 hpow
    simpa only [Nat.clog_pow 2 (lengthCutoff Δ γ ε) (by decide)] using hc
  exact printed_entries_le_six_plus n m (Nat.clog 2 n) Δ k γ ε edge
    hγ hΔ hε hincident hdegree
    (ParameterizedCanonicalSource.checksAtSize Δ γ edge
      hγ hΔ hincident hdegree hsize) hL hk

end Paper2.SharpOutputSize
