import Paper2.TotalFiniteConstructor
import Paper2.FairBitCap

/-! Uniform finite bit-count and printed-entry bounds for the one selected
output. These are cardinal/length bounds, not running-time bounds. -/

namespace Paper2.TotalFiniteResourcesScratch

open SourceProfileParameters SourceRecursiveNoSampling
  ParameterizedCanonicalSource TotalFiniteConstructorScratch

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000

def resourceBound (n k : ℕ) : ℕ := (n + 2) ^ (160 * (k + 1))

private theorem dyadic_le_base_square (n : ℕ) (hn : 0 < n) :
    2 ^ Nat.clog 2 n ≤ (n + 2) ^ 2 := by
  have h := CappedSampler.ticketSize_le_twice n hn
  change 2 ^ Nat.clog 2 n ≤ 2 * n at h
  have hpoly : 2 * n ≤ (n + 2) ^ 2 := by nlinarith
  exact h.trans hpoly

private theorem scheduled_pow_le (n k c : ℕ) (hn : 0 < n)
    (hc : 2 * c ≤ 160) :
    2 ^ (c * (k + 1) * Nat.clog 2 n) ≤ resourceBound n k := by
  have hbase := dyadic_le_base_square n hn
  have hpow := Nat.pow_le_pow_left hbase (c * (k + 1))
  have hexp : 2 * (c * (k + 1)) ≤ 160 * (k + 1) := by
    calc
      _ = (2 * c) * (k + 1) := by ring
      _ ≤ 160 * (k + 1) := Nat.mul_le_mul_right (k + 1) hc
  calc
    _ = (2 ^ Nat.clog 2 n) ^ (c * (k + 1)) := by
      rw [← pow_mul]
      congr 1
      ring
    _ ≤ ((n + 2) ^ 2) ^ (c * (k + 1)) := hpow
    _ = (n + 2) ^ (2 * (c * (k + 1))) := by rw [← pow_mul]
    _ ≤ resourceBound n k := by
      dsimp [resourceBound]
      exact pow_le_pow_right₀ (by omega) hexp

private theorem fallback_entries_le (n m k : ℕ) (hn : 0 < n)
    (edge : Fin m → Bool → Fin n) (hk : 1 ≤ k) :
    FiniteFallbackOutput.rows k * FiniteFallbackOutput.cols k ≤
      resourceBound n k := by
  have hsize := FiniteFallbackOutput.fallback_bits_length_le edge k hk
  rw [FiniteFallbackOutput.fallbackTable_bits_length] at hsize
  have hbase : 2 ≤ n + 2 := by omega
  have hpow : 2 ^ (2 * k) ≤ (n + 2) ^ (2 * k) :=
    Nat.pow_le_pow_left hbase _
  have hexp : 2 * k ≤ 160 * (k + 1) := by omega
  exact hsize.trans (hpow.trans (by
    dsimp [resourceBound]
    exact pow_le_pow_right₀ (by omega) hexp))

/-- Counts announced by `select` are bounded uniformly in the source size
and level; no graph promise is used to decide the branch. -/
theorem selected_announced_counts_le {n m : ℕ} (hn : 0 < n)
    (edge : Fin m → Bool → Fin n) (Δ : ℕ) (γ : ℚ)
    (k : ℕ) (hk : 1 ≤ k) :
    let o := select hn edge Δ γ k
    o.rows * o.cols ≤ resourceBound n k ∧
    o.inputBits ≤ resourceBound n k := by
  dsimp only
  by_cases hc : CompletePublicScheduleScratch.Checks
      (V := Fin n) (E := Fin m) (Nat.clog 2 n) Δ γ
  · letI : NeZero n := ⟨Nat.ne_of_gt hn⟩
    rw [select_good hn edge Δ γ k hc]
    constructor
    · have h := ScheduledOutputBounds.checked_entries_le
        (Nat.clog 2 n) Δ γ hc k
      have hpoly := scheduled_pow_le n k 58 hn (by omega)
      simpa only [scheduledOutput] using h.trans hpoly
    · have h := FairBitCap.scheduled_inputBitCount_le
        (Nat.clog 2 n) Δ γ hc k
      have hpoly := scheduled_pow_le n k 80 hn (by omega)
      simpa only [scheduledOutput] using h.trans hpoly
  · rw [select_bad hn edge Δ γ k hc]
    constructor
    · simpa only [fallbackOutput] using fallback_entries_le n m k hn edge hk
    · simp [fallbackOutput, resourceBound]

/-- The one-vertex graph necessarily uses fallback: its dyadic source
parameter is zero, whereas every checked schedule requires `L≥16`. -/
theorem one_vertex_check_fails (m Δ : ℕ) (γ : ℚ) :
    ¬ CompletePublicScheduleScratch.Checks
      (V := Fin 1) (E := Fin m) (Nat.clog 2 1) Δ γ := by
  intro hc
  simp [CompletePublicScheduleScratch.Checks] at hc

/-- Literal list lengths equal the selected public counts on every tape,
including the all-zero scheduled abort. Both counts, and their sum, obey
the uniform graph-size bound. -/
theorem selected_actual_lengths_le {n m : ℕ} (hn : 0 < n)
    (edge : Fin m → Bool → Fin n) (Δ : ℕ) (γ : ℚ)
    (k : ℕ) (hk : 1 ≤ k)
    (loopless : ∀ e, edge e false ≠ edge e true)
    (hdegree : ∀ v, SourceItems.degree edge v ≤ Δ)
    (hγ : 0 < γ) (hΔ : 0 < Δ) (hm : 0 < m) :
    let o := select hn edge Δ γ k
    ∀ t : o.Tape,
      (o.table t).bits.length = o.rows * o.cols ∧
      (o.tapeBits t).length = o.inputBits ∧
      (o.table t).bits.length ≤ resourceBound n k ∧
      (o.tapeBits t).length ≤ resourceBound n k ∧
      (o.table t).bits.length + (o.tapeBits t).length ≤
        2 * resourceBound n k := by
  dsimp only
  have hcounts := selected_announced_counts_le hn edge Δ γ k hk
  have hlengths := TotalFiniteConstructorScratch.selected_exact_lengths
    hn edge Δ γ k loopless hdegree hγ hΔ hm
  intro t
  have h := hlengths t
  have htable : ((select hn edge Δ γ k).table t).bits.length ≤
      resourceBound n k := h.1.le.trans hcounts.1
  have htape : ((select hn edge Δ γ k).tapeBits t).length ≤
      resourceBound n k := h.2.le.trans hcounts.2
  exact ⟨h.1, h.2, htable, htape, by omega⟩


end Paper2.TotalFiniteResourcesScratch
