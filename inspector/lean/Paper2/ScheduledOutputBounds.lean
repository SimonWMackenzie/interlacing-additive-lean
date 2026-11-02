import Paper2.ParameterizedCanonicalSource
import Paper2.ReductionDimensions

/-! Output-entry size for the literal checked public source schedule.
This does not bound the time needed to produce the table. -/

namespace Paper2.ScheduledOutputBounds

open SourceProfileParameters SourceRecursiveNoSampling
  ParameterizedCanonicalSource

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000

/-- Every successful public check gives the exact uniform finite bound on
the scheduled number of printed Boolean entries. -/
theorem checked_entries_le {n m : ℕ} [NeZero n]
    (L Δ : ℕ) (γ : ℚ)
    (hc : CompletePublicScheduleScratch.Checks
      (V := Fin n) (E := Fin m) L Δ γ) (k : ℕ) :
    sourceRows L (restorationDepth L) (coverDepth n m L Δ γ) k *
      sourceCols L (restorationDepth L) (coverDepth n m L Δ γ) k ≤
      2 ^ (58 * (k + 1) * L) := by
  have hc' := hc
  rcases hc' with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
    hover, hL, hseed⟩
  let d₀ := LookupSeed.exponent L + 1
  let h := SourceOverheadBounds.overhead
    (V := Fin n) (E := Fin m) L Δ γ
  have hL1 : 1 ≤ L := by omega
  have hbudget : sourceBudget L (restorationDepth L)
      (coverDepth n m L Δ γ) k = d₀ + k * h := by
    dsimp [sourceBudget, d₀, h, SourceOverheadBounds.overhead,
      restorationDepth, coverDepth]
  have hcost : sourceCost L (restorationDepth L)
      (coverDepth n m L Δ γ) k = d₀ + k * h + k := by
    dsimp [sourceCost, d₀, h, SourceOverheadBounds.overhead,
      restorationDepth, coverDepth]
    ring
  have hbound := ReductionDimensions.entries_uniform_bound
    d₀ h k L hseed hover hL1
  rw [← hcost, ← hbudget] at hbound
  change sourceRows L (restorationDepth L)
      (coverDepth n m L Δ γ) k *
    sourceCols L (restorationDepth L)
      (coverDepth n m L Δ γ) k ≤ _ at hbound
  exact hbound

/-- The graph-size cutoff proves the same exact public entry bound with
`L = ⌈log₂ n⌉`, including all integer ceilings. -/
theorem at_size_entries_le {n m : ℕ} [NeZero n]
    (Δ : ℕ) (γ : ℚ) (edge : Fin m → Bool → Fin n)
    (hγ : 0 < γ) (hΔ : 0 < Δ)
    (hincident : ∀ v, ∃ e b, edge e b = v)
    (hdegree : ∀ v, SourceItems.degree edge v ≤ Δ)
    (hsize : CompletePublicScheduleScratch.sizeThreshold Δ γ ≤ n)
    (k : ℕ) :
    sourceRows (Nat.clog 2 n) (restorationDepth (Nat.clog 2 n))
        (coverDepth n m (Nat.clog 2 n) Δ γ) k *
      sourceCols (Nat.clog 2 n) (restorationDepth (Nat.clog 2 n))
        (coverDepth n m (Nat.clog 2 n) Δ γ) k ≤
      2 ^ (58 * (k + 1) * Nat.clog 2 n) :=
  checked_entries_le (Nat.clog 2 n) Δ γ
    (checksAtSize Δ γ edge hγ hΔ hincident hdegree hsize) k

/-- A fully elementary polynomial form when the source has at least two
vertices. The exponent doubles because the dyadic ceiling obeys
`2^⌈log₂ n⌉ ≤ 2n ≤ n²`; it is not a sharp leading-coefficient claim. -/
theorem at_size_entries_le_poly {n m : ℕ} [NeZero n]
    (Δ : ℕ) (γ : ℚ) (edge : Fin m → Bool → Fin n)
    (hγ : 0 < γ) (hΔ : 0 < Δ)
    (hincident : ∀ v, ∃ e b, edge e b = v)
    (hdegree : ∀ v, SourceItems.degree edge v ≤ Δ)
    (hsize : CompletePublicScheduleScratch.sizeThreshold Δ γ ≤ n)
    (hn : 2 ≤ n) (k : ℕ) :
    sourceRows (Nat.clog 2 n) (restorationDepth (Nat.clog 2 n))
        (coverDepth n m (Nat.clog 2 n) Δ γ) k *
      sourceCols (Nat.clog 2 n) (restorationDepth (Nat.clog 2 n))
        (coverDepth n m (Nat.clog 2 n) Δ γ) k ≤
      n ^ (116 * (k + 1)) := by
  have hceil : 2 ^ Nat.clog 2 n ≤ n ^ 2 := by
    have h := CappedSampler.ticketSize_le_twice n (by omega)
    change 2 ^ Nat.clog 2 n ≤ 2 * n at h
    have htwice : 2 * n ≤ n ^ 2 := by nlinarith
    exact h.trans htwice
  calc
    _ ≤ 2 ^ (58 * (k + 1) * Nat.clog 2 n) :=
      at_size_entries_le Δ γ edge hγ hΔ hincident hdegree hsize k
    _ = (2 ^ Nat.clog 2 n) ^ (58 * (k + 1)) := by
      rw [← pow_mul]
      congr 1
      ring
    _ ≤ (n ^ 2) ^ (58 * (k + 1)) :=
      Nat.pow_le_pow_left hceil _
    _ = n ^ (116 * (k + 1)) := by
      rw [← pow_mul]
      congr 1
      ring

end Paper2.ScheduledOutputBounds


