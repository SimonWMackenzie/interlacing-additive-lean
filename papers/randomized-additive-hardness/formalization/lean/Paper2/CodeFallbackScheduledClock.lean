import Paper2.CodeTableFallback
import Paper2.FairBitCap
import Mathlib.Tactic

/-! A private bound for the actual fixed zero-table writer on the checked
Paper 2 schedule. Source: frozen v12 Appendix D, `eq:generator-bound` and
the exhausted-cap fallback paragraph. This does not bound the interpreter. -/

namespace Paper2.CodeFallbackScheduledClock

open Paper2.SourceRecursiveNoSampling Paper2.ParameterizedCanonicalSource

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000

theorem writerBound_le_entries (r c : Nat) (hc : 1 ≤ c) :
    EthInapproximability.CurrentPaper.MatrixTableWriter.writerBound r c 1 ≤
      16 * (r * c + 1) := by
  dsimp [EthInapproximability.CurrentPaper.MatrixTableWriter.writerBound]
  nlinarith

/-- Dimension form: no lower bound on the column count is needed. -/
theorem writerBound_le_dims (r c E : Nat) (hr : r ≤ E) (hc : c ≤ E)
    (hE : 1 ≤ E) :
    EthInapproximability.CurrentPaper.MatrixTableWriter.writerBound r c 1 ≤
      20 * E ^ 2 := by
  dsimp [EthInapproximability.CurrentPaper.MatrixTableWriter.writerBound]
  have hrc : r * c ≤ E * E := Nat.mul_le_mul hr hc
  have hE2 : E ≤ E * E := by nlinarith
  have hsq : E ^ 2 = E * E := by ring
  rw [hsq]
  nlinarith

/-- The fallback writer bound at the exact scheduled dimensions: the row
count is `sourceRows ...` and the column count `sourceCols ...`, the
prescribed sample counts of the checked schedule. -/
theorem scheduled_writerBound_le {n m : Nat} [NeZero n]
    (L Δ : Nat) (γ : ℚ)
    (hc : Paper2.CompletePublicScheduleScratch.Checks
      (V := Fin n) (E := Fin m) L Δ γ) (k : Nat) :
    EthInapproximability.CurrentPaper.MatrixTableWriter.writerBound
      (sourceRows L (restorationDepth L) (coverDepth n m L Δ γ) k)
      (sourceCols L (restorationDepth L) (coverDepth n m L Δ γ) k) 1 ≤
      2 ^ (64 * (k + 1) * L) := by
  let T := (k + 1) * L
  have hL : 16 ≤ L := by
    rcases hc with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hL, _⟩
    exact hL
  have hT : 1 ≤ T := by
    have hp : 0 < (k + 1) * L := Nat.mul_pos (by omega) (by omega)
    dsimp [T]; omega
  obtain ⟨hx, hy⟩ := FairBitCap.scheduled_each_dimension_le L Δ γ hc k
  have he : 29 * (k + 1) * L = 29 * T := by dsimp [T]; ring
  rw [he] at hx hy
  have hE : 1 ≤ 2 ^ (29 * T) := Nat.one_le_two_pow
  have hw := writerBound_le_dims _ _ (2 ^ (29 * T)) hx hy hE
  have hsq : (2 ^ (29 * T)) ^ 2 = 2 ^ (58 * T) := by
    rw [← pow_mul]; congr 1; ring
  have h32 : 20 * 2 ^ (58 * T) ≤ 2 ^ (64 * T) := by
    have h5 : 2 ^ 5 ≤ 2 ^ (6 * T) :=
      pow_le_pow_right₀ (by decide : 1 ≤ (2:Nat)) (by omega)
    calc
      20 * 2 ^ (58 * T) ≤ 2 ^ 5 * 2 ^ (58 * T) := by
        apply Nat.mul_le_mul_right; norm_num
      _ ≤ 2 ^ (6 * T) * 2 ^ (58 * T) := Nat.mul_le_mul_right _ h5
      _ = 2 ^ (64 * T) := by rw [← pow_add]; congr 1; ring
  have he64 : 64 * (k + 1) * L = 64 * T := by dsimp [T]; ring
  rw [he64]
  rw [hsq] at hw
  exact hw.trans h32

#print axioms writerBound_le_entries
#print axioms writerBound_le_dims
#print axioms scheduled_writerBound_le

end Paper2.CodeFallbackScheduledClock
