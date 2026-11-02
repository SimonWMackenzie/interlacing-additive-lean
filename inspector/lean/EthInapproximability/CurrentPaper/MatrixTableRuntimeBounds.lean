import EthInapproximability.CurrentPaper.MatrixUniformEntryBounds
import EthInapproximability.CurrentPaper.MatrixTableWriter

/-! # A uniform bound for the actual row-major output loop

The entry budget below is the concrete bound used by the full entry runtime.
This arithmetic lemma charges all row/column administration and final output
reversal as well as all calls of that evaluator.
-/

namespace EthInapproximability.CurrentPaper.MatrixTableRuntimeBounds

open MatrixUniformEntryBounds

def bound (a d N₁ N₂ n : ℕ) : ℕ := 4194304 * scale a d N₁ N₂ n ^ 17

theorem writer_bound (a d N₁ N₂ n : ℕ) :
    MatrixTableWriter.writerBound (4 * N₂ + n) (8 * (d * N₁) ^ 4)
      (65536 * scale a d N₁ N₂ n ^ 8) ≤ bound a d N₁ N₂ n := by
  let S := scale a d N₁ N₂ n
  have hS := (scale_bounds a d N₁ N₂ n).1
  have hr := rows_bound a d N₁ N₂ n
  have hc := columns_bound a d N₁ N₂ n
  have h08 : 1 ≤ S ^ 8 := Nat.one_le_pow _ _ hS
  have h816 : S ^ 8 ≤ S ^ 16 := Nat.pow_le_pow_right hS (by decide : 8 ≤ 16)
  have h016 : 1 ≤ S ^ 16 := Nat.one_le_pow _ _ hS
  have h017 : 1 ≤ S ^ 17 := Nat.one_le_pow _ _ hS
  have hT : 65536 * S ^ 8 + 2 ≤ 65538 * S ^ 8 := by omega
  have hprod := Nat.mul_le_mul hc hT
  have hpow : S ^ 8 * S ^ 8 = S ^ 16 := by ring
  have hinside : (8 * (d * N₁) ^ 4) * (65536 * S ^ 8 + 2) +
      4 * (8 * (d * N₁) ^ 4) + 8 ≤ 524352 * S ^ 16 := by
    change 8 * (d * N₁) ^ 4 * (65536 * S ^ 8 + 2) ≤
      (8 * S ^ 8) * (65538 * S ^ 8) at hprod
    change 8 * (d * N₁) ^ 4 ≤ 8 * S ^ 8 at hc
    nlinarith
  have hfull := Nat.mul_le_mul hr hinside
  change (4 * N₂ + n) * _ ≤ (5 * S) * (524352 * S ^ 16) at hfull
  change (4 * N₂ + n) * ((8 * (d * N₁) ^ 4) * (65536 * S ^ 8 + 2) +
    4 * (8 * (d * N₁) ^ 4) + 8) + 5 ≤ 4194304 * S ^ 17
  nlinarith [show S * S ^ 16 = S ^ 17 by ring]

end EthInapproximability.CurrentPaper.MatrixTableRuntimeBounds
