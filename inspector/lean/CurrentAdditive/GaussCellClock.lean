import CurrentAdditive.GaussCellSpec
import CurrentAdditive.GaussClock

namespace CurrentAdditive.GaussPhysical

open CurrentAdditive.CodeDCodec
open EthInapproximability.CurrentPaper.BitMachineBankCodec

/-- The complete physical input packet for one clear-cell update is linear
in the four canonical rational operands. -/
theorem cellPacket_length (pivotRow : Bool)
    (current column row pivot : RawRat) (S : ℕ)
    (hcurrent : (encodeRawRat current).length ≤ 4 * S + 5)
    (hcolumn : (encodeRawRat column).length ≤ 4 * S + 5)
    (hrow : (encodeRawRat row).length ≤ 4 * S + 5)
    (hpivot : (encodeRawRat pivot).length ≤ 4 * S + 5) :
    (cellPacket pivotRow current column row pivot).length ≤ 32 * S + 54 := by
  simp only [cellPacket, encode_length]
  simp [cellBank, Fin.sum_univ_succ]
  omega

theorem canonicalCellPacket_length (pivotRow : Bool)
    (current column row pivot : ℚ) (S : ℕ)
    (hnc : Nat.size current.num.natAbs ≤ S) (hdc : Nat.size current.den ≤ S)
    (hncol : Nat.size column.num.natAbs ≤ S) (hdcol : Nat.size column.den ≤ S)
    (hnr : Nat.size row.num.natAbs ≤ S) (hdr : Nat.size row.den ≤ S)
    (hnp : Nat.size pivot.num.natAbs ≤ S) (hdp : Nat.size pivot.den ≤ S) :
    (cellPacket pivotRow (rawOfRat current) (rawOfRat column)
      (rawOfRat row) (rawOfRat pivot)).length ≤ 32 * S + 54 := by
  apply cellPacket_length pivotRow _ _ _ _ S
  · exact rawOfRat_code_length current S hnc hdc
  · exact rawOfRat_code_length column S hncol hdcol
  · exact rawOfRat_code_length row S hnr hdr
  · exact rawOfRat_code_length pivot S hnp hdp

/-- Every packet used to clear a cell of the actual materialized Gauss
state has a cubic-in-row-count length bound, even when the matrix has an
arbitrary number of columns. -/
theorem actualGauss_cell_packet_length {m k : ℕ}
    (A : Matrix (Fin m) (Fin k) ℤ)
    (h01 : ∀ i j, A i j = 0 ∨ A i j = 1)
    (t : ℕ) (ht : t ≤ k) (r i : Fin m) (c j : Fin k) :
    let Aq : Fin m → Fin k → ℚ := fun i j => (A i j : ℚ)
    let B := (CurrentAdditive.EliminationEntryBounds.cursorAfter Aq t).B
    (cellPacket (decide (i = r))
      (rawOfRat (B i j)) (rawOfRat (B i c))
      (rawOfRat (B r j)) (rawOfRat (B r c))).length ≤
      32 * ((m + 3) * (m + 1) ^ 2 + 1) + 54 := by
  let Aq : Fin m → Fin k → ℚ := fun i j => (A i j : ℚ)
  let B := (CurrentAdditive.EliminationEntryBounds.cursorAfter Aq t).B
  let S := (m + 3) * (m + 1) ^ 2 + 1
  have hentry (i : Fin m) (j : Fin k) :
      Nat.size (B i j).den ≤ S ∧ Nat.size (B i j).num.natAbs ≤ S := by
    exact CurrentAdditive.EliminationEntryBounds.every_actual_step_entry_bits
      A h01 t ht i j
  apply canonicalCellPacket_length (decide (i = r)) _ _ _ _ S
  · exact (hentry i j).2
  · exact (hentry i j).1
  · exact (hentry i c).2
  · exact (hentry i c).1
  · exact (hentry r j).2
  · exact (hentry r j).1
  · exact (hentry r c).2
  · exact (hentry r c).1

end CurrentAdditive.GaussPhysical
