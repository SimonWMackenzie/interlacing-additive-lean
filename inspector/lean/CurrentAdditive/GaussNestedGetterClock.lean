import CurrentAdditive.GaussNestedGetterRun
import CurrentAdditive.IndexedV2Clock

set_option maxHeartbeats 1000000

/-! A coarse cubic bound for the valid nested counted-V2 matrix selector.
The row word and both unary indices are bounded by the original matrix
encoding, so the two selector costs are charged to one input length. -/

namespace CurrentAdditive.GaussNestedGetterClock

open EthInapproximability.CurrentPaper
open CurrentAdditive.GaussListContext
open CurrentAdditive.GaussListContext.IndexedV2Clock

def clock (rowPre rowSuffix cellPre cellSuffix : List (List Bool))
    (cell : List Bool) : Nat :=
  let row := SourceListEncoding.encode (cellPre ++ cell :: cellSuffix)
  let matrix := SourceListEncoding.encode (rowPre ++ row :: rowSuffix)
  (2 * rowPre.length + 5 +
    (2 * matrix.length + 5 +
      (4 * (rowPre ++ row :: rowSuffix).length.bits.length + 6 +
        IndexedFieldProgram.fieldCost (rowPre ++ [row])))) + 1 +
  (2 * row.length + 5 +
    (4 * (cellPre ++ cell :: cellSuffix).length.bits.length + 6 +
      IndexedFieldProgram.fieldCost (cellPre ++ [cell])))

theorem clock_cubic (rowPre rowSuffix cellPre cellSuffix : List (List Bool))
    (cell : List Bool) :
    let row := SourceListEncoding.encode (cellPre ++ cell :: cellSuffix)
    let matrix := SourceListEncoding.encode (rowPre ++ row :: rowSuffix)
    clock rowPre rowSuffix cellPre cellSuffix cell ≤
      120 * (matrix.length + 1)^3 := by
  dsimp only
  let row := SourceListEncoding.encode (cellPre ++ cell :: cellSuffix)
  let matrix := SourceListEncoding.encode (rowPre ++ row :: rowSuffix)
  let N := matrix.length
  let R := row.length
  have hrow : R ≤ N := by
    have hitem := fields_item_length_le (rowPre ++ row :: rowSuffix)
      row (by simp)
    have hfields : (SourceListEncoding.fields
      (rowPre ++ row :: rowSuffix)).length ≤ N := by
      simp [N, matrix, SourceListEncoding.encode]
    exact hitem.trans hfields
  have hpre : rowPre.length ≤ N := by
    have hcount := fields_length_ge_count (rowPre ++ row :: rowSuffix)
    simp only [List.length_append, List.length_cons] at hcount
    have hfields : (SourceListEncoding.fields
      (rowPre ++ row :: rowSuffix)).length ≤ N := by
      simp [N, matrix, SourceListEncoding.encode]
    omega
  have hcellPre : cellPre.length ≤ R := by
    have hcount := fields_length_ge_count
      (cellPre ++ cell :: cellSuffix)
    simp only [List.length_append, List.length_cons] at hcount
    have hfields : (SourceListEncoding.fields
      (cellPre ++ cell :: cellSuffix)).length ≤ R := by
      simp [R, row, SourceListEncoding.encode]
    omega
  have houterBits :
      (rowPre ++ row :: rowSuffix).length.bits.length ≤ N := by
    have hb := bits_length_le (rowPre ++ row :: rowSuffix).length
    have hcount := fields_length_ge_count (rowPre ++ row :: rowSuffix)
    have hfields : (SourceListEncoding.fields
      (rowPre ++ row :: rowSuffix)).length ≤ N := by
      simp [N, matrix, SourceListEncoding.encode]
    omega
  have hinnerBits :
      (cellPre ++ cell :: cellSuffix).length.bits.length ≤ R := by
    have hb := bits_length_le (cellPre ++ cell :: cellSuffix).length
    have hcount := fields_length_ge_count
      (cellPre ++ cell :: cellSuffix)
    have hfields : (SourceListEncoding.fields
      (cellPre ++ cell :: cellSuffix)).length ≤ R := by
      simp [R, row, SourceListEncoding.encode]
    omega
  have houterCost := fieldCost_prefix_le
    (rowPre ++ [row]) rowSuffix
  have hinnerCost := fieldCost_prefix_le
    (cellPre ++ [cell]) cellSuffix
  have houterShape :
      (rowPre ++ [row]) ++ rowSuffix = rowPre ++ row :: rowSuffix := by
    simp [List.append_assoc]
  have hinnerShape :
      (cellPre ++ [cell]) ++ cellSuffix = cellPre ++ cell :: cellSuffix := by
    simp [List.append_assoc]
  rw [houterShape] at houterCost
  rw [hinnerShape] at hinnerCost
  have hcube : (R + 1)^3 ≤ (N + 1)^3 := by
    exact Nat.pow_le_pow_left (by omega) 3
  have hlin : N ≤ (N + 1)^3 := by
    nlinarith [sq_nonneg ((N : ℤ) + 1)]
  have hRlin : R ≤ (N + 1)^3 := hrow.trans hlin
  have hpos : 1 ≤ (N + 1)^3 := by
    nlinarith [sq_nonneg ((N : ℤ) + 1)]
  dsimp [clock, row, matrix, N, R] at *
  nlinarith

#print axioms clock_cubic

end CurrentAdditive.GaussNestedGetterClock
