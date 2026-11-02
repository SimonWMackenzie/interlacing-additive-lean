import CurrentAdditive.GaussGetterIntegrated

set_option maxHeartbeats 1000000

namespace CurrentAdditive.GaussGetterIntegratedClock

open EthInapproximability.CurrentPaper
open CurrentAdditive.GaussListContext
open CurrentAdditive.GaussListContext.IndexedV2Clock

theorem canonical_getter_cubic
    (rowPre rowSuffix cellPre cellSuffix : List (List Bool))
    (cell : List Bool) :
    let row := SourceListEncoding.encode (cellPre ++ cell :: cellSuffix)
    let matrix := SourceListEncoding.encode (rowPre ++ row :: rowSuffix)
    let initial := GaussGetterIntegrated.firstFrame
      (GaussNestedGetter.firstFrame
        (GaussNestedGetter.inputForeign cellPre.length)
        (CylinderContextScanStep.initial matrix rowPre.length))
    ∃ t ≤ 140 * (matrix.length + 1)^3,
      (GaussGetterIntegrated.run t initial).l = none ∧
      (GaussGetterIntegrated.run t initial).stk 6 = cell ∧
      (GaussGetterIntegrated.run t initial).stk 18 = cell ∧
      (GaussGetterIntegrated.run t initial).stk 8 = matrix := by
  dsimp only
  let row := SourceListEncoding.encode (cellPre ++ cell :: cellSuffix)
  let matrix := SourceListEncoding.encode (rowPre ++ row :: rowSuffix)
  obtain ⟨t, ht, hlabel, hcell6, hcell18, hmatrix⟩ :=
    GaussGetterIntegrated.canonical_getter_bank6
      rowPre rowSuffix cellPre cellSuffix cell
  have hcubic := GaussNestedGetterClock.clock_cubic
    rowPre rowSuffix cellPre cellSuffix cell
  have hrow : row.length ≤ matrix.length := by
    have hitem := fields_item_length_le (rowPre ++ row :: rowSuffix)
      row (by simp)
    have hfields : (SourceListEncoding.fields
      (rowPre ++ row :: rowSuffix)).length ≤ matrix.length := by
      simp [matrix, SourceListEncoding.encode]
    exact hitem.trans hfields
  have hcell : cell.length ≤ row.length := by
    have hitem := fields_item_length_le
      (cellPre ++ cell :: cellSuffix) cell (by simp)
    have hfields : (SourceListEncoding.fields
      (cellPre ++ cell :: cellSuffix)).length ≤ row.length := by
      simp [row, SourceListEncoding.encode]
    exact hitem.trans hfields
  let N := matrix.length
  have hN : N ≤ (N + 1)^3 := by
    nlinarith [sq_nonneg ((N : ℤ) + 1)]
  have hpos : 1 ≤ (N + 1)^3 := by
    nlinarith [sq_nonneg ((N : ℤ) + 1)]
  refine ⟨t, ?_, hlabel, hcell6, hcell18, hmatrix⟩
  dsimp [row, matrix, N] at *
  nlinarith

#print axioms canonical_getter_cubic

end CurrentAdditive.GaussGetterIntegratedClock
