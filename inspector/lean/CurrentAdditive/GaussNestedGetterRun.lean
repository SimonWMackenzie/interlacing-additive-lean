import CurrentAdditive.GaussNestedGetter

set_option maxHeartbeats 1000000

namespace CurrentAdditive.GaussNestedGetter

open EthInapproximability.CurrentPaper
open CurrentAdditive.GaussListContext
open Turing Turing.TM2.Stmt BitMachineEncoding

theorem run_add {c c' : Config} {n : Nat}
    (h : run n c = c') (m : Nat) :
    run (n + m) c = run m c' := by
  rw [Nat.add_comm, run, Function.iterate_add_apply]
  exact congrArg (run m) h

theorem nested_lookup
    (rowPre rowSuffix cellPre cellSuffix : List (List Bool))
    (cell : List Bool) :
    let row := SourceListEncoding.encode (cellPre ++ cell :: cellSuffix)
    let matrix := SourceListEncoding.encode (rowPre ++ row :: rowSuffix)
    let afterRow := firstFrame (inputForeign cellPre.length)
      (firstDone matrix (SourceListEncoding.fields rowSuffix)
        row rowPre.length)
    ∃ t ≤
      (2 * rowPre.length + 5 +
        (2 * matrix.length + 5 +
          (4 * (rowPre ++ row :: rowSuffix).length.bits.length + 6 +
            IndexedFieldProgram.fieldCost (rowPre ++ [row])))) + 1 +
      (2 * row.length + 5 +
        (4 * (cellPre ++ cell :: cellSuffix).length.bits.length + 6 +
          IndexedFieldProgram.fieldCost (cellPre ++ [cell]))),
      run t (firstFrame (inputForeign cellPre.length)
        (CylinderContextScanStep.initial matrix rowPre.length)) =
      secondFrame afterRow.stk
        ⟨none,
         PreservingV2Program.v2Control
           (IndexedV2Program.indexControl
             (SourceListMachineFields.coreControl (some true, false), none)),
         ![SourceListEncoding.fields cellSuffix, [], [], [], [],
           List.replicate cell.length true, cell, [], row, []]⟩ := by
  dsimp only
  let row := SourceListEncoding.encode (cellPre ++ cell :: cellSuffix)
  let matrix := SourceListEncoding.encode (rowPre ++ row :: rowSuffix)
  let afterRow := firstFrame (inputForeign cellPre.length)
    (firstDone matrix (SourceListEncoding.fields rowSuffix)
      row rowPre.length)
  obtain ⟨u, hu, heRow⟩ := first_lookup rowPre row rowSuffix
    (inputForeign cellPre.length)
  have heRow' :
      run u (firstFrame (inputForeign cellPre.length)
        (CylinderContextScanStep.initial matrix rowPre.length)) = afterRow := by
    exact heRow
  have heBridge := after_first_step matrix
    (SourceListEncoding.fields rowSuffix) row rowPre.length cellPre.length
  obtain ⟨v, hv, heCell⟩ := second_lookup cellPre cell cellSuffix afterRow.stk
  have h1 := run_add heRow' 1
  have h2 : run (u + 1)
      (firstFrame (inputForeign cellPre.length)
        (CylinderContextScanStep.initial matrix rowPre.length)) =
      secondFrame afterRow.stk
        (PreservingV2Program.initial row cellPre.length) := by
    simpa [run] using h1.trans heBridge
  have h3 := (run_add h2 v).trans heCell
  refine ⟨u + 1 + v, ?_, ?_⟩
  · dsimp only [row, matrix] at hu hv ⊢
    omega
  · exact h3

theorem nested_lookup_cell_and_matrix
    (rowPre rowSuffix cellPre cellSuffix : List (List Bool))
    (cell : List Bool) :
    let row := SourceListEncoding.encode (cellPre ++ cell :: cellSuffix)
    let matrix := SourceListEncoding.encode (rowPre ++ row :: rowSuffix)
    ∃ t ≤
      (2 * rowPre.length + 5 +
        (2 * matrix.length + 5 +
          (4 * (rowPre ++ row :: rowSuffix).length.bits.length + 6 +
            IndexedFieldProgram.fieldCost (rowPre ++ [row])))) + 1 +
      (2 * row.length + 5 +
        (4 * (cellPre ++ cell :: cellSuffix).length.bits.length + 6 +
          IndexedFieldProgram.fieldCost (cellPre ++ [cell]))),
      (run t (firstFrame (inputForeign cellPre.length)
        (CylinderContextScanStep.initial matrix rowPre.length))).stk 18 = cell ∧
      (run t (firstFrame (inputForeign cellPre.length)
        (CylinderContextScanStep.initial matrix rowPre.length))).stk 8 = matrix := by
  dsimp only
  obtain ⟨t, ht, he⟩ := nested_lookup rowPre rowSuffix cellPre cellSuffix cell
  refine ⟨t, ht, ?_, ?_⟩
  · rw [he]
    exact second_selected_cell _ _
  · rw [he, second_preserves_matrix]
    exact BitMachineStackEmbedding.bank_at firstMap
      (inputForeign cellPre.length)
      (firstDone
        (SourceListEncoding.encode
          (rowPre ++ SourceListEncoding.encode
            (cellPre ++ cell :: cellSuffix) :: rowSuffix))
        (SourceListEncoding.fields rowSuffix)
        (SourceListEncoding.encode (cellPre ++ cell :: cellSuffix))
        rowPre.length).stk 8

#print axioms nested_lookup
#print axioms nested_lookup_cell_and_matrix

end CurrentAdditive.GaussNestedGetter
