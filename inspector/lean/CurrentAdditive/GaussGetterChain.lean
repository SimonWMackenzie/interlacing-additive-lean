import CurrentAdditive.GaussCellTransfer

set_option maxHeartbeats 1000000

/-! A charged sequential execution of the two checked fixed finite programs:
nested matrix selection and final physical cell transfer. -/

namespace CurrentAdditive.GaussGetterChain

open EthInapproximability.CurrentPaper
open CurrentAdditive.GaussListContext
open Turing BitMachineEncoding

theorem selected_transfer
    (rowPre rowSuffix cellPre cellSuffix : List (List Bool))
    (cell : List Bool) :
    let row := SourceListEncoding.encode (cellPre ++ cell :: cellSuffix)
    let matrix := SourceListEncoding.encode (rowPre ++ row :: rowSuffix)
    ∃ tSelect ≤
      (2 * rowPre.length + 5 +
        (2 * matrix.length + 5 +
          (4 * (rowPre ++ row :: rowSuffix).length.bits.length + 6 +
            IndexedFieldProgram.fieldCost (rowPre ++ [row])))) + 1 +
      (2 * row.length + 5 +
        (4 * (cellPre ++ cell :: cellSuffix).length.bits.length + 6 +
          IndexedFieldProgram.fieldCost (cellPre ++ [cell]))),
      let selected := GaussNestedGetter.run tSelect
        (GaussNestedGetter.firstFrame
          (GaussNestedGetter.inputForeign cellPre.length)
          (CylinderContextScanStep.initial matrix rowPre.length))
      selected.l = some (.inr (.inr .afterSecond)) ∧
      ∃ tTransfer ≤ row.length + 1 + (2 * cell.length + 3),
        ∃ S' : Fin 22 → List Bool,
          GaussCellTransfer.run tTransfer
            ⟨some .clear6, ((), none), selected.stk⟩ =
              ⟨some .done, ((), none), S'⟩ ∧
          S' 6 = cell ∧ S' 18 = cell ∧ S' 8 = matrix := by
  dsimp only
  obtain ⟨t, ht, he⟩ := GaussNestedGetter.nested_lookup
    rowPre rowSuffix cellPre cellSuffix cell
  let row := SourceListEncoding.encode (cellPre ++ cell :: cellSuffix)
  let matrix := SourceListEncoding.encode (rowPre ++ row :: rowSuffix)
  let afterRow := GaussNestedGetter.firstFrame
    (GaussNestedGetter.inputForeign cellPre.length)
    (GaussNestedGetter.firstDone matrix
      (SourceListEncoding.fields rowSuffix) row rowPre.length)
  let finalLocal : PreservingV2Program.Config :=
    ⟨none,
     PreservingV2Program.v2Control
       (IndexedV2Program.indexControl
         (SourceListMachineFields.coreControl (some true, false), none)),
     ![SourceListEncoding.fields cellSuffix, [], [], [], [],
       List.replicate cell.length true, cell, [], row, []]⟩
  let selected := GaussNestedGetter.run t
    (GaussNestedGetter.firstFrame
      (GaussNestedGetter.inputForeign cellPre.length)
      (CylinderContextScanStep.initial matrix rowPre.length))
  have hselected : selected =
      GaussNestedGetter.secondFrame afterRow.stk finalLocal := he
  have hcell : selected.stk 18 = cell := by
    rw [hselected]
    exact GaussNestedGetter.second_selected_cell _ _
  have htemp : selected.stk 14 = [] := by
    rw [hselected]
    exact BitMachineStackEmbedding.bank_at
      GaussNestedGetter.secondMap afterRow.stk finalLocal.stk 2
  have hrow : selected.stk 6 = row := by
    rw [hselected]
    exact BitMachineStackEmbedding.bank_at
      GaussNestedGetter.secondMap afterRow.stk finalLocal.stk 8
  have hmatrix : selected.stk 8 = matrix := by
    rw [hselected, GaussNestedGetter.second_preserves_matrix]
    exact BitMachineStackEmbedding.bank_at
      GaussNestedGetter.firstMap
      (GaussNestedGetter.inputForeign cellPre.length)
      (GaussNestedGetter.firstDone matrix
        (SourceListEncoding.fields rowSuffix) row rowPre.length).stk 8
  obtain ⟨u, hu, S', hrun, hout, hrestore, hpreserve⟩ :=
    GaussCellTransfer.transfer selected.stk cell hcell htemp
  refine ⟨t, ht, ?_, u, ?_, S', hrun, hout, hrestore, ?_⟩
  · change selected.l = _
    rw [hselected]
    rfl
  · simpa [hrow] using hu
  · exact hpreserve.trans hmatrix

#print axioms selected_transfer

end CurrentAdditive.GaussGetterChain
