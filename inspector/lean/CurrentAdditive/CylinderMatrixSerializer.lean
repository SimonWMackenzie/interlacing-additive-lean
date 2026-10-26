import CurrentAdditive.CylinderRowSerializer

/-! A physical nested counted-list writer for a matrix whose Boolean cylinder
entries have already been evaluated.  The inner machine writes each rational
row, and the outer machine frames those rows in source-list order. -/

namespace CurrentAdditive.CylinderMatrixSerializer

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachine
open CurrentAdditive.CylinderRowSerializer

def rawRow (bits : List Bool) : List Bool :=
  SourceListEncoding.encode (rawBitItems bits)

def rawRows (rows : List (List Bool)) : List (List Bool) := rows.map rawRow

def decodedBits (item : List Bool) : List Bool :=
  ((SourceListEncoding.decode item).getD []).map (fun x => x.headD false)

@[simp] theorem decodedBits_rawRow (bits : List Bool) :
    decodedBits (rawRow bits) = bits := by
  simp [decodedBits, rawRow, rawBitItems,
    SourceListEncoding.decode_encode, List.map_map, Function.comp_def]

def rowOutput (item : List Bool) : List Bool :=
  encodedRow (decodedBits item)

noncomputable def rowBound (item : List Bool) : Nat :=
  rowClock (decodedBits item)

noncomputable def matrixMachine : Machine :=
  SourceListMachineOuterFramed.machine rowMachine

noncomputable def matrixClock (rows : List (List Bool)) : Nat :=
  SourceListMachineOuter.canonicalBound
    (SourceListMachineOuterFramed.itemMachine rowMachine)
    (rawRows rows)
    (SourceListMachineOuterFramed.framedOutput rowOutput)
    (SourceListMachineOuterFramed.framedBound rowOutput rowBound)

def encodedMatrix (rows : List (List Bool)) : List Bool :=
  SourceListEncoding.encode (rows.map encodedRow)

theorem matrix_outputs (rows : List (List Bool)) :
    matrixMachine.OutputsWithin
      (SourceListEncoding.encode (rawRows rows))
      (encodedMatrix rows) (matrixClock rows) := by
  have hrow : ∀ x ∈ rawRows rows,
      rowMachine.OutputsWithin x (rowOutput x) (rowBound x) := by
    intro x hx
    obtain ⟨bits, _, rfl⟩ := List.mem_map.mp hx
    rw [show rowOutput (rawRow bits) = encodedRow bits by
      simp [rowOutput], show rowBound (rawRow bits) = rowClock bits by
      simp [rowBound]]
    exact row_outputs bits
  have h := SourceListMachineOuterFramed.outputsWithin
    rowMachine (rawRows rows) rowOutput rowBound hrow
  have hmap : (rawRows rows).map rowOutput = rows.map encodedRow := by
    simp [rawRows, rowOutput, List.map_map]
  simpa only [matrixMachine, matrixClock, encodedMatrix, hmap] using h

#print axioms matrix_outputs

end CurrentAdditive.CylinderMatrixSerializer
