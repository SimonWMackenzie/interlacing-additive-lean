import CurrentAdditive.CylinderMatrixClock

/-! Exact interface between the semantic v27 cylinder matrix and the physical
matrix serializer, conditional on the Boolean entries being supplied. -/

namespace CurrentAdditive.CylinderPreparedMatrixBridge

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachine
open CurrentAdditive.CylinderFeatureCodec
open CurrentAdditive.CylinderRowSerializer
open CurrentAdditive.CylinderMatrixSerializer

def preparedRows (q D : Nat) (alphabet : Array Nat)
    (source : Array ((Fin q → Nat) × ℚ)) : List (List Bool) :=
  (cylinders q D alphabet source).toList.map
    (fun row => row.toList.map (fun x => decide (x ≠ 0)))

theorem encodedCell_decide_ne (x : ℚ) :
    encodedCell (decide (x ≠ 0)) = encodeZeroOne x := by
  by_cases hx : x = 0
  · simp [encodedCell, encodeZeroOne, hx]
  · simp [encodedCell, encodeZeroOne, hx]

private theorem encodedRow_prepare (row : Array ℚ) :
    encodedRow (row.toList.map (fun x => decide (x ≠ 0))) =
      SourceListEncoding.encode (row.toList.map encodeZeroOne) := by
  have h : ∀ xs : List ℚ,
      (xs.map (fun x => decide (x ≠ 0))).map encodedCell =
        xs.map encodeZeroOne := by
    intro xs
    induction xs with
    | nil => rfl
    | cons x xs ih => simp only [List.map_cons, encodedCell_decide_ne, ih]
  exact congrArg SourceListEncoding.encode (h row.toList)

theorem preparedRows_encoding (q D : Nat) (alphabet : Array Nat)
    (source : Array ((Fin q → Nat) × ℚ)) :
    encodedMatrix (preparedRows q D alphabet source) =
      cylinderMatrixBits q D alphabet source := by
  change SourceListEncoding.encode
      (((cylinders q D alphabet source).toList.map
        (fun row => row.toList.map (fun x => decide (x ≠ 0)))).map encodedRow) =
    SourceListEncoding.encode
      ((cylinders q D alphabet source).toList.map
        (fun row => SourceListEncoding.encode (row.toList.map encodeZeroOne)))
  congr 1
  induction (cylinders q D alphabet source).toList with
  | nil => rfl
  | cons row rows ih => simp only [List.map_cons, encodedRow_prepare, ih]

theorem prepared_matrix_outputs (q D : Nat) (alphabet : Array Nat)
    (source : Array ((Fin q → Nat) × ℚ)) :
    matrixMachine.OutputsWithin
      (SourceListEncoding.encode
        (rawRows (preparedRows q D alphabet source)))
      (cylinderMatrixBits q D alphabet source)
      (matrixClock (preparedRows q D alphabet source)) := by
  rw [← preparedRows_encoding]
  exact matrix_outputs _

#print axioms prepared_matrix_outputs

end CurrentAdditive.CylinderPreparedMatrixBridge
