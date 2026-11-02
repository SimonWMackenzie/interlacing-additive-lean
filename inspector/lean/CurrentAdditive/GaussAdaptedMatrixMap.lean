import CurrentAdditive.GaussUniformCellClock
import CurrentAdditive.GaussNestedMatrixMap

set_option maxHeartbeats 1000000

/-! The fixed two-level matrix writer on the uniform adapted cell requests. -/

namespace CurrentAdditive.GaussAdaptedMatrixMap

open CurrentAdditive.GaussNestedMatrixMap

def adaptedMatrix {m k : Nat} (B : Fin m → Fin k → ℚ)
    (r pivot : Fin m) (c : Fin k) : List (List (List Bool)) :=
  (List.finRange m).map fun i =>
    (List.finRange k).map
      (GaussUniformCellAlgebra.adaptedSourceCellPacket B r pivot c i)

theorem mapped_adapted_exact {m k : Nat}
    (B : Fin m → Fin k → ℚ) (r pivot : Fin m) (c : Fin k)
    (f : List Bool → List Bool)
    (hf : ∀ i j,
      f (GaussUniformCellAlgebra.adaptedSourceCellPacket B r pivot c i j) =
        CurrentAdditive.CodeDCodec.encodeRawRat
          (CurrentAdditive.GaussPhysical.rawOfRat
            (CurrentAdditive.SequentialTotality.clearTyped
              (CurrentAdditive.SequentialTotality.swapTyped B r pivot)
              r c i j))) :
    mappedNested f (adaptedMatrix B r pivot c) =
      CurrentAdditive.GaussPhysical.encodeTypedMatrix
        (CurrentAdditive.SequentialTotality.clearTyped
          (CurrentAdditive.SequentialTotality.swapTyped B r pivot) r c) := by
  simp [mappedNested, adaptedMatrix,
    CurrentAdditive.GaussPhysical.encodeTypedMatrix,
    CurrentAdditive.GaussPhysical.encodeRationalMatrix,
    CurrentAdditive.GaussPhysical.encodeMatrix,
    CurrentAdditive.GaussPhysical.encodeRow,
    CurrentAdditive.GaussPhysical.typedRows,
    CurrentAdditive.CodeDCodecV2.encodeItems,
    List.map_map, Function.comp_def, hf]

theorem physical_adapted_clear {m k : Nat}
    (B : Fin m → Fin k → ℚ) (r pivot : Fin m) (c : Fin k)
    (M : EthInapproximability.CurrentPaper.BitMachine.Machine)
    (f : List Bool → List Bool) (bound : List Bool → Nat)
    (hcell : ∀ i j,
      M.OutputsWithin
        (GaussUniformCellAlgebra.adaptedSourceCellPacket B r pivot c i j)
        (f (GaussUniformCellAlgebra.adaptedSourceCellPacket B r pivot c i j))
        (bound (GaussUniformCellAlgebra.adaptedSourceCellPacket B r pivot c i j)))
    (hf : ∀ i j,
      f (GaussUniformCellAlgebra.adaptedSourceCellPacket B r pivot c i j) =
        CurrentAdditive.CodeDCodec.encodeRawRat
          (CurrentAdditive.GaussPhysical.rawOfRat
            (CurrentAdditive.SequentialTotality.clearTyped
              (CurrentAdditive.SequentialTotality.swapTyped B r pivot)
              r c i j))) :
    (matrixMachine M).OutputsWithin
      (encodeNested (adaptedMatrix B r pivot c))
      (CurrentAdditive.GaussPhysical.encodeTypedMatrix
        (CurrentAdditive.SequentialTotality.clearTyped
          (CurrentAdditive.SequentialTotality.swapTyped B r pivot) r c))
      (matrixClock M f bound (adaptedMatrix B r pivot c)) := by
  have hrow : ∀ row ∈ adaptedMatrix B r pivot c,
      ∀ cell ∈ row, M.OutputsWithin cell (f cell) (bound cell) := by
    intro row hrow cell hmem
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hrow
    obtain ⟨j, _, rfl⟩ := List.mem_map.mp hmem
    exact hcell i j
  simpa only [mapped_adapted_exact B r pivot c f hf] using
    physical_nested_map M f bound (adaptedMatrix B r pivot c) hrow

theorem adapted_clock_le {m k : Nat}
    (B : Fin m → Fin k → ℚ) (r pivot : Fin m) (c : Fin k)
    (M : EthInapproximability.CurrentPaper.BitMachine.Machine)
    (f : List Bool → List Bool) (bound : List Bool → Nat)
    (L R T : Nat)
    (hin : ∀ i j,
      (GaussUniformCellAlgebra.adaptedSourceCellPacket B r pivot c i j).length ≤ L)
    (hout : ∀ i j,
      (f (GaussUniformCellAlgebra.adaptedSourceCellPacket B r pivot c i j)).length ≤ R)
    (htime : ∀ i j,
      bound (GaussUniformCellAlgebra.adaptedSourceCellPacket B r pivot c i j) ≤ T) :
    matrixClock M f bound (adaptedMatrix B r pivot c) ≤
      matrixTimeEnvelope M m k L R T := by
  apply matrixClock_le M f bound (adaptedMatrix B r pivot c) m k L R T
  · simp [adaptedMatrix]
  · intro row hrow
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hrow
    simp
  · intro row hrow x hx
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hrow
    obtain ⟨j, _, rfl⟩ := List.mem_map.mp hx
    exact hin i j
  · intro row hrow x hx
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hrow
    obtain ⟨j, _, rfl⟩ := List.mem_map.mp hx
    exact hout i j
  · intro row hrow x hx
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hrow
    obtain ⟨j, _, rfl⟩ := List.mem_map.mp hx
    exact htime i j

#print axioms mapped_adapted_exact
#print axioms physical_adapted_clear
#print axioms adapted_clock_le

end CurrentAdditive.GaussAdaptedMatrixMap
