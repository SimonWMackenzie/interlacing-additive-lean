import CurrentAdditive.GaussAdaptedMatrixMap
import CurrentAdditive.GaussSwapIndexSpec

set_option maxHeartbeats 1000000

/-! Connect a selected nonzero pivot to the uniform physical matrix writer. -/

namespace CurrentAdditive.GaussAdaptedPivotStep

open EthInapproximability.CurrentPaper

theorem selected_pivot_numerator {m k : Nat}
    (B : Fin m → Fin k → ℚ) (r pivot : Fin m) (c : Fin k)
    (hp : CurrentAdditive.SequentialTotality.pivotTyped B r.val c = some pivot) :
    0 < EncodedCommunication.bitsValue
      (CurrentAdditive.GaussPhysical.rawOfRat
        (B (GaussCellSourceBridge.sourceRow r pivot r) c)).numerator := by
  have hnonzero := (CurrentAdditive.SequentialTotality.pivotTyped_spec
    B r.val c pivot hp).2
  rw [GaussSwapIndexSpec.sourceRow_current]
  apply CurrentAdditive.GaussPhysical.numerator_positive_of_nonzero_value
  intro hzero
  apply hnonzero
  simpa only [CurrentAdditive.GaussPhysical.rawOfRat_value] using hzero

theorem physical_pivot_step {m k : Nat}
    (s : CurrentAdditive.GaussControlTrace.State m k)
    (hr : s.r < m) (hc : s.c < k) (pivot : Fin m)
    (hp : CurrentAdditive.SequentialTotality.pivotTyped
      s.B s.r ⟨s.c, hc⟩ = some pivot)
    (M : BitMachine.Machine) (f : List Bool → List Bool)
    (bound : List Bool → Nat)
    (hcell : ∀ i j,
      M.OutputsWithin
        (GaussUniformCellAlgebra.adaptedSourceCellPacket
          s.B ⟨s.r, hr⟩ pivot ⟨s.c, hc⟩ i j)
        (f (GaussUniformCellAlgebra.adaptedSourceCellPacket
          s.B ⟨s.r, hr⟩ pivot ⟨s.c, hc⟩ i j))
        (bound (GaussUniformCellAlgebra.adaptedSourceCellPacket
          s.B ⟨s.r, hr⟩ pivot ⟨s.c, hc⟩ i j)))
    (hf : ∀ i j,
      f (GaussUniformCellAlgebra.adaptedSourceCellPacket
          s.B ⟨s.r, hr⟩ pivot ⟨s.c, hc⟩ i j) =
        CurrentAdditive.CodeDCodec.encodeRawRat
          (CurrentAdditive.GaussPhysical.rawOfRat
            (CurrentAdditive.SequentialTotality.clearTyped
              (CurrentAdditive.SequentialTotality.swapTyped
                s.B ⟨s.r, hr⟩ pivot) ⟨s.r, hr⟩ ⟨s.c, hc⟩ i j))) :
    (GaussNestedMatrixMap.matrixMachine M).OutputsWithin
      (GaussNestedMatrixMap.encodeNested
        (GaussAdaptedMatrixMap.adaptedMatrix
          s.B ⟨s.r, hr⟩ pivot ⟨s.c, hc⟩))
      (CurrentAdditive.GaussPhysical.encodeTypedMatrix
        (CurrentAdditive.GaussControlTrace.step s).B)
      (GaussNestedMatrixMap.matrixClock M f bound
        (GaussAdaptedMatrixMap.adaptedMatrix
          s.B ⟨s.r, hr⟩ pivot ⟨s.c, hc⟩)) := by
  have h := GaussAdaptedMatrixMap.physical_adapted_clear
    s.B ⟨s.r, hr⟩ pivot ⟨s.c, hc⟩ M f bound hcell hf
  simpa [CurrentAdditive.GaussControlTrace.step, hr, hc, hp,
    CurrentAdditive.MaterializedGauss.materialize_eq] using h

#print axioms selected_pivot_numerator
#print axioms physical_pivot_step

end CurrentAdditive.GaussAdaptedPivotStep
