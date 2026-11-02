import CurrentAdditive.GaussAdaptedPivotStep
import CurrentAdditive.GaussCellFullArithmeticClockScratch

set_option maxHeartbeats 2000000

/-! The named physical arithmetic callback runs at every cell of the named
two-level matrix writer, including the pivot row. -/

namespace CurrentAdditive.GaussUniformMatrixRun

open EthInapproximability.CurrentPaper

noncomputable def exponent : Nat :=
  19014 * (RationalSubtractCanonical.exponent + 1)

theorem uniform_cell_clock :
    ∃ (f : List Bool → List Bool) (C : Nat),
      GaussCellSubtractCall.machine.ComputesWithin f
        (fun n => C * (n+1)^exponent) ∧
      ∀ (flag : Bool) (current column row pivot : CodeDCodec.RawRat),
        current.Valid → column.Valid → row.Valid → pivot.Valid →
        0 < EncodedCommunication.bitsValue pivot.numerator →
        f (GaussUniformCellAlgebra.adaptedPacket
          flag current column row pivot) =
          CodeDCodec.encodeRawRat
            (GaussCellArithmeticTarget.cellRaw
              flag current column row pivot) := by
  obtain ⟨f,C,h⟩ :=
    GaussCellFullArithmeticClockScratch.full_machine_computes_polynomial
  refine ⟨f,C,?_,?_⟩
  · simpa only [exponent] using h
  intro flag current column row pivot hc hcol hr hp hnum
  obtain ⟨T,hvalid⟩ :=
    GaussUniformCellAlgebra.uniform_machine_outputs
      flag current column row pivot hc hcol hr hp hnum
  exact BitMachine.outputsWithin_unique GaussCellSubtractCall.machine
    (h _) hvalid

theorem physical_pivot_matrix_run {m k : Nat}
    (s : CurrentAdditive.GaussControlTrace.State m k)
    (hr : s.r < m) (hc : s.c < k) (pivot : Fin m)
    (hp : CurrentAdditive.SequentialTotality.pivotTyped
      s.B s.r ⟨s.c, hc⟩ = some pivot) :
    ∃ (f : List Bool → List Bool) (C : Nat),
      (GaussNestedMatrixMap.matrixMachine
        GaussCellSubtractCall.machine).OutputsWithin
        (GaussNestedMatrixMap.encodeNested
          (GaussAdaptedMatrixMap.adaptedMatrix
            s.B ⟨s.r, hr⟩ pivot ⟨s.c, hc⟩))
        (CurrentAdditive.GaussPhysical.encodeTypedMatrix
          (CurrentAdditive.GaussControlTrace.step s).B)
        (GaussNestedMatrixMap.matrixClock
          GaussCellSubtractCall.machine f
          (fun x => C*(x.length+1)^exponent)
          (GaussAdaptedMatrixMap.adaptedMatrix
            s.B ⟨s.r, hr⟩ pivot ⟨s.c, hc⟩)) := by
  obtain ⟨f,C,hclock,_⟩ := uniform_cell_clock
  refine ⟨f,C,?_⟩
  have hnum := GaussAdaptedPivotStep.selected_pivot_numerator
    s.B ⟨s.r, hr⟩ pivot ⟨s.c, hc⟩ hp
  apply GaussAdaptedPivotStep.physical_pivot_step
    s hr hc pivot hp GaussCellSubtractCall.machine f
    (fun x => C*(x.length+1)^exponent)
  · intro i j
    exact hclock _
  · intro i j
    obtain ⟨T,hvalid⟩ :=
      GaussUniformCellAlgebra.adapted_source_cell_outputs
        s.B ⟨s.r, hr⟩ pivot i ⟨s.c, hc⟩ j hnum
    exact BitMachine.outputsWithin_unique
      GaussCellSubtractCall.machine (hclock _) hvalid

#print axioms uniform_cell_clock
#print axioms physical_pivot_matrix_run

end CurrentAdditive.GaussUniformMatrixRun
