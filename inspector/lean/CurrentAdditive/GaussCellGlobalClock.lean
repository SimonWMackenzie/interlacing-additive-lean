import CurrentAdditive.GaussMatrixClockPolynomial

/-! Fixed witnesses for the one arithmetic program's all-input clock. -/

namespace CurrentAdditive.GaussCellGlobalClock

open EthInapproximability.CurrentPaper

noncomputable def result : List Bool → List Bool :=
  Classical.choose GaussUniformMatrixRun.uniform_cell_clock

noncomputable def coefficient : Nat :=
  Classical.choose
    (Classical.choose_spec GaussUniformMatrixRun.uniform_cell_clock)

theorem computes :
    GaussCellSubtractCall.machine.ComputesWithin result
      (fun n => coefficient*(n+1)^GaussUniformMatrixRun.exponent) := by
  exact (Classical.choose_spec
    (Classical.choose_spec GaussUniformMatrixRun.uniform_cell_clock)).1

theorem adapted_exact (flag : Bool)
    (current column row pivot : CodeDCodec.RawRat)
    (hc : current.Valid) (hcol : column.Valid)
    (hr : row.Valid) (hp : pivot.Valid)
    (hnum : 0 < EncodedCommunication.bitsValue pivot.numerator) :
    result (GaussUniformCellAlgebra.adaptedPacket
      flag current column row pivot) =
      CodeDCodec.encodeRawRat
        (GaussCellArithmeticTarget.cellRaw flag current column row pivot) := by
  exact (Classical.choose_spec
    (Classical.choose_spec GaussUniformMatrixRun.uniform_cell_clock)).2
      flag current column row pivot hc hcol hr hp hnum

#print axioms computes
#print axioms adapted_exact

end CurrentAdditive.GaussCellGlobalClock
