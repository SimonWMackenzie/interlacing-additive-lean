import CurrentAdditive.GaussCellSubtractCall

/-! A single subtraction formula for pivot and nonpivot Gauss cells. -/

namespace CurrentAdditive.GaussUniformCellAlgebra

open CurrentAdditive.CodeDCodec

def adaptedCurrent (flag : Bool) (current : RawRat) : RawRat :=
  if flag then CodeDCanonicalSource.rawOfRat 0 else current

def adaptedColumn (flag : Bool) (column : RawRat) : RawRat :=
  if flag then CodeDCanonicalSource.rawOfRat (-1) else column

def adaptedPacket (flag : Bool) (current column row pivot : RawRat) : List Bool :=
  GaussPhysical.cellPacket false
    (adaptedCurrent flag current) (adaptedColumn flag column) row pivot

theorem adapted_current_valid (flag : Bool) (current : RawRat)
    (hcurrent : current.Valid) : (adaptedCurrent flag current).Valid := by
  cases flag <;> simp [adaptedCurrent, hcurrent,
    CodeDCanonicalSource.rawOfRat_valid]

theorem adapted_column_valid (flag : Bool) (column : RawRat)
    (hcolumn : column.Valid) : (adaptedColumn flag column).Valid := by
  cases flag <;> simp [adaptedColumn, hcolumn,
    CodeDCanonicalSource.rawOfRat_valid]

theorem adapted_difference (flag : Bool)
    (current column row pivot : RawRat) :
    GaussCellArithmeticTarget.differenceRaw
      (adaptedCurrent flag current) (adaptedColumn flag column) row pivot =
    GaussCellArithmeticTarget.cellRaw flag current column row pivot := by
  cases flag with
  | false => rfl
  | true =>
      unfold adaptedCurrent adaptedColumn
      simp only [ite_true, GaussCellArithmeticTarget.differenceRaw,
        GaussCellArithmeticTarget.productRaw,
        GaussCellArithmeticTarget.quotientRaw,
        GaussCellArithmeticTarget.cellRaw,
        CodeDCanonicalSource.rawOfRat_value]
      congr 1
      ring

theorem uniform_machine_outputs (flag : Bool)
    (current column row pivot : RawRat)
    (hcurrent : current.Valid) (hcolumn : column.Valid)
    (hrow : row.Valid) (hpivot : pivot.Valid)
    (hnum : 0 < EthInapproximability.CurrentPaper.EncodedCommunication.bitsValue
      pivot.numerator) :
    ∃ T, GaussCellSubtractCall.machine.OutputsWithin
      (adaptedPacket flag current column row pivot)
      (encodeRawRat (GaussCellArithmeticTarget.cellRaw
        flag current column row pivot)) T := by
  obtain ⟨T,h⟩ := GaussCellSubtractCall.outputs_cell
    (adaptedCurrent flag current) (adaptedColumn flag column)
    row pivot (adapted_current_valid flag current hcurrent)
    (adapted_column_valid flag column hcolumn) hrow hpivot hnum
  refine ⟨T, ?_⟩
  simpa only [adaptedPacket, adapted_difference] using h

def adaptedSourceCellPacket {m k : Nat} (B : Fin m → Fin k → ℚ)
    (r pivot : Fin m) (c : Fin k) (i : Fin m) (j : Fin k) : List Bool :=
  adaptedPacket (decide (i = r))
    (GaussPhysical.rawOfRat
      (B (GaussCellSourceBridge.sourceRow r pivot i) j))
    (GaussPhysical.rawOfRat
      (B (GaussCellSourceBridge.sourceRow r pivot i) c))
    (GaussPhysical.rawOfRat
      (B (GaussCellSourceBridge.sourceRow r pivot r) j))
    (GaussPhysical.rawOfRat
      (B (GaussCellSourceBridge.sourceRow r pivot r) c))

theorem adapted_source_cell_outputs {m k : Nat}
    (B : Fin m → Fin k → ℚ) (r pivot i : Fin m) (c j : Fin k)
    (hnum : 0 < EthInapproximability.CurrentPaper.EncodedCommunication.bitsValue
      (GaussPhysical.rawOfRat
        (B (GaussCellSourceBridge.sourceRow r pivot r) c)).numerator) :
    ∃ T, GaussCellSubtractCall.machine.OutputsWithin
      (adaptedSourceCellPacket B r pivot c i j)
      (encodeRawRat (GaussPhysical.rawOfRat
        (SequentialTotality.clearTyped
          (SequentialTotality.swapTyped B r pivot) r c i j))) T := by
  let current := GaussPhysical.rawOfRat
    (B (GaussCellSourceBridge.sourceRow r pivot i) j)
  let column := GaussPhysical.rawOfRat
    (B (GaussCellSourceBridge.sourceRow r pivot i) c)
  let row := GaussPhysical.rawOfRat
    (B (GaussCellSourceBridge.sourceRow r pivot r) j)
  let p := GaussPhysical.rawOfRat
    (B (GaussCellSourceBridge.sourceRow r pivot r) c)
  obtain ⟨T,h⟩ := uniform_machine_outputs (decide (i = r))
    current column row p (GaussPhysical.rawOfRat_valid _)
    (GaussPhysical.rawOfRat_valid _) (GaussPhysical.rawOfRat_valid _)
    (GaussPhysical.rawOfRat_valid _) hnum
  have htarget := GaussCellArithmeticTarget.sourceCellPacket_target
    B r pivot c i j
  refine ⟨T, ?_⟩
  simpa only [adaptedSourceCellPacket, current, column, row, p,
    htarget] using h

#print axioms adapted_difference
#print axioms uniform_machine_outputs
#print axioms adapted_source_cell_outputs

end CurrentAdditive.GaussUniformCellAlgebra
