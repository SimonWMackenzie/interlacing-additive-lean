import CurrentAdditive.CylinderContextScanRun
import CurrentAdditive.GaussSearchClock
import CurrentAdditive.GaussRowCount
import CurrentAdditive.GaussTypedGetterBridge
import EthInapproximability.CurrentPaper.BitMachineComposition

/-! The physical dimensions of the raw typed matrix. The column count is
obtained by a real first-row lookup followed by the real counted-list machine;
it is not an input parameter silently placed in a unary bank. -/

namespace CurrentAdditive.GaussMatrixDimensions64

noncomputable section

set_option maxRecDepth 4096
set_option maxHeartbeats 1800000

open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding

noncomputable instance : Fintype CylinderContextScanStep.Label := Fintype.ofFinite _
noncomputable instance : Fintype CylinderContextScanStep.Control := Fintype.ofFinite _

noncomputable def firstRowMachine : BitMachine.Machine :=
  ofFinite (8 : Fin 12) 6 (.inl .scan : CylinderContextScanStep.Label)
    (CylinderContextScanStep.copyControl ((),none)) CylinderContextScanStep.program

theorem firstRow_initial (source : List Bool) :
    rawInit (8 : Fin 12) (.inl .scan : CylinderContextScanStep.Label)
      (CylinderContextScanStep.copyControl ((),none)) source =
      CylinderContextScanStep.initial source 0 := by
  unfold rawInit CylinderContextScanStep.initial
  congr 1
  funext j
  fin_cases j <;> rfl

theorem firstRow_outputs (row : List Bool) (rows : List (List Bool)) :
    firstRowMachine.OutputsWithin (SourceListEncoding.encode (row::rows)) row
      (50*((SourceListEncoding.encode (row::rows)).length+1)^3) := by
  obtain ⟨t,ht,he⟩ := CylinderContextScanStep.scan_step [] row rows
  have hbudget := GaussSearchClock.getter_bound [] row rows
  have ht' : t ≤ 50*((SourceListEncoding.encode (row::rows)).length+1)^3 := by
    unfold LargeContextListScheduler.getterBudget at hbudget
    simp only [List.length_nil,List.nil_append,Nat.mul_zero,Nat.zero_add] at ht hbudget
    omega
  apply outputsWithin_of_raw_run (8 : Fin 12) 6
    (.inl .scan : CylinderContextScanStep.Label)
    (CylinderContextScanStep.copyControl ((),none)) CylinderContextScanStep.program
    (SourceListEncoding.encode (row::rows)) row t _ ht'
  · rw [firstRow_initial]
    change (CylinderContextScanStep.run t _).l = none
    simpa only [List.nil_append,List.length_nil] using congrArg (fun c => c.l) he
  · rw [firstRow_initial]
    change (CylinderContextScanStep.run t _).stk 6 = row
    have h := congrArg (fun c => c.stk (6 : Fin 12)) he
    simpa only [List.nil_append,List.length_nil,CylinderContextScanStep.selectedBank] using h

noncomputable def columnsMachine : BitMachine.Machine :=
  BitMachineComposition.composition firstRowMachine GaussRowCount.machine

noncomputable def columnsClock (N : Nat) : Nat :=
  50*(N+1)^3+2*N+2+GaussRowCount.polynomialClock N

private theorem row_length_le (row : List Bool) (rows : List (List Bool)) :
    row.length ≤ (SourceListEncoding.encode (row::rows)).length := by
  have h := GaussListContext.IndexedV2Clock.fields_item_length_le (row::rows)
    row (by simp)
  simp only [SourceListEncoding.encode,List.length_append]
  omega

theorem columns_outputs (cells : List (List Bool)) (rows : List (List Bool)) :
    columnsMachine.OutputsWithin
      (SourceListEncoding.encode (SourceListEncoding.encode cells::rows))
      (List.replicate cells.length true)
      (columnsClock (SourceListEncoding.encode (SourceListEncoding.encode cells::rows)).length) := by
  have hrow := row_length_le (SourceListEncoding.encode cells) rows
  have hc := BitMachine.outputsWithin_mono GaussRowCount.machine
    (GaussRowCount.outputs_polynomial cells)
    (GaussRowCount.polynomialClock_mono hrow)
  apply BitMachine.outputsWithin_mono columnsMachine
    (BitMachineComposition.composition_outputsWithin firstRowMachine
      GaussRowCount.machine (firstRow_outputs (SourceListEncoding.encode cells) rows) hc)
  unfold columnsClock
  omega

theorem typed_rows {m k : Nat} (B : Fin m → Fin k → ℚ) :
    GaussRowCount.machine.OutputsWithin (GaussPhysical.encodeTypedMatrix B)
      (List.replicate m true)
      (GaussRowCount.polynomialClock (GaussPhysical.encodeTypedMatrix B).length) := by
  simpa only [GaussTypedGetterBridge.encodeTypedMatrix_eq,
    GaussTypedGetterBridge.rowWords,List.length_map,List.length_finRange] using
      GaussRowCount.outputs_polynomial (GaussTypedGetterBridge.rowWords B)

/-- Every nonempty rectangular typed matrix supplies its true column count
to the fixed program, including a nonempty matrix with zero columns. -/
theorem typed_columns {m k : Nat} (B : Fin m → Fin k → ℚ) (hm : 0 < m) :
    columnsMachine.OutputsWithin (GaussPhysical.encodeTypedMatrix B)
      (List.replicate k true)
      (columnsClock (GaussPhysical.encodeTypedMatrix B).length) := by
  let i : Fin m := ⟨0,hm⟩
  let rows := GaussTypedGetterBridge.rowWords B
  let cells := GaussTypedGetterBridge.cellWords B i
  have hrows : rows.length = m := by simp [rows,GaussTypedGetterBridge.rowWords]
  have hsplit : rows = SourceListEncoding.encode cells :: rows.drop 1 := by
    have h := GaussTypedGetterBridge.split_at rows 0 (by omega)
    have hget : rows[0] = SourceListEncoding.encode cells := by
      exact GaussTypedGetterBridge.rowWords_get B i
    simpa only [List.take_zero,List.nil_append,Nat.zero_add,hget] using h
  have hmatrix : GaussPhysical.encodeTypedMatrix B =
      SourceListEncoding.encode (SourceListEncoding.encode cells :: rows.drop 1) := by
    rw [GaussTypedGetterBridge.encodeTypedMatrix_eq]
    exact congrArg SourceListEncoding.encode hsplit
  rw [hmatrix]
  have hlen : cells.length = k := by simp [cells,GaussTypedGetterBridge.cellWords]
  simpa only [hlen] using columns_outputs cells (rows.drop 1)

#print axioms firstRow_outputs
#print axioms typed_rows
#print axioms typed_columns

end
end CurrentAdditive.GaussMatrixDimensions64
