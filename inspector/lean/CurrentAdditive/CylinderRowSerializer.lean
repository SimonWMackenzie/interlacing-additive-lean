import CurrentAdditive.CylinderBitCellMachine
import EthInapproximability.CurrentPaper.SourceListMachineOuterFramed

/-! A physical counted-list writer for a row of already evaluated cylinder
bits.  Each bit is changed to the exact Bank3 rational zero/one record by a
fixed one-step item program; the inherited outer machine traverses the list,
frames each item, and charges every stack operation. -/

namespace CurrentAdditive.CylinderRowSerializer

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper.BitMachine
open CurrentAdditive.CodeDCodec
open CurrentAdditive.CylinderFeatureCodec
open CurrentAdditive.CylinderBitCellMachine

noncomputable def cellMachine : Machine :=
  ofFinite (0 : Fin 2) 1 .write (none : Option Bool)
    CylinderBitCellMachine.program

private theorem rawInit_cell (b : Bool) :
    rawInit (0 : Fin 2) (.write : CylinderBitCellMachine.Label)
      (none : Option Bool) [b] =
    CylinderBitCellMachine.cfg (some .write) none [b] [] := by
  unfold rawInit CylinderBitCellMachine.cfg CylinderBitCellMachine.bank
  congr 1

theorem cell_outputs (b : Bool) :
    cellMachine.OutputsWithin [b]
      (encodeRawRat (if b then oneRat else zeroRat)) 1 := by
  apply outputsWithin_of_raw_run (0 : Fin 2) 1 .write
    (none : Option Bool) CylinderBitCellMachine.program
    [b] (encodeRawRat (if b then oneRat else zeroRat)) 1 1 le_rfl
  · change (CylinderBitCellMachine.run 1 _).l = none
    rw [rawInit_cell, CylinderBitCellMachine.run_cell]
    rfl
  · change (CylinderBitCellMachine.run 1 _).stk 1 = _
    rw [rawInit_cell, CylinderBitCellMachine.run_cell]
    rfl

def rawBitItems (bits : List Bool) : List (List Bool) :=
  bits.map (fun b => [b])

def encodedCell (b : Bool) : List Bool :=
  encodeRawRat (if b then oneRat else zeroRat)

def encodedRow (bits : List Bool) : List Bool :=
  SourceListEncoding.encode (bits.map encodedCell)

def cellOutput (item : List Bool) : List Bool :=
  encodedCell (item.headD false)

noncomputable def rowMachine : Machine :=
  SourceListMachineOuterFramed.machine cellMachine

noncomputable def rowClock (bits : List Bool) : Nat :=
  SourceListMachineOuter.canonicalBound
    (SourceListMachineOuterFramed.itemMachine cellMachine)
    (rawBitItems bits)
    (SourceListMachineOuterFramed.framedOutput cellOutput)
    (SourceListMachineOuterFramed.framedBound cellOutput (fun _ => 1))

theorem row_outputs (bits : List Bool) :
    rowMachine.OutputsWithin
      (SourceListEncoding.encode (rawBitItems bits))
      (encodedRow bits) (rowClock bits) := by
  have hcell : ∀ x ∈ rawBitItems bits,
      cellMachine.OutputsWithin x (cellOutput x) 1 := by
    intro x hx
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hx
    simpa [cellOutput, encodedCell] using cell_outputs b
  have h := SourceListMachineOuterFramed.outputsWithin
    cellMachine (rawBitItems bits) cellOutput (fun _ => 1) hcell
  simpa [rowMachine, rowClock, rawBitItems,
    SourceListMachineOuterFramed.machine, encodedRow, cellOutput,
    encodedCell] using h

noncomputable def cellCost (b : Bool) : Nat :=
  SourceListMachineWork.itemCost
    (SourceListMachineOuterFramed.itemMachine cellMachine)
    [b]
    (SourceListMachineOuterFramed.framedOutput cellOutput [b])
    (SourceListMachineOuterFramed.framedBound cellOutput (fun _ => 1) [b])

noncomputable def cellCostCap : Nat := max (cellCost false) (cellCost true)

def frameLength (b : Bool) : Nat :=
  (SourceListMachineOuterFramed.framedOutput cellOutput [b]).length

def frameLengthCap : Nat := max (frameLength false) (frameLength true)

theorem rowClock_quadratic (bits : List Bool) :
    rowClock bits ≤
      (cellCostCap + frameLengthCap + 100) * (bits.length + 1)^2 := by
  let M := SourceListMachineOuterFramed.itemMachine cellMachine
  let xs := rawBitItems bits
  let f := SourceListMachineOuterFramed.framedOutput cellOutput
  let g := SourceListMachineOuterFramed.framedBound cellOutput (fun _ => 1)
  have hitem : ∀ x ∈ xs,
      SourceListMachineWork.itemCost M x (f x) (g x) ≤ cellCostCap := by
    intro x hx
    obtain ⟨b, _, rfl⟩ := List.mem_map.mp hx
    cases b
    · exact le_max_left _ _
    · exact le_max_right _ _
  have hout : ∀ x ∈ xs, (f x).length ≤ frameLengthCap := by
    intro x hx
    obtain ⟨b, _, rfl⟩ := List.mem_map.mp hx
    cases b
    · exact le_max_left _ _
    · exact le_max_right _ _
  have hb := SourceListMachineOuter.canonicalBound_le_count M xs f g
    cellCostCap frameLengthCap hitem hout
  have hx : xs.length = bits.length := by simp [xs, rawBitItems]
  have hbits : bits.length.bits.length ≤ bits.length :=
    UnaryBinaryEncoding.bits_length_le bits.length
  have hmul := Nat.mul_le_mul_left bits.length (show
    4 * bits.length.bits.length + 7 ≤ 4 * bits.length + 7 by omega)
  have hfield :
      (EthInapproximability.CurrentPaper.EncodedCommunication.natField
        bits.length).length ≤ 2 * bits.length + 1 := by
    simp only [EthInapproximability.CurrentPaper.EncodedCommunication.natField,
      EthInapproximability.CurrentPaper.EncodedCommunication.field_length]
    omega
  rw [hx] at hb
  have hbound : rowClock bits ≤
      5 * bits.length.bits.length + 7 +
        (bits.length * cellCostCap +
          bits.length * (4 * bits.length.bits.length + 7)) +
        (4 * bits.length.bits.length +
          (EthInapproximability.CurrentPaper.EncodedCommunication.natField
            bits.length).length + bits.length * frameLengthCap + 9) := by
    simpa only [rowClock, M, xs, f, g] using hb
  have hbase : rowClock bits ≤
      bits.length * cellCostCap + bits.length * frameLengthCap +
        4 * bits.length^2 + 18 * bits.length + 17 := by
    nlinarith [hbits, hmul, hfield, hbound]
  have hpow : bits.length ≤ (bits.length + 1)^2 := by nlinarith
  have hcost := Nat.mul_le_mul_left cellCostCap hpow
  have hframe := Nat.mul_le_mul_left frameLengthCap hpow
  have hconstant :
      4 * bits.length^2 + 18 * bits.length + 17 ≤
        100 * (bits.length + 1)^2 := by nlinarith
  nlinarith [hbase, hcost, hframe, hconstant]

#print axioms cell_outputs
#print axioms row_outputs
#print axioms rowClock_quadratic

end CurrentAdditive.CylinderRowSerializer
