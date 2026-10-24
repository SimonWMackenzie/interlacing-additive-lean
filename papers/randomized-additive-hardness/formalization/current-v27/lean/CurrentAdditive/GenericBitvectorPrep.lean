import CurrentAdditive.GenericBitvectorPaddedTable
import EthInapproximability.CurrentPaper.BitMachineRawSequence

/-! One physical program prepares both coordinates for a supplied padded
base table while retaining their original code words. -/

namespace Paper2.GenericBitvectorPrep

open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open BitMachineRawSequence (leftLabel)

def rowControl : Option Bool × (Bool × Bool) := (none, (false, false))
def program := BitMachineRawSequence.program
  GenericBitvectorRowAddress.program GenericBitvectorColumnLength.program
  GenericWordLengthCopy.Label.scan rowControl (none : Option Bool)

def start : BitMachineRawSequence.Label
    (BitMachineRawSequence.Label BitMachineCopy.Label MatrixBinaryAddress.Label)
    GenericWordLengthCopy.Label := .inl (.inl .scan)
def initial := (rowControl, (none : Option Bool))

theorem prep_run (S : Fin 14 → List Bool) (row col : List Bool)
    (h0 : S 0 = row) (h1 : S 1 = []) (h2 : S 2 = [])
    (h3 : S 3 = []) (h4 : S 4 = [])
    (h5 : S 5 = col) (h8 : S 8 = []) (h9 : S 9 = []) :
    ∃ t ≤ 2 * row.length + 2 + MatrixBinaryAddress.workFrom 0 row + 1 +
        (2 * col.length + 2) + 1,
      ((advance program)^[t])
        (⟨some start, initial, S⟩ : TM2.Cfg (fun _ : Fin 14 => Bool) _ _) =
      ⟨none, initial,
        Function.update (Function.update S 1
          (List.replicate (MatrixBinaryAddress.valueFrom 0 row) true)) 8
          (List.replicate col.length true)⟩ := by
  obtain ⟨tr, htr, hr⟩ := GenericBitvectorRowAddress.row_address_run
    S row h0 h1 h2 h3 h4
  let R := Function.update S 1
    (List.replicate (MatrixBinaryAddress.valueFrom 0 row) true)
  have hc := GenericBitvectorColumnLength.length_run R col
    (by simp [R, h5]) (by simp [R, h8]) (by simp [R, h9])
  obtain ⟨t, ht, h⟩ := BitMachineRawSequence.runs
    GenericBitvectorRowAddress.program GenericBitvectorColumnLength.program
    (.inl BitMachineCopy.Label.scan) GenericWordLengthCopy.Label.scan
    rowControl rowControl (none : Option Bool) (none : Option Bool)
    S R _ tr (2 * col.length + 2) hr hc
  exact ⟨t, by omega, by simpa only [program, start, initial] using h⟩

#print axioms prep_run

end Paper2.GenericBitvectorPrep
