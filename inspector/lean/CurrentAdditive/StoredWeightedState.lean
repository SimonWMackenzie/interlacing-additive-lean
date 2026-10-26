import CurrentAdditive.V39StoredGenerated
import CurrentAdditive.CodeDTargetV2
import EthInapproximability.CurrentPaper.MatrixMaterialization

set_option maxHeartbeats 1000000

/-! The reusable physical state stores all Boolean cells and both ordered
canonical rational law tables. Dimensions are recovered from the two list
counts. All positions, including equal labels/values, remain present. -/

namespace CurrentAdditive.StoredWeightedState

open Paper2
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineBankCodec
open CurrentAdditive.V39GeneratedConstruction CurrentAdditive.CodeDCodec
open CurrentAdditive.CodeDCanonicalSourceV2

def lawAlphabet {n : ℕ} (μ : PositiveRationalLaw (Fin n)) : Array (ℕ × ℚ) :=
  Array.ofFn (fun i : Fin n => (i.val,μ.weight i))

@[simp] theorem lawAlphabet_size {n : ℕ} (μ : PositiveRationalLaw (Fin n)) :
    (lawAlphabet μ).size=n := by simp [lawAlphabet]

def lawBytes {n : ℕ} (μ : PositiveRationalLaw (Fin n)) : List Bool :=
  CodeDTargetV2.alphabetBytes (lawAlphabet μ)

def decodedLaw {n : ℕ} (μ : PositiveRationalLaw (Fin n)) : List (ℕ × RawRat) :=
  (lawAlphabet μ).toList.map (fun a => (a.1,rawOfRat a.2))

theorem law_decode {n : ℕ} (μ : PositiveRationalLaw (Fin n)) :
    CodeDTargetV2.alphabetDecode (lawBytes μ)=some (decodedLaw μ) :=
  CodeDTargetV2.alphabetDecode_correct (lawAlphabet μ)

@[simp] theorem decodedLaw_length {n : ℕ} (μ : PositiveRationalLaw (Fin n)) :
    (decodedLaw μ).length=n := by simp [decodedLaw]

theorem decodedLaw_values {n : ℕ} (μ : PositiveRationalLaw (Fin n)) :
    (decodedLaw μ).map (fun a => (a.1,a.2.value))=(lawAlphabet μ).toList :=
  CodeDTargetV2.alphabet_values_correct (lawAlphabet μ)

theorem decodedLaw_indexed {n : ℕ} (μ : PositiveRationalLaw (Fin n)) :
    decodedLaw μ=List.ofFn (fun i : Fin n => (i.val,rawOfRat (μ.weight i))) := by
  simp [decodedLaw,lawAlphabet,List.map_ofFn,Function.comp_def]

def cells (R : StoredMatrix) : List Bool := MatrixMaterialization.rowMajor R.entry

@[simp] theorem cells_length (R : StoredMatrix) : (cells R).length=R.rows*R.cols :=
  MatrixMaterialization.rowMajor_length R.entry

theorem cells_entry (R : StoredMatrix) (r : Fin R.rows) (c : Fin R.cols) :
    (cells R)[r.val*R.cols+c.val]?=some (R.entry r c) :=
  MatrixMaterialization.rowMajor_entry R.entry r c

def encode (R : StoredMatrix) : List Bool :=
  BitMachineBankCodec.encode ![cells R,lawBytes R.rowLaw,lawBytes R.colLaw]

abbrev RawState := List Bool × (List (ℕ × RawRat) × List (ℕ × RawRat))

def decode (word : List Bool) : Option RawState := do
  let S←BitMachineBankCodec.decode 3 word
  let row←CodeDTargetV2.alphabetDecode (S 1)
  let col←CodeDTargetV2.alphabetDecode (S 2)
  pure (S 0,(row,col))

theorem decode_encode (R : StoredMatrix) :
    decode (encode R)=some (cells R,(decodedLaw R.rowLaw,decodedLaw R.colLaw)) := by
  simp [decode,encode,law_decode]

theorem state_dimensions (R : StoredMatrix) :
    (decodedLaw R.rowLaw).length=R.rows ∧
      (decodedLaw R.colLaw).length=R.cols ∧
      (cells R).length=(decodedLaw R.rowLaw).length*(decodedLaw R.colLaw).length := by
  simp

end CurrentAdditive.StoredWeightedState

#print axioms CurrentAdditive.StoredWeightedState.decode_encode
#print axioms CurrentAdditive.StoredWeightedState.cells_entry
