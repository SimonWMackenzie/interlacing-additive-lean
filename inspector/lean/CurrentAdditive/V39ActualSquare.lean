import CurrentAdditive.V39PublicGeneratedSchedule
import CurrentAdditive.V39GeneratedSupportBudget
import CurrentAdditive.DeterministicETHEncodedTable

/-! Literal final table and encoding for the currently computed constructor.
This file instantiates square padding on StoredMatrix rather than receiving
an arbitrary presentation record. No NO promise or physical clock is assumed.
The square word below is the actual all-table estimator input.
-/

namespace CurrentAdditive.V39GeneratedConstruction

open Workspace.Types.CommComplexity
open EthInapproximability.CurrentPaper
open CurrentAdditive.DeterministicETHEncodedTable

namespace StoredMatrix

theorem rows_pos (R : StoredMatrix) : 0 < R.rows := law_size_pos R.rowLaw
theorem cols_pos (R : StoredMatrix) : 0 < R.cols := law_size_pos R.colLaw

def square (R : StoredMatrix) :
    Fin (Paper2.SquarePadding.side R.rows R.cols) →
      Fin (Paper2.SquarePadding.side R.rows R.cols) → Bool :=
  Paper2.SquarePadding.matrix R.rows_pos R.cols_pos R.entry

def squareWord (R : StoredMatrix) : List Bool :=
  DeterministicETHEncodedTable.squareWord R.square

theorem square_cost (R : StoredMatrix) : D R.square = D R.entry :=
  Paper2.SquarePadding.D_matrix R.rows_pos R.cols_pos R.entry

theorem square_original (R : StoredMatrix) (i : Fin R.rows) (j : Fin R.cols) :
    R.square (Fin.castLE (Paper2.SquarePadding.rows_le_side _ _) i)
      (Fin.castLE (Paper2.SquarePadding.cols_le_side _ _) j) = R.entry i j :=
  Paper2.SquarePadding.matrix_original_entry _ _ _ _ _

theorem square_side_power (R : StoredMatrix) :
    ∃ e : ℕ, Paper2.SquarePadding.side R.rows R.cols = 2^e :=
  ⟨Paper2.SquarePadding.exponent R.rows R.cols, rfl⟩

theorem squareWord_target (R : StoredMatrix) :
    Paper2.AModel.targetD R.squareWord = some (D R.entry) := by
  rw [squareWord, DeterministicETHEncodedTable.squareWord_targetD R.square
    (Paper2.SquarePadding.side_pos _ _), R.square_cost]

theorem squareWord_decodes (R : StoredMatrix) :
    Paper2.AModel.decodeMatrix R.squareWord =
      some (Paper2.SquarePadding.side R.rows R.cols,
        Paper2.SquarePadding.side R.rows R.cols,
        MatrixMaterialization.rowMajor R.square) :=
  DeterministicETHEncodedTable.squareWord_decodes R.square
    (Paper2.SquarePadding.side_pos _ _)

theorem squareWord_length (R : StoredMatrix) :
    R.squareWord.length ≤ 5*(Paper2.SquarePadding.side R.rows R.cols)^2+2 :=
  DeterministicETHEncodedTable.squareWord_length_le R.square
    (Paper2.SquarePadding.side_pos _ _)

/-- Every printed bit is charged: the two actual dimensions and all repeated
Boolean entries are present in this canonical matrix word. -/
theorem squareWord_length_rectangle (R : StoredMatrix) :
    R.squareWord.length ≤ 20*(R.rows*R.cols)^2+2 := by
  have hp := Paper2.SquarePadding.entries_lt_four_input_sq R.rows_pos R.cols_pos
  have hl := R.squareWord_length
  change Paper2.SquarePadding.side R.rows R.cols *
    Paper2.SquarePadding.side R.rows R.cols < 4*(R.rows*R.cols)^2 at hp
  nlinarith

end StoredMatrix

/-- The constructor, public threshold and canonical estimator word are all
fixed before either graph promise is considered. -/
def publicGraphWord (p : SourceConstants) {n m : ℕ}
    (hn : 0 < n) (hlow : n ≤ 2*m) (hdegree : 2*m ≤ p.degree*n)
    (edge : Fin m → Bool → Fin n) (k : ℕ) : List Bool :=
  (publicGraphRun p hn hlow hdegree edge k).squareWord

theorem publicGraphWord_target (p : SourceConstants) {n m : ℕ}
    (hn : 0 < n) (hlow : n ≤ 2*m) (hdegree : 2*m ≤ p.degree*n)
    (edge : Fin m → Bool → Fin n) (k : ℕ) :
    Paper2.AModel.targetD (publicGraphWord p hn hlow hdegree edge k) =
      some (D (publicGraphRun p hn hlow hdegree edge k).entry) :=
  StoredMatrix.squareWord_target _

/-- Same-table YES guarantee, with no NO/global-profile premise. -/
theorem publicGraphWord_yes (p : SourceConstants) {n m : ℕ}
    (hn : 0 < n) (hlow : n ≤ 2*m) (hdegree : 2*m ≤ p.degree*n)
    (edge : Fin m → Bool → Fin n) (k : ℕ) (colour : Fin n → Fin 3)
    (proper : ∀ j, colour (edge j false) ≠ colour (edge j true)) :
    ∃ d : ℕ,
      Paper2.AModel.targetD (publicGraphWord p hn hlow hdegree edge k) = some d ∧
      d ≤ publicGraphThreshold p n m hn hlow hdegree k :=
  ⟨_, publicGraphWord_target p hn hlow hdegree edge k,
    publicGraphRun_yes p hn hlow hdegree edge k colour proper⟩

end CurrentAdditive.V39GeneratedConstruction

#print axioms CurrentAdditive.V39GeneratedConstruction.StoredMatrix.squareWord_target
#print axioms CurrentAdditive.V39GeneratedConstruction.StoredMatrix.squareWord_length_rectangle
#print axioms CurrentAdditive.V39GeneratedConstruction.publicGraphWord_yes
