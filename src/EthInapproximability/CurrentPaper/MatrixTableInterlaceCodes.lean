import EthInapproximability.CurrentPaper.MatrixMaterialization
import EthInapproximability.CurrentPaper.MatrixTableWriter
import Workspace.Types.Interlace

/-!
# Ordinal codes for the classical interlace table

Frozen v8 `02-foundations.tex`, `def:paper-interlace`, and
`B-effectivity-details.tex`, `thm:paper-materialization`.

The block index varies slowly within the row code.  In the column code,
coordinate zero is least significant.  This is the explicit coding used by
the existing `Workspace.Types.Interlace.interlace` matrix constructor.  A
different tuple order would require an explicit permutation before connecting
to that constructor.
-/

namespace EthInapproximability.CurrentPaper.MatrixTableInterlaceCodes

open MatrixMaterialization Workspace.Types.Interlace

/-- The row ordinal of `(block, oldRow)`. -/
def rowCode (blocks rows : ℕ) : Fin blocks × Fin rows ≃ Fin (blocks * rows) :=
  finProdFinEquiv

/-- The first coordinate is the least significant base-`cols` digit. -/
def columnCode (blocks cols : ℕ) : (Fin blocks → Fin cols) ≃ Fin (cols ^ blocks) :=
  finFunctionFinEquiv

theorem rowCode_value {blocks rows : ℕ} (i : Fin blocks) (x : Fin rows) :
    (rowCode blocks rows (i, x)).val = i.val * rows + x.val := by
  simp [rowCode, finProdFinEquiv_apply_val, Nat.add_comm, Nat.mul_comm]

theorem columnCode_coordinate {blocks cols : ℕ}
    (y : Fin (cols ^ blocks)) (i : Fin blocks) :
    ((columnCode blocks cols).symm y i).val = y.val / cols ^ i.val % cols := rfl

/-- Numerical entry equation for the actual mathematical interlace. -/
def entry (rows cols : ℕ) (source : List Bool) (r c : ℕ) : Bool :=
  source[(r % rows) * cols + (c / cols ^ (r / rows) % cols)]?.getD false

def table (rows cols blocks : ℕ) (source : List Bool) : List Bool :=
  MatrixTableWriter.tableWord (entry rows cols source) (cols ^ blocks)
    0 (blocks * rows)

theorem entry_on_codes {rows cols blocks : ℕ} (source : List Bool)
    (i : Fin blocks) (x : Fin rows) (y : Fin blocks → Fin cols) :
    entry rows cols source (rowCode blocks rows (i, x)).val
      (columnCode blocks cols y).val =
      source[x.val * cols + (y i).val]?.getD false := by
  have hr : (i.val * rows + x.val) % rows = x.val := by
    rw [Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt x.isLt]
  have hi : (i.val * rows + x.val) / rows = i.val := by
    rw [Nat.mul_comm i.val rows, Nat.mul_add_div (Nat.zero_lt_of_lt x.isLt),
      Nat.div_eq_of_lt x.isLt]
    simp
  simp only [entry, rowCode_value, hr, hi]
  rw [← columnCode_coordinate (columnCode blocks cols y) i]
  simp

/-- The literal source table produces exactly the mathematical interlace on
the explicit ordinal codes.  No source table accessor is hypothesized. -/
theorem entry_rowMajor {rows cols blocks : ℕ}
    (f : Fin rows → Fin cols → Bool)
    (i : Fin blocks) (x : Fin rows) (y : Fin blocks → Fin cols) :
    entry rows cols (rowMajor f) (rowCode blocks rows (i, x)).val
      (columnCode blocks cols y).val = interlaceFun f blocks (i, x) y := by
  rw [entry_on_codes, rowMajor_entry]
  rfl

end EthInapproximability.CurrentPaper.MatrixTableInterlaceCodes
