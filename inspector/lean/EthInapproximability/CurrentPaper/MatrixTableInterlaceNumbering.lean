import EthInapproximability.CurrentPaper.Iteration
import EthInapproximability.CurrentPaper.MatrixTableInterlace

/-!
# Ordinal adapter for the current paper's tuple numbering

Frozen v8 `def:paper-interlace`, `eq:one-level-exact-carriers`.
The one-level construction numbers tuples lexicographically, whereas the
physical interlace table uses the least-significant-first `finFunctionFinEquiv`.
Reversing the interlace block coordinate exactly reconciles the two codes.
This is a mathematical adapter, not yet a physical row-block permutation.
-/

namespace EthInapproximability.CurrentPaper.MatrixTableInterlaceNumbering

open MatrixTableInterlaceCodes

def reverseBlockRow (blocks rows : ℕ) (r : Fin (blocks*rows)) :
    Fin (blocks*rows) :=
  rowCode blocks rows
    (((rowCode blocks rows).symm r).1.rev,
      ((rowCode blocks rows).symm r).2)

theorem tuple_code (blocks cols : ℕ) (c : Fin (cols^blocks)) :
    ((Iteration.Numbering.fin cols).tuple blocks).equiv c =
      fun i => (columnCode blocks cols).symm c i.rev := by
  rfl

theorem prod_code (blocks rows : ℕ) (r : Fin (blocks*rows)) :
    ((Iteration.Numbering.fin blocks).prod
      (Iteration.Numbering.fin rows)).equiv r =
      (rowCode blocks rows).symm r := by
  rfl

theorem numbered_interlace (blocks rows cols : ℕ)
    (f : Fin rows → Fin cols → Bool)
    (r : Fin (blocks*rows)) (c : Fin (cols^blocks)) :
    Workspace.Types.Interlace.interlaceFun f blocks
      (((Iteration.Numbering.fin blocks).prod
        (Iteration.Numbering.fin rows)).equiv r)
      (((Iteration.Numbering.fin cols).tuple blocks).equiv c) =
    MatrixTableInterlace.interlaced (blocks := blocks) f
      (reverseBlockRow blocks rows r) c := by
  rw [prod_code, tuple_code]
  unfold reverseBlockRow MatrixTableInterlace.interlaced
  simp only [Equiv.symm_apply_apply]
  rfl

theorem tuple_code_general {Y : Type} (eY : Iteration.Numbering Y)
    (blocks : ℕ) (c : Fin (eY.size^blocks)) (i : Fin blocks) :
    ((eY.tuple blocks).equiv c) i =
      eY.equiv ((columnCode blocks eY.size).symm c i.rev) := by
  rfl

theorem prod_code_general {X : Type} (eX : Iteration.Numbering X)
    (blocks : ℕ) (r : Fin (blocks*eX.size)) :
    ((Iteration.Numbering.fin blocks).prod eX).equiv r =
      (((rowCode blocks eX.size).symm r).1,
        eX.equiv (((rowCode blocks eX.size).symm r).2)) := by
  rfl

/-- Numeric table of a transposed interlace under the paper's numbering.
The only discrepancy from the physical LSB-first table is reversal of the
block component of the interlace row. -/
theorem restoration_numeric {X Y : Type} (W : X → Y → Bool)
    (eX : Iteration.Numbering X) (eY : Iteration.Numbering Y)
    (r : ℕ) (c : Fin (eY.size^(2^r)))
    (row : Fin ((2^r)*eX.size)) :
    Restoration.output W r ((eY.tuple (2^r)).equiv c)
      (((Iteration.Numbering.fin (2^r)).prod eX).equiv row) =
    MatrixTableInterlace.interlaced (blocks := 2^r)
      (fun x y => W (eX.equiv x) (eY.equiv y))
      (reverseBlockRow (2^r) eX.size row) c := by
  rw [prod_code_general, Restoration.output_apply]
  rw [tuple_code_general eY (2^r) c
    (((rowCode (2^r) eX.size).symm row).1)]
  unfold reverseBlockRow MatrixTableInterlace.interlaced
  simp only [Equiv.symm_apply_apply]
  rfl

end EthInapproximability.CurrentPaper.MatrixTableInterlaceNumbering
