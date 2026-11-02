import EthInapproximability.CurrentPaper.MatrixWeightedArithmetic
import EthInapproximability.CurrentPaper.MatrixTableColumnRepeat
import EthInapproximability.CurrentPaper.MatrixAddressMachine
import EthInapproximability.CurrentPaper.MatrixStage4Codes

/-!
# Fixed finite-stack copying stages for the protected duplicate

These are genuine runs of the existing fixed column-repeat machine.  The
input tables are literal bit lists, and the stated bounds charge reads and
writes.  The diagonal input here is an **explicit table argument**, not a
proved output of the graph/source reduction: constructing it from raw `B`
and its joint-tail diagonal is a separate outstanding machine obligation.
Likewise joining these groups and duplicating four row supports is not
silently included in these statements.
-/

namespace EthInapproximability.CurrentPaper.MatrixWeightedGroupMachine

open MatrixTableColumnRepeat MatrixTableWriter
open Construction MatrixStage4Codes

/-- The current paper has exactly two, not three, protected column groups. -/
def fullCopies (diagonalWidth : ℕ) : ℕ := 182 * diagonalWidth
def diagonalCopies (fullWidth : ℕ) : ℕ := 2 * fullWidth

/-- Literal fixed-machine multiplication obtains the full-group copy count;
both input factors survive, and the output is written in unary. -/
theorem fullCopies_run (diagonalWidth : ℕ) :
    MatrixAddressMachine.run
      (MatrixAddressMachine.exactTime 182 diagonalWidth 0)
      (MatrixAddressMachine.cfg (some .outer) false
        (List.replicate 182 true) (List.replicate diagonalWidth true)
        (List.replicate 0 true) [] [] []) =
      MatrixAddressMachine.cfg none false
        (List.replicate 182 true) (List.replicate diagonalWidth true)
        (List.replicate 0 true) [] []
        (List.replicate (fullCopies diagonalWidth) true) := by
  simpa [fullCopies] using
    MatrixAddressMachine.address_run 182 diagonalWidth 0 false []

/-- Literal fixed-machine multiplication obtains the diagonal-group count. -/
theorem diagonalCopies_run (fullWidth : ℕ) :
    MatrixAddressMachine.run
      (MatrixAddressMachine.exactTime 2 fullWidth 0)
      (MatrixAddressMachine.cfg (some .outer) false
        (List.replicate 2 true) (List.replicate fullWidth true)
        (List.replicate 0 true) [] [] []) =
      MatrixAddressMachine.cfg none false
        (List.replicate 2 true) (List.replicate fullWidth true)
        (List.replicate 0 true) [] []
        (List.replicate (diagonalCopies fullWidth) true) := by
  simpa [diagonalCopies] using
    MatrixAddressMachine.address_run 2 fullWidth 0 false []

/-- Physical generation of the 182-weight full-column group from raw `B`'s
row-major bit table.  `fullWidth` and `diagonalWidth` are preserved as unary
scalars in the machine's persistent bank; the copy count is an explicit
scalar input and must be computed by a preceding charged arithmetic stage. -/
theorem full_group_run (rows fullWidth diagonalWidth : ℕ)
    (rawTable oldOutput : List Bool) :
    ∃ t ≤ MatrixTableWriter.writerBound rows
      (fullWidth * fullCopies diagonalWidth)
      (uniformBound rows fullWidth (fullCopies diagonalWidth) rawTable.length), ∃ v,
      MatrixTableWriter.run entryProgram start initial t
        (MatrixTableWriter.cfg (some (.inr (.copy .rows))) (initial, none)
          (MatrixTableWriter.ready
            (persistentBank (fullCopies diagonalWidth) fullWidth rawTable)
            rows (fullWidth * fullCopies diagonalWidth) 0 0 0 0 [] oldOutput)) =
      MatrixTableWriter.cfg none v
        (MatrixTableWriter.ready
          (persistentBank (fullCopies diagonalWidth) fullWidth rawTable)
          rows (fullWidth * fullCopies diagonalWidth) 0 0 0 0 []
          (MatrixTableWriter.tableWord
            (fun x y => rawTable[x * fullWidth + y / fullCopies diagonalWidth]?.getD false)
            (fullWidth * fullCopies diagonalWidth) 0 rows ++ oldOutput)) := by
  exact repeat_table rows fullWidth (fullCopies diagonalWidth) rawTable oldOutput

/-- Specialisation to the actual Stage--4 source table.  This is the full
support only; it does not make the diagonal-group table an external oracle. -/
def actual_full_group_run {rx cy : ℕ}
    (R : Fin rx → Fin cy → Bool) (a s q L nv nb : ℕ)
    (hs : 0 < s) (family : SecondFamily a q L (Fin rx))
    (order : ItemOrder nv nb)
    (vectors : Fin (nv + nb) → Fin q → Bool)
    (cap : ∀ α, (activeItems vectors α).card ≤ s)
    (oldOutput : List Bool) :=
  full_group_run (rows s L nv nb rx) (cols a s q cy)
    (q * cy ^ firstLength a s)
    (rawTable R a s q L nv nb hs family order vectors cap) oldOutput

/-- Physical generation of the 2-weight diagonal-column group, once its
ordered diagonal restriction table has itself been produced and charged. -/
theorem diagonal_group_run (rows fullWidth diagonalWidth : ℕ)
    (diagonalTable oldOutput : List Bool) :
    ∃ t ≤ MatrixTableWriter.writerBound rows
      (diagonalWidth * diagonalCopies fullWidth)
      (uniformBound rows diagonalWidth (diagonalCopies fullWidth) diagonalTable.length), ∃ v,
      MatrixTableWriter.run entryProgram start initial t
        (MatrixTableWriter.cfg (some (.inr (.copy .rows))) (initial, none)
          (MatrixTableWriter.ready
            (persistentBank (diagonalCopies fullWidth) diagonalWidth diagonalTable)
            rows (diagonalWidth * diagonalCopies fullWidth) 0 0 0 0 [] oldOutput)) =
      MatrixTableWriter.cfg none v
        (MatrixTableWriter.ready
          (persistentBank (diagonalCopies fullWidth) diagonalWidth diagonalTable)
          rows (diagonalWidth * diagonalCopies fullWidth) 0 0 0 0 []
          (MatrixTableWriter.tableWord
            (fun x y => diagonalTable[
              x * diagonalWidth + y / diagonalCopies fullWidth]?.getD false)
            (diagonalWidth * diagonalCopies fullWidth) 0 rows ++ oldOutput)) := by
  exact repeat_table rows diagonalWidth (diagonalCopies fullWidth)
    diagonalTable oldOutput

/-- The further uniform-copy factor is a third *copying pass*, not a third
support group.  It is paid for at its full output width. -/
theorem uniform_group_run (rows groupedWidth Sdup : ℕ)
    (groupedTable oldOutput : List Bool) :
    ∃ t ≤ MatrixTableWriter.writerBound rows (groupedWidth * Sdup)
      (uniformBound rows groupedWidth Sdup groupedTable.length), ∃ v,
      MatrixTableWriter.run entryProgram start initial t
        (MatrixTableWriter.cfg (some (.inr (.copy .rows))) (initial, none)
          (MatrixTableWriter.ready (persistentBank Sdup groupedWidth groupedTable)
            rows (groupedWidth * Sdup) 0 0 0 0 [] oldOutput)) =
      MatrixTableWriter.cfg none v
        (MatrixTableWriter.ready (persistentBank Sdup groupedWidth groupedTable)
          rows (groupedWidth * Sdup) 0 0 0 0 []
          (MatrixTableWriter.tableWord
            (fun x y => groupedTable[x * groupedWidth + y / Sdup]?.getD false)
            (groupedWidth * Sdup) 0 rows ++ oldOutput)) := by
  exact repeat_table rows groupedWidth Sdup groupedTable oldOutput

end EthInapproximability.CurrentPaper.MatrixWeightedGroupMachine
