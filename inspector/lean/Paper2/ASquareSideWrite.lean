import Paper2.ASquareSide
import Paper2.A4SquareWriter

/-!
# U17: the unary side joined with the admitted square writer (lane owner:a-square-1)

Private, 26 September 2026. ONE fixed program on the admitted writer's own stack type
`MatrixTableWriter.Stack 10`, sequenced by the admitted `BitMachineRawSequence.runs`:

1. `Side.program` (ASquareSide), inlined by the admitted stack embedding at `ιW`: it reads unary `m`,
   `n` from the writer's persistent bank slots 0, 1 (restored), writes unary
   `SquarePadding.side m n` into the writer's `rows` and `cols` counters, and uses only bank slots
   3..9 and the writer's `temp` stack as scratch (empty before and after);
2. the admitted writer `MatrixTableWriter.program` over the admitted `SquareWriter.entryProgram`,
   run by the admitted `SquareWriter.square_table`.

So the writer's entry configuration `MatrixTableWriter.ready (persistentBank m n (rowMajor F)) side
side 0 0 0 0 [] output`, which `square_table` takes as SUPPLIED, is now PRODUCED (for the counters)
from the bank `ready (persistentBank m n (rowMajor F)) 0 0 0 0 0 0 [] output`; every step is
charged. The bank itself (`unary m`, `unary n`, the row-major source word) is still an input of this
stage: its production from the encoded instance (the parser) is NOT done here.
Does not close a ledger row.
-/

namespace Paper2.ASquare.SideWrite

open Turing Turing.TM2.Stmt
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper.Unit4Post
open Paper2.ASquare.Side

abbrev WStack := MatrixTableWriter.Stack 10

/-- Side-program stacks into the writer's stacks: `m, n` = bank 0, 1; the counters `rows`, `cols`;
scratch = bank 3..9 and `temp`. -/
def ιWfun : Fin 12 → WStack :=
  ![.inl (.inl 0), .inl (.inl 1), .inl (.inl 3), .inl (.inl 4), .inl (.inl 5), .inl (.inl 6),
    .inl (.inl 7), .inr .rows, .inl (.inl 8), .inl (.inl 9), .inr .cols, .inr .temp]

def ιW : Fin 12 ↪ WStack := ⟨ιWfun, by decide⟩

def sSide := fun l => BitMachineStackEmbedding.stackStmt ιW (Side.program l)

abbrev WLabel := MatrixTableWriter.Label Unit4Shell.SquareWriter.Label
abbrev WControl := MatrixTableWriter.Control Unit4Shell.SquareWriter.Control

def writer : WLabel → TM2.Stmt (fun _ : WStack => Bool) WLabel WControl :=
  MatrixTableWriter.program Unit4Shell.SquareWriter.entryProgram Unit4Shell.SquareWriter.start
    Unit4Shell.SquareWriter.initial

def writerStart : WLabel := .inr (.copy .rows)
def writerInit : WControl := (Unit4Shell.SquareWriter.initial, none)

abbrev Label := BitMachineRawSequence.Label Side.Label WLabel
abbrev Control := BitMachineRawSequence.Control Side.Control WControl
/-- The joined program: the side stage, then the admitted square writer. -/
def program := BitMachineRawSequence.program sSide writer writerStart Side.initial writerInit
def start : Label := BitMachineRawSequence.leftLabel Side.start
def initial : Control := (Side.initial, writerInit)

theorem side_stage (m n : ℕ) (source output : List Bool) :
    ∃ t ≤ sideBound m n, ∃ v,
      ((advance sSide)^[t])
        ⟨some Side.start, Side.initial,
          (MatrixTableWriter.ready (Unit4Shell.SquareWriter.persistentBank m n source)
            0 0 0 0 0 0 [] output).contents⟩ =
      ⟨none, v,
          (MatrixTableWriter.ready (Unit4Shell.SquareWriter.persistentBank m n source)
            (SquarePadding.side m n) (SquarePadding.side m n) 0 0 0 0 [] output).contents⟩ := by
  obtain ⟨t, ht, v, h⟩ := side_run m n
  refine ⟨t, ht, v, ?_⟩
  exact embed_run ιW Side.program Side.start Side.initial v _ _ _ _ t h
    (by intro i; fin_cases i <;> rfl) (by intro i; fin_cases i <;> rfl)
    (by
      intro j hj
      rcases j with (k | k) | k
      · fin_cases k <;> first
          | rfl
          | exact absurd rfl (hj 0) | exact absurd rfl (hj 1) | exact absurd rfl (hj 2)
          | exact absurd rfl (hj 3) | exact absurd rfl (hj 4) | exact absurd rfl (hj 5)
          | exact absurd rfl (hj 6) | exact absurd rfl (hj 8) | exact absurd rfl (hj 9)
      · fin_cases k <;> rfl
      · cases k <;> first
          | rfl
          | exact absurd rfl (hj 7) | exact absurd rfl (hj 10) | exact absurd rfl (hj 11))

/-- **The square writer with its counters produced.** For `m, n > 0`, every `F`, and every old
output, the ONE fixed joined program, started on the writer bank with `unary m`, `unary n`,
`rowMajor F` in the persistent slots and EMPTY counters, halts with exactly
`rowMajor (SquarePadding.matrix hm hn F) ++ output` on the output stack, the persistent bank
restored, and `unary (SquarePadding.side m n)` left in both counters (every other writer stack empty),
within `sideBound m n + writerBound side side (callbackBound side side m n (m*n)) + 1` steps. -/
theorem side_write {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (F : Fin m → Fin n → Bool)
    (output : List Bool) :
    ∃ t ≤ sideBound m n +
        MatrixTableWriter.writerBound (SquarePadding.side m n) (SquarePadding.side m n)
          (Unit4Shell.SquareWriter.callbackBound (SquarePadding.side m n)
            (SquarePadding.side m n) m n (m * n)) + 1, ∃ v,
      ((advance program)^[t])
        ⟨some start, initial,
          (MatrixTableWriter.ready
            (Unit4Shell.SquareWriter.persistentBank m n (MatrixMaterialization.rowMajor F))
            0 0 0 0 0 0 [] output).contents⟩ =
      ⟨none, v,
          (MatrixTableWriter.ready
            (Unit4Shell.SquareWriter.persistentBank m n (MatrixMaterialization.rowMajor F))
            (SquarePadding.side m n) (SquarePadding.side m n) 0 0 0 0 []
            (MatrixMaterialization.rowMajor (SquarePadding.matrix hm hn F) ++ output)).contents⟩ := by
  obtain ⟨ts, hts, vs, hs⟩ := side_stage m n (MatrixMaterialization.rowMajor F) output
  obtain ⟨tw, htw, vw, hw⟩ := Unit4Shell.SquareWriter.square_table hm hn F output
  have hw' : ((advance writer)^[tw])
      ⟨some writerStart, writerInit,
        (MatrixTableWriter.ready
          (Unit4Shell.SquareWriter.persistentBank m n (MatrixMaterialization.rowMajor F))
          (SquarePadding.side m n) (SquarePadding.side m n) 0 0 0 0 [] output).contents⟩ =
      ⟨none, vw,
        (MatrixTableWriter.ready
          (Unit4Shell.SquareWriter.persistentBank m n (MatrixMaterialization.rowMajor F))
          (SquarePadding.side m n) (SquarePadding.side m n) 0 0 0 0 []
          (MatrixMaterialization.rowMajor (SquarePadding.matrix hm hn F) ++ output)).contents⟩ :=
    hw
  obtain ⟨t, ht, e⟩ := BitMachineRawSequence.runs sSide writer Side.start writerStart
    Side.initial vs writerInit vw _ _ _ ts tw hs hw'
  exact ⟨t, by omega, _, e⟩

#print axioms side_stage
#print axioms side_write

end Paper2.ASquare.SideWrite
