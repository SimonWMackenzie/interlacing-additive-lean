import EthInapproximability.CurrentPaper.SourceClauseRowWriterFanout

/-!
# Charged processed-row index advance

The row-loop callback carries its own persistent unary processed-row ordinal.
After each completed source row, one physical push advances that ordinal while
all validated-row, accumulator, and remaining-input cells stay unchanged.
-/

namespace EthInapproximability.CurrentPaper.SourceClauseRowWriterRowAdvance

open Turing Turing.TM2.Stmt BitMachineEncoding
open scoped Classical

abbrev Stack (q : ℕ) := SourceClauseRowWriterOperands.Stack q

inductive Label where
  | push | done
  deriving DecidableEq, Fintype

def program {q : ℕ} : Label →
    TM2.Stmt (fun _ : Stack q => Bool) Label Unit
  | .push => push SourceClauseRowWriterOperands.rowIndex
      (fun _ => true) (goto (fun _ => .done))
  | .done => halt

theorem run {q : ℕ} (S : Stack q → List Bool) :
    ((advance (program (q := q)))^[2])
      (⟨some .push, (), S⟩ :
        TM2.Cfg (fun _ : Stack q => Bool) Label Unit) =
      ⟨none, (), Function.update S
        SourceClauseRowWriterOperands.rowIndex
        (true :: S SourceClauseRowWriterOperands.rowIndex)⟩ := by
  simp [Function.iterate_succ_apply', Function.iterate_succ_apply,
    advance, TM2.step, program, TM2.stepAux]

theorem row_increment {q : ℕ} (S : Stack q → List Bool) (r : ℕ)
    (h : S SourceClauseRowWriterOperands.rowIndex =
      List.replicate r true) :
    (Function.update S SourceClauseRowWriterOperands.rowIndex
      (true :: S SourceClauseRowWriterOperands.rowIndex))
      SourceClauseRowWriterOperands.rowIndex =
      List.replicate (r + 1) true := by
  simp [h, List.replicate_succ]

theorem other_preserved {q : ℕ} (S : Stack q → List Bool)
    (x : Stack q) (h : x ≠ SourceClauseRowWriterOperands.rowIndex) :
    (Function.update S SourceClauseRowWriterOperands.rowIndex
      (true :: S SourceClauseRowWriterOperands.rowIndex)) x = S x := by
  simp [Function.update, h]

end EthInapproximability.CurrentPaper.SourceClauseRowWriterRowAdvance
