import EthInapproximability.CurrentPaper.SourceClauseRowWriterGateRun

/-!
# Whole-writer physical cleanup between source literals

The writer retains the checked row, reversed payload, output suffix, unary
count, unary vertex count, and unary processed-row index. Every other stack
is physically emptied. This cleanup is shared by unit and three-clause gate
calls and charges every bit popped from the finite complement.
-/

namespace EthInapproximability.CurrentPaper.SourceClauseRowWriterCleanup

open Turing BitMachineEncoding
open scoped Classical

abbrev Stack (q : ℕ) := SourceClauseRowWriterOperands.Stack q

noncomputable instance (q : ℕ) : Fintype (Stack q) := Fintype.ofFinite _

def rowCell {q : ℕ} (x : SourceCSPRowQueryFrame.Stack q) : Stack q :=
  .inl (.inl (.inl x))

def savedCell {q : ℕ} : Stack q := .inl (.inl (.inr 0))
def outputCell {q : ℕ} : Stack q := .inl (.inl (.inr 1))
def countCell {q : ℕ} : Stack q := .inl (.inl (.inr 2))

noncomputable def keep (q : ℕ) : Finset (Stack q) :=
  (Finset.univ.image (rowCell (q := q))) ∪
    {savedCell, outputCell, countCell,
      SourceClauseRowWriterOperands.vertex,
      SourceClauseRowWriterOperands.rowIndex}

theorem row_mem {q : ℕ} (x : SourceCSPRowQueryFrame.Stack q) :
    rowCell x ∈ keep q := by
  apply Finset.mem_union_left
  exact Finset.mem_image.mpr ⟨x, Finset.mem_univ _, rfl⟩

theorem saved_mem {q : ℕ} : (savedCell : Stack q) ∈ keep q := by
  simp [keep]
theorem output_mem {q : ℕ} : (outputCell : Stack q) ∈ keep q := by
  simp [keep]
theorem count_mem {q : ℕ} : (countCell : Stack q) ∈ keep q := by
  simp [keep]
theorem vertex_mem {q : ℕ} :
    SourceClauseRowWriterOperands.vertex (q := q) ∈ keep q := by
  simp [keep]
theorem row_index_mem {q : ℕ} :
    SourceClauseRowWriterOperands.rowIndex (q := q) ∈ keep q := by
  simp [keep]

noncomputable def clean {q : ℕ} (S : Stack q → List Bool) :
    Stack q → List Bool :=
  SourceClauseClearExcept.result (keep q) S

theorem retained {q : ℕ} (S : Stack q → List Bool)
    (x : Stack q) (hx : x ∈ keep q) : clean S x = S x :=
  SourceClauseClearExcept.retained (keep q) S x hx

theorem emptied {q : ℕ} (S : Stack q → List Bool)
    (x : Stack q) (hx : x ∉ keep q) : clean S x = [] :=
  SourceClauseClearExcept.emptied (keep q) S x hx

theorem run {q : ℕ} (S : Stack q → List Bool) :
    ((advance (SourceClauseClearExcept.program (keep q)))^[
      (∑ i : Fin (SourceClauseClearExcept.workCount (keep q)),
        (S (SourceClauseClearExcept.workBank (keep q) i)).length) +
      SourceClauseClearExcept.workCount (keep q) + 2])
      (⟨some (.clear 0), ((), none), S⟩ :
        TM2.Cfg (fun _ : Stack q => Bool)
          (SourceClauseClearExcept.Label
            (SourceClauseClearExcept.workCount (keep q)))
          (Unit × Option Bool)) =
      ⟨none, ((), none), clean S⟩ :=
  SourceClauseClearExcept.run (keep q) S

end EthInapproximability.CurrentPaper.SourceClauseRowWriterCleanup
