import EthInapproximability.CurrentPaper.MatrixTableLookup
import EthInapproximability.CurrentPaper.MatrixTableWriter

/-!
# Physical row-major transposition

Source: frozen v8 `B-effectivity-details.tex`, proof of
`thm:paper-materialization` ("Transposition gives N").  The input is a
literal row-major bit table, not an oracle.  The writer enumerates output
coordinates, while the fixed Boolean-stack callback computes the reversed
row-major address, reads the source table, and restores its workspace.
-/

namespace EthInapproximability.CurrentPaper.MatrixTableTranspose

open Turing BitMachineEncoding

abbrev CellStack := MatrixTableWriter.CellStack 7
abbrev Label := MatrixTableLookup.Label
abbrev Control := MatrixTableLookup.Control

private def permutation : Fin 10 ≃ Fin 10 where
  toFun := ![1,3,4,5,6,8,9,2,0,7]
  invFun := ![8,0,7,1,2,3,4,9,5,6]
  left_inv k := by fin_cases k <;> rfl
  right_inv k := by fin_cases k <;> rfl

/-- The writer's row index is the source column, and its column index is
the source row.  The remaining seven slots are persistent callback data. -/
def slots : CellStack ≃ MatrixTableLookup.Stack := finSumFinEquiv.trans permutation

def entryProgram (l : Label) : TM2.Stmt (fun _ : CellStack => Bool) Label Control :=
  renameStmt slots.symm (Equiv.refl _) (Equiv.refl _) (MatrixTableLookup.program l)

def persistentBank (width : ℕ) (source : List Bool) : Fin 7 → List Bool :=
  ![List.replicate width true, [], [], [], source, [], []]

theorem input_frame (width x y : ℕ) (source answer : List Bool)
    (l : Option Label) (s : Control) :
    renameCfg slots.symm (Equiv.refl _) (Equiv.refl _)
      (MatrixTableLookup.cfg l s (List.replicate y true)
        (List.replicate width true) (List.replicate x true) [] source answer) =
      MatrixTableWriter.cellCfg l s (persistentBank width source) x y answer := by
  unfold renameCfg MatrixTableLookup.cfg MatrixTableWriter.cellCfg
  cases l with
  | none =>
      apply congrArg
        (fun S => (⟨none, s, S⟩ : TM2.Cfg (fun _ : CellStack => Bool) Label Control))
      funext k
      cases k with
      | inl k => fin_cases k <;> rfl
      | inr k => fin_cases k <;> rfl
  | some l =>
      apply congrArg
        (fun S => (⟨some l, s, S⟩ : TM2.Cfg (fun _ : CellStack => Bool) Label Control))
      funext k
      cases k with
      | inl k => fin_cases k <;> rfl
      | inr k => fin_cases k <;> rfl

theorem renamed_run {width x y t : ℕ} {source answer : List Bool} {s : Control}
    (h : MatrixTableLookup.run t
      (MatrixTableLookup.cfg (some MatrixTableLookup.start) MatrixTableLookup.initial
        (List.replicate y true) (List.replicate width true)
        (List.replicate x true) [] source []) =
      MatrixTableLookup.cfg none s (List.replicate y true)
        (List.replicate width true) (List.replicate x true) [] source answer) :
    ((advance entryProgram)^[t])
      (MatrixTableWriter.cellCfg (some MatrixTableLookup.start)
        MatrixTableLookup.initial (persistentBank width source) x y []) =
      MatrixTableWriter.cellCfg none s (persistentBank width source) x y answer := by
  have hr := rename_run slots.symm (Equiv.refl Label) (Equiv.refl Control)
    MatrixTableLookup.program
    (MatrixTableLookup.cfg (some MatrixTableLookup.start) MatrixTableLookup.initial
      (List.replicate y true) (List.replicate width true)
      (List.replicate x true) [] source []) t
  change ((advance entryProgram)^[t]) _ =
    renameCfg slots.symm (Equiv.refl _) (Equiv.refl _) (MatrixTableLookup.run t _) at hr
  rw [h, input_frame, input_frame] at hr
  exact hr

/-- Uniform charged callback time for every transposed output coordinate. -/
def callbackBound (rows cols sourceLength : ℕ) : ℕ :=
  128 * (rows + cols + sourceLength + 1) ^ 2

theorem entry_runs (rows cols : ℕ) (source : List Bool) :
    MatrixTableWriter.EntryRuns entryProgram MatrixTableLookup.start
      MatrixTableLookup.initial (persistentBank cols source)
      cols rows (callbackBound rows cols source.length)
      (fun x y => source[y * cols + x]?.getD false) := by
  intro x hx y hy
  obtain ⟨t, ht, he⟩ := MatrixTableLookup.lookup_run y cols x source []
  refine ⟨t, ?_, MatrixTableLookup.initial, renamed_run he⟩
  let n := rows + cols + source.length + 1
  have hn : y + cols + x + source.length + 1 ≤ 2 * n := by
    dsimp [n]
    omega
  have hsq := Nat.pow_le_pow_left hn 2
  dsimp [callbackBound]
  nlinarith

/-- A literal source table is transposed by a fixed program.  The writer
physically enumerates all cells and restores its dimensions and payload. -/
theorem transpose_table (rows cols : ℕ) (source output : List Bool) :
    ∃ t ≤ MatrixTableWriter.writerBound cols rows
      (callbackBound rows cols source.length), ∃ v,
      MatrixTableWriter.run entryProgram MatrixTableLookup.start MatrixTableLookup.initial t
        (MatrixTableWriter.cfg (some (.inr (.copy .rows)))
          (MatrixTableLookup.initial, none)
          (MatrixTableWriter.ready (persistentBank cols source)
            cols rows 0 0 0 0 [] output)) =
      MatrixTableWriter.cfg none v
        (MatrixTableWriter.ready (persistentBank cols source)
          cols rows 0 0 0 0 []
          (MatrixTableWriter.tableWord
            (fun x y => source[y * cols + x]?.getD false) rows 0 cols ++ output)) := by
  exact MatrixTableWriter.write_table entryProgram MatrixTableLookup.start
    MatrixTableLookup.initial (persistentBank cols source) cols rows
    (callbackBound rows cols source.length)
    (fun x y => source[y * cols + x]?.getD false)
    (entry_runs rows cols source) output

/-- When the input is an actual matrix's row-major table, the output is
the literal row-major table of its transpose, even with an old suffix. -/
theorem transpose_rowMajor (rows cols : ℕ)
    (f : Fin rows → Fin cols → Bool) (output : List Bool) :
    ∃ t ≤ MatrixTableWriter.writerBound cols rows
      (callbackBound rows cols (MatrixMaterialization.rowMajor f).length), ∃ v,
      MatrixTableWriter.run entryProgram MatrixTableLookup.start MatrixTableLookup.initial t
        (MatrixTableWriter.cfg (some (.inr (.copy .rows)))
          (MatrixTableLookup.initial, none)
          (MatrixTableWriter.ready (persistentBank cols (MatrixMaterialization.rowMajor f))
            cols rows 0 0 0 0 [] output)) =
      MatrixTableWriter.cfg none v
        (MatrixTableWriter.ready (persistentBank cols (MatrixMaterialization.rowMajor f))
          cols rows 0 0 0 0 []
          (MatrixMaterialization.rowMajor (fun x y => f y x) ++ output)) := by
  apply MatrixTableWriter.write_rowMajor entryProgram MatrixTableLookup.start
    MatrixTableLookup.initial (persistentBank cols (MatrixMaterialization.rowMajor f))
    cols rows (callbackBound rows cols (MatrixMaterialization.rowMajor f).length)
    (fun x y => (MatrixMaterialization.rowMajor f)[y * cols + x]?.getD false)
    (fun x y => f y x)
  · intro x y
    have he := MatrixMaterialization.rowMajor_entry f y x
    rw [he]
    rfl
  · exact entry_runs rows cols (MatrixMaterialization.rowMajor f)

theorem transpose_bound_polynomial (rows cols sourceLength : ℕ) :
    MatrixTableWriter.writerBound cols rows (callbackBound rows cols sourceLength) ≤
      256 * (rows + cols + sourceLength + 1) ^ 4 := by
  let n := rows + cols + sourceLength + 1
  have hn : 1 ≤ n := by dsimp [n]; omega
  have hr : rows ≤ n := by dsimp [n]; omega
  have hc : cols ≤ n := by dsimp [n]; omega
  have hrc : cols * rows ≤ n ^ 2 := by
    nlinarith [Nat.mul_le_mul hc hr]
  have hq : 1 ≤ n ^ 2 := by nlinarith
  have hn2 : n ^ 2 ≤ n ^ 4 := by
    nlinarith [Nat.mul_le_mul (le_refl (n ^ 2)) hq]
  have hn_n2 : n ≤ n ^ 2 := by
    nlinarith [Nat.mul_le_mul (le_refl n) hn]
  have hn_n4 : n ≤ n ^ 4 := by omega
  have hmain : (cols * rows) * n ^ 2 ≤ n ^ 4 := by
    nlinarith [Nat.mul_le_mul hrc (le_refl (n ^ 2))]
  change cols * (rows * (128 * n ^ 2 + 2) + 4 * rows + 8) + 5 ≤ 256 * n ^ 4
  calc
    cols * (rows * (128 * n ^ 2 + 2) + 4 * rows + 8) + 5 =
        128 * ((cols * rows) * n ^ 2) + 6 * (cols * rows) + 8 * cols + 5 := by ring
    _ ≤ 256 * n ^ 4 := by nlinarith

end EthInapproximability.CurrentPaper.MatrixTableTranspose
