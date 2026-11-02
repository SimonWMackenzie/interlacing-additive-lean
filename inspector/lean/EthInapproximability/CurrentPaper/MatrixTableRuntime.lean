import EthInapproximability.CurrentPaper.MatrixEntryRuntime
import EthInapproximability.CurrentPaper.MatrixTableWriter
import EthInapproximability.CurrentPaper.MatrixTableRuntimeBounds

/-!
# Wiring the exact entry program into the actual row-major writer

The persistent bank is finite and excludes the two physical indices and the
answer stack. The wiring below is a literal stack renaming of the single
entry program; it does not replace entry evaluation with a lookup oracle.
-/

namespace EthInapproximability.CurrentPaper.MatrixTableRuntime

open Turing BitMachineEncoding

abbrev CellStack := MatrixTableWriter.CellStack 51
abbrev Label := MatrixEntryProgram.Label
abbrev Control := MatrixEntryProgram.Control

private def permutation : Fin 54 ≃ Fin 54 where
  toFun := ![2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18,
    19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33,
    35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53,
    0, 1, 34]
  invFun := ![51, 52, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14,
    15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 53,
    32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50]
  left_inv k := by fin_cases k <;> rfl
  right_inv k := by fin_cases k <;> rfl

def slots : CellStack ≃ MatrixEntryProgram.Stack := finSumFinEquiv.trans permutation

def entryProgram (l : Label) : TM2.Stmt (fun _ : CellStack => Bool) Label Control :=
  renameStmt slots.symm (Equiv.refl _) (Equiv.refl _) (MatrixEntryProgram.program l)

def persistentBank (a d N₁ N₂ : ℕ) (data : MatrixMaterialization.ExactBitData) :
    Fin 51 → List Bool :=
  fun k => MatrixEntryData.input a d N₁ N₂ 0 0 data [] (slots (.inl k))

theorem input_frame (a d N₁ N₂ x y : ℕ) (data : MatrixMaterialization.ExactBitData)
    (l : Option Label) (s : Control) (answer : List Bool) :
    renameCfg slots.symm (Equiv.refl _) (Equiv.refl _)
      (MatrixEntryProgram.cfg l s (MatrixEntryData.input a d N₁ N₂ x y data answer)) =
      MatrixTableWriter.cellCfg l s (persistentBank a d N₁ N₂ data) x y answer := by
  simp only [renameCfg, MatrixEntryProgram.cfg, MatrixTableWriter.cellCfg,
    Equiv.refl_apply]
  have hl : Option.map (Equiv.refl Label) l = l := by cases l <;> rfl
  rw [hl]
  apply congrArg (fun S => (⟨l, s, S⟩ : TM2.Cfg (fun _ : CellStack => Bool) Label Control))
  funext k
  cases k with
  | inl k => fin_cases k <;> rfl
  | inr k => fin_cases k <;> rfl

theorem renamed_run {a d N₁ N₂ x y t : ℕ} {data : MatrixMaterialization.ExactBitData}
    {s : Control} {answer : List Bool}
    (h : MatrixEntryProgram.run t
      (MatrixEntryProgram.cfg (some MatrixEntryProgram.start) MatrixEntryProgram.initial
        (MatrixEntryData.input a d N₁ N₂ x y data [])) =
      MatrixEntryProgram.cfg none s (MatrixEntryData.input a d N₁ N₂ x y data answer)) :
    ((advance entryProgram)^[t])
      (MatrixTableWriter.cellCfg (some MatrixEntryProgram.start) MatrixEntryProgram.initial
        (persistentBank a d N₁ N₂ data) x y []) =
      MatrixTableWriter.cellCfg none s (persistentBank a d N₁ N₂ data) x y answer := by
  have hr := rename_run slots.symm (Equiv.refl Label) (Equiv.refl Control)
    MatrixEntryProgram.program
    (MatrixEntryProgram.cfg (some MatrixEntryProgram.start) MatrixEntryProgram.initial
      (MatrixEntryData.input a d N₁ N₂ x y data [])) t
  change ((advance entryProgram)^[t]) _ =
    renameCfg slots.symm (Equiv.refl _) (Equiv.refl _) (MatrixEntryProgram.run t _) at hr
  rw [h, input_frame, input_frame] at hr
  exact hr

/-- The value requested by the writer's natural-number counters. Values
outside the rectangular carrier are irrelevant to its bounded loop. -/
def exactEntry {a d N₁ N₂ n : ℕ} (ha : 2 ≤ a)
    (C₁ : ExactConstruction.FirstFamily a N₁) (C₂ : ExactConstruction.SecondFamily a d N₂)
    (v : Fin n → Fin d → Bool) (cap : ∀ α, (Construction.activeItems v α).card ≤ 2)
    (x y : ℕ) : Bool :=
  if hx : x < 4 * N₂ + n then
    if hy : y < 8 * (d * N₁) ^ 4 then
      ExactConstruction.matrix ha C₁ C₂ v cap
        ((MatrixMaterialization.rowCode N₂ n).symm ⟨x, hx⟩)
        ((MatrixMaterialization.columnCode d N₁).symm ⟨y, hy⟩)
    else false
  else false

theorem exactEntry_on_carrier {a d N₁ N₂ n : ℕ} (ha : 2 ≤ a)
    (C₁ : ExactConstruction.FirstFamily a N₁) (C₂ : ExactConstruction.SecondFamily a d N₂)
    (v : Fin n → Fin d → Bool) (cap : ∀ α, (Construction.activeItems v α).card ≤ 2)
    (x : Fin (4 * N₂ + n)) (y : Fin (8 * (d * N₁) ^ 4)) :
    exactEntry ha C₁ C₂ v cap x.val y.val =
      MatrixMaterialization.encodedMatrix (MatrixMaterialization.store C₁ C₂ v) ha x y := by
  simp only [exactEntry, dif_pos x.isLt, dif_pos y.isLt]
  let r := (MatrixMaterialization.rowCode N₂ n).symm x
  let c := (MatrixMaterialization.columnCode d N₁).symm y
  have hcap : ∀ α, (Construction.activeItems
      (MatrixMaterialization.sourceAccessor (MatrixMaterialization.store C₁ C₂ v) n d) α).card ≤ 2 := by
    simpa only [MatrixMaterialization.store_sourceAccessor] using cap
  have h := MatrixMaterialization.encodedMatrix_correct
    (MatrixMaterialization.store C₁ C₂ v) ha hcap r c
  simpa only [r, c, Equiv.apply_symm_apply, MatrixMaterialization.store_firstAccessor,
    MatrixMaterialization.store_secondAccessor, MatrixMaterialization.store_sourceAccessor]
    using h.symm

/-- Each call of the writer invokes the renamed fixed Fin54 entry controller. -/
theorem entry_runs {a d N₁ N₂ n : ℕ} (ha : 2 ≤ a)
    (C₁ : ExactConstruction.FirstFamily a N₁) (C₂ : ExactConstruction.SecondFamily a d N₂)
    (v : Fin n → Fin d → Bool) (cap : ∀ α, (Construction.activeItems v α).card ≤ 2) :
    MatrixTableWriter.EntryRuns entryProgram MatrixEntryProgram.start MatrixEntryProgram.initial
      (persistentBank a d N₁ N₂ (MatrixMaterialization.storeBits C₁ C₂ v))
      (4 * N₂ + n) (8 * (d * N₁) ^ 4) (MatrixEntryRuntime.bound a d N₁ N₂ n)
      (exactEntry ha C₁ C₂ v cap) := by
  intro x hx y hy
  let r := (MatrixMaterialization.rowCode N₂ n).symm ⟨x, hx⟩
  let c := (MatrixMaterialization.columnCode d N₁).symm ⟨y, hy⟩
  obtain ⟨t, ht, h⟩ := MatrixEntryRuntime.entry_run ha C₁ C₂ v cap r c []
  have hr : (MatrixMaterialization.rowCode N₂ n r).val = x := by
    simp only [r, Equiv.apply_symm_apply]
  have hc : (MatrixMaterialization.columnCode d N₁ c).val = y := by
    simp only [c, Equiv.apply_symm_apply]
  rw [hr, hc] at h
  have hv : ExactConstruction.matrix ha C₁ C₂ v cap r c =
      exactEntry ha C₁ C₂ v cap x y := by
    simp only [exactEntry, dif_pos hx, dif_pos hy, r, c]
  rw [hv] at h
  exact ⟨t, ht, MatrixEntryProgram.initial, renamed_run h⟩

/-- The concrete row-major writer outputs every bit of the exact-NP matrix.
Its bank is the literal three-array payload, and its cell callback is the
renamed physical entry program above. -/
theorem write_bitTable {a d N₁ N₂ n : ℕ} (ha : 2 ≤ a)
    (C₁ : ExactConstruction.FirstFamily a N₁) (C₂ : ExactConstruction.SecondFamily a d N₂)
    (v : Fin n → Fin d → Bool) (cap : ∀ α, (Construction.activeItems v α).card ≤ 2)
    (output : List Bool) :
    ∃ t ≤ MatrixTableRuntimeBounds.bound a d N₁ N₂ n, ∃ state,
      MatrixTableWriter.run entryProgram MatrixEntryProgram.start MatrixEntryProgram.initial t
        (MatrixTableWriter.cfg (some (.inr (.copy .rows)))
          (MatrixEntryProgram.initial, none)
          (MatrixTableWriter.ready
            (persistentBank a d N₁ N₂ (MatrixMaterialization.storeBits C₁ C₂ v))
            (4 * N₂ + n) (8 * (d * N₁) ^ 4) 0 0 0 0 [] output)) =
      MatrixTableWriter.cfg none state
        (MatrixTableWriter.ready
          (persistentBank a d N₁ N₂ (MatrixMaterialization.storeBits C₁ C₂ v))
          (4 * N₂ + n) (8 * (d * N₁) ^ 4) 0 0 0 0 []
          (MatrixMaterialization.bitTable (d := d) (N₁ := N₁) (N₂ := N₂) (n := n)
            (MatrixMaterialization.storeBits C₁ C₂ v) ha ++ output)) := by
  let data := MatrixMaterialization.storeBits C₁ C₂ v
  let f := MatrixMaterialization.encodedMatrix (d := d) (N₁ := N₁) (N₂ := N₂)
    (n := n) (MatrixMaterialization.store C₁ C₂ v) ha
  obtain ⟨t, ht, state, hrun⟩ := MatrixTableWriter.write_rowMajor entryProgram
    MatrixEntryProgram.start MatrixEntryProgram.initial
    (persistentBank a d N₁ N₂ data) (4 * N₂ + n) (8 * (d * N₁) ^ 4)
    (MatrixEntryRuntime.bound a d N₁ N₂ n) (exactEntry ha C₁ C₂ v cap) f
    (exactEntry_on_carrier ha C₁ C₂ v cap)
    (entry_runs ha C₁ C₂ v cap) output
  refine ⟨t, ht.trans (MatrixTableRuntimeBounds.writer_bound a d N₁ N₂ n), state, ?_⟩
  simpa only [f, data, MatrixMaterialization.table,
    MatrixMaterialization.bitTable_storeBits] using hrun

end EthInapproximability.CurrentPaper.MatrixTableRuntime
