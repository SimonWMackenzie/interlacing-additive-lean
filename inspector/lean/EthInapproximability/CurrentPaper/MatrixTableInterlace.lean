import EthInapproximability.CurrentPaper.MatrixTableInterlaceEntry
import EthInapproximability.CurrentPaper.MatrixTableInterlaceCodes
import EthInapproximability.CurrentPaper.MatrixTableWriter

/-!
# Literal row-major classical interlace

Frozen v8 `def:paper-interlace` and Appendix B `thm:paper-materialization`.
The writer enumerates every output cell; its callback is the fixed physical
row-split, variable-index digit-select and old-table lookup program.
-/

namespace EthInapproximability.CurrentPaper.MatrixTableInterlace

open Turing BitMachineEncoding
open MatrixTableInterlaceCodes

abbrev CellStack := MatrixTableWriter.CellStack 20
abbrev Label := MatrixTableInterlaceEntry.Label
abbrev Control := MatrixTableInterlaceEntry.Control

private def writerPerm : MatrixTableInterlaceEntry.Stack ≃ MatrixTableInterlaceEntry.Stack where
  toFun := ![1,2,3,4,5,6,7,9,10,11,12,13,14,15,16,17,18,19,21,22,0,8,20]
  invFun := ![20,0,1,2,3,4,5,6,21,7,8,9,10,11,12,13,14,15,16,17,22,18,19]
  left_inv k := by fin_cases k <;> rfl
  right_inv k := by fin_cases k <;> rfl

def writerSlots : CellStack ≃ MatrixTableInterlaceEntry.Stack :=
  finSumFinEquiv.trans writerPerm

def entryProgram (l : Label) : TM2.Stmt (fun _ : CellStack => Bool) Label Control :=
  renameStmt writerSlots.symm (Equiv.refl _) (Equiv.refl _)
    (MatrixTableInterlaceEntry.program l)

def persistentBank (rows cols : ℕ) (source : List Bool) : Fin 20 → List Bool :=
  ![List.replicate rows true,[],[],[],[],[],[],List.replicate cols true,
    [],[],[],[],[],[],[],[],[],source,[],[]]

theorem input_frame (rows cols x y : ℕ) (source answer : List Bool)
    (l : Option Label) (s : Control) :
    renameCfg writerSlots.symm (Equiv.refl _) (Equiv.refl _)
      (MatrixTableInterlaceEntry.cfg l s (List.replicate x true)
        (List.replicate rows true) [] (List.replicate y true)
        (List.replicate cols true) [] source answer) =
      MatrixTableWriter.cellCfg l s (persistentBank rows cols source) x y answer := by
  unfold renameCfg MatrixTableInterlaceEntry.cfg MatrixTableWriter.cellCfg
  cases l with
  | none =>
      apply congrArg
        (fun S => (⟨none,s,S⟩ : TM2.Cfg (fun _ : CellStack => Bool) Label Control))
      funext k
      cases k with
      | inl k => fin_cases k <;> rfl
      | inr k => fin_cases k <;> rfl
  | some l =>
      apply congrArg
        (fun S => (⟨some l,s,S⟩ : TM2.Cfg (fun _ : CellStack => Bool) Label Control))
      funext k
      cases k with
      | inl k => fin_cases k <;> rfl
      | inr k => fin_cases k <;> rfl

theorem renamed_run {rows cols x y t : ℕ} {source answer : List Bool}
    (h : MatrixTableInterlaceEntry.run t
      (MatrixTableInterlaceEntry.cfg (some MatrixTableInterlaceEntry.start)
        MatrixTableInterlaceEntry.initial (List.replicate x true)
        (List.replicate rows true) [] (List.replicate y true)
        (List.replicate cols true) [] source []) =
      MatrixTableInterlaceEntry.cfg none MatrixTableInterlaceEntry.initial
        (List.replicate x true) (List.replicate rows true) []
        (List.replicate y true) (List.replicate cols true) [] source answer) :
    ((advance entryProgram)^[t])
      (MatrixTableWriter.cellCfg (some MatrixTableInterlaceEntry.start)
        MatrixTableInterlaceEntry.initial (persistentBank rows cols source) x y []) =
      MatrixTableWriter.cellCfg none MatrixTableInterlaceEntry.initial
        (persistentBank rows cols source) x y answer := by
  have hr := rename_run writerSlots.symm (Equiv.refl Label) (Equiv.refl Control)
    MatrixTableInterlaceEntry.program
    (MatrixTableInterlaceEntry.cfg (some MatrixTableInterlaceEntry.start)
      MatrixTableInterlaceEntry.initial (List.replicate x true)
      (List.replicate rows true) [] (List.replicate y true)
      (List.replicate cols true) [] source []) t
  change ((advance entryProgram)^[t]) _ =
    renameCfg writerSlots.symm (Equiv.refl _) (Equiv.refl _)
      (MatrixTableInterlaceEntry.run t _) at hr
  rw [h, input_frame, input_frame] at hr
  exact hr

def uniformBound (blocks rows cols sourceLength : ℕ) : ℕ :=
  MatrixTableInterlaceEntry.callbackBound (blocks*rows) rows (cols^blocks) cols sourceLength

theorem entry_runs (blocks rows cols : ℕ) (source : List Bool) :
    MatrixTableWriter.EntryRuns entryProgram MatrixTableInterlaceEntry.start
      MatrixTableInterlaceEntry.initial (persistentBank rows cols source)
      (blocks*rows) (cols^blocks) (uniformBound blocks rows cols source.length)
      (MatrixTableInterlaceCodes.entry rows cols source) := by
  intro x hx y hy
  obtain ⟨t,ht,he⟩ := MatrixTableInterlaceEntry.entry_run x rows y cols source []
  refine ⟨t, ?_, MatrixTableInterlaceEntry.initial, renamed_run he⟩
  let localSize := x+rows+y+cols+source.length+1
  let globalSize := blocks*rows+rows+cols^blocks+cols+source.length+1
  have hs : localSize ≤ globalSize := by dsimp [localSize,globalSize]; omega
  have hp := Nat.pow_le_pow_left hs 2
  exact ht.trans (Nat.mul_le_mul_left 128 hp)

theorem interlace_table (blocks rows cols : ℕ) (source output : List Bool) :
    ∃ t ≤ MatrixTableWriter.writerBound (blocks*rows) (cols^blocks)
      (uniformBound blocks rows cols source.length), ∃ v,
      MatrixTableWriter.run entryProgram MatrixTableInterlaceEntry.start
        MatrixTableInterlaceEntry.initial t
        (MatrixTableWriter.cfg (some (.inr (.copy .rows)))
          (MatrixTableInterlaceEntry.initial,none)
          (MatrixTableWriter.ready (persistentBank rows cols source)
            (blocks*rows) (cols^blocks) 0 0 0 0 [] output)) =
      MatrixTableWriter.cfg none v
        (MatrixTableWriter.ready (persistentBank rows cols source)
          (blocks*rows) (cols^blocks) 0 0 0 0 []
          (MatrixTableWriter.tableWord
            (MatrixTableInterlaceCodes.entry rows cols source)
            (cols^blocks) 0 (blocks*rows) ++ output)) := by
  exact MatrixTableWriter.write_table entryProgram MatrixTableInterlaceEntry.start
    MatrixTableInterlaceEntry.initial (persistentBank rows cols source)
    (blocks*rows) (cols^blocks) (uniformBound blocks rows cols source.length)
    (MatrixTableInterlaceCodes.entry rows cols source)
    (entry_runs blocks rows cols source) output

def interlaced {rows cols blocks : ℕ} (f : Fin rows → Fin cols → Bool) :
    Fin (blocks*rows) → Fin (cols^blocks) → Bool :=
  fun r c => Workspace.Types.Interlace.interlaceFun f blocks
    ((rowCode blocks rows).symm r) ((columnCode blocks cols).symm c)

theorem entry_rowMajor (blocks rows cols : ℕ)
    (f : Fin rows → Fin cols → Bool) (r : Fin (blocks*rows))
    (c : Fin (cols^blocks)) :
    MatrixTableInterlaceCodes.entry rows cols (MatrixMaterialization.rowMajor f)
      r.val c.val = interlaced f r c := by
  let ix := (rowCode blocks rows).symm r
  let ys := (columnCode blocks cols).symm c
  have h := MatrixTableInterlaceCodes.entry_rowMajor f ix.1 ix.2 ys
  simpa [ix,ys,interlaced] using h

theorem interlace_rowMajor (blocks rows cols : ℕ)
    (f : Fin rows → Fin cols → Bool) (output : List Bool) :
    ∃ t ≤ MatrixTableWriter.writerBound (blocks*rows) (cols^blocks)
      (uniformBound blocks rows cols (MatrixMaterialization.rowMajor f).length), ∃ v,
      MatrixTableWriter.run entryProgram MatrixTableInterlaceEntry.start
        MatrixTableInterlaceEntry.initial t
        (MatrixTableWriter.cfg (some (.inr (.copy .rows)))
          (MatrixTableInterlaceEntry.initial,none)
          (MatrixTableWriter.ready
            (persistentBank rows cols (MatrixMaterialization.rowMajor f))
            (blocks*rows) (cols^blocks) 0 0 0 0 [] output)) =
      MatrixTableWriter.cfg none v
        (MatrixTableWriter.ready
          (persistentBank rows cols (MatrixMaterialization.rowMajor f))
          (blocks*rows) (cols^blocks) 0 0 0 0 []
          (MatrixMaterialization.rowMajor (interlaced (blocks := blocks) f) ++ output)) := by
  exact MatrixTableWriter.write_rowMajor entryProgram MatrixTableInterlaceEntry.start
    MatrixTableInterlaceEntry.initial
    (persistentBank rows cols (MatrixMaterialization.rowMajor f))
    (blocks*rows) (cols^blocks)
    (uniformBound blocks rows cols (MatrixMaterialization.rowMajor f).length)
    (MatrixTableInterlaceCodes.entry rows cols (MatrixMaterialization.rowMajor f))
    (interlaced (blocks := blocks) f) (entry_rowMajor blocks rows cols f)
    (entry_runs blocks rows cols (MatrixMaterialization.rowMajor f)) output

/-- The charged runtime is polynomial in the unary counts, literal source
length, and actual output carrier sizes.  This is one interlace transform,
not a uniform bound for an unbounded chain of transforms. -/
theorem interlace_bound_polynomial (blocks rows cols sourceLength : ℕ) :
    MatrixTableWriter.writerBound (blocks*rows) (cols^blocks)
      (uniformBound blocks rows cols sourceLength) ≤
      512*(blocks+rows+cols+sourceLength+blocks*rows+cols^blocks+1)^4 := by
  let R := blocks*rows
  let C := cols^blocks
  let S := blocks+rows+cols+sourceLength+R+C+1
  let M := R+rows+C+cols+sourceLength+1
  have hS : 1 ≤ S := by dsimp [S]; omega
  have hR : R ≤ S := by dsimp [S]; omega
  have hC : C ≤ S := by dsimp [S]; omega
  have hM : M ≤ S := by dsimp [M,S]; omega
  have hM2 := Nat.pow_le_pow_left hM 2
  have hT : uniformBound blocks rows cols sourceLength ≤ 128*S^2 := by
    exact Nat.mul_le_mul_left 128 hM2
  have hRC : R*C ≤ S^2 := by nlinarith [Nat.mul_le_mul hR hC]
  have hRT : (R*C)*(uniformBound blocks rows cols sourceLength) ≤
      128*S^4 := by
    have h := Nat.mul_le_mul hRC hT
    nlinarith
  have hS2 : 1 ≤ S^2 := by nlinarith
  have hS4 : 1 ≤ S^4 := by nlinarith
  have hS2S4 : S^2 ≤ S^4 := by
    nlinarith [Nat.mul_le_mul (le_refl (S^2)) hS2]
  have hSS4 : S ≤ S^4 := by
    have hSS2 : S ≤ S^2 := by nlinarith [Nat.mul_le_mul (le_refl S) hS]
    omega
  change R*(C*(uniformBound blocks rows cols sourceLength+2)+4*C+8)+5 ≤
    512*S^4
  nlinarith

end EthInapproximability.CurrentPaper.MatrixTableInterlace
