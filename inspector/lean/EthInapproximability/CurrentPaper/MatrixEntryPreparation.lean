import EthInapproximability.CurrentPaper.BitMachineCopy
import EthInapproximability.CurrentPaper.MatrixRowDecode
import EthInapproximability.CurrentPaper.MatrixColumnHeader

/-!
# Physical preparation of a matrix-entry query

Source: locked v8 Appendix B, `thm:paper-materialization`.
A fixed controller copies the literal row and column counters, decodes the
copies, and computes the source-row header from the column. The originals
and four scalar registers are preserved.

The 26-stack bank is explicit: originals 0/1; scalars row-cut, N₂, base, N₁
on 2/3/4/5; row work 6, scratch 7/8, template index 9, scratch 10;
column work 11, scratch 12/13, family indices 2/3/1/0 on 14/15/16/17;
scratch 18; coordinates 3/2/1/0 on 19/20/21/22; tail scratch 23;
copy scratch 24; arbitrary preserved stack 25. All scratch is empty at exit.
The scalar registers are preloaded. This is not yet the packed-input endpoint.
-/

namespace EthInapproximability.CurrentPaper.MatrixEntryPreparation

open Turing BitMachineEncoding BitMachineComposition BitMachineSubroutine
open BitMachineSubroutineRenaming

abbrev CLabel := BitMachineCopy.Label
abbrev RLabel := MatrixRowDecode.Label
abbrev HLabel := MatrixColumnHeader.Label
abbrev Label := CLabel ⊕ (CLabel ⊕ (RLabel ⊕ HLabel))
abbrev Control := Option Bool × (Option Bool × (MatrixRowDecode.Control × MatrixColumnHeader.Control))
abbrev Header := MatrixMaterializationMachine.Control
abbrev Config := TM2.Cfg (fun _ : Fin 26 => Bool) Label Control

private def copyRowPerm : Fin 26 ≃ Fin 26 where
  toFun i := ![0, 6, 24, 1, 2, 3, 4, 5, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 25] i
  invFun i := ![0, 3, 4, 5, 6, 7, 1, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 2, 25] i
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

def copyRowBank : Fin 3 ⊕ Fin 23 ≃ Fin 26 := finSumFinEquiv.trans copyRowPerm

private def copyColPerm : Fin 26 ≃ Fin 26 where
  toFun i := ![1, 11, 24, 0, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 25] i
  invFun i := ![3, 0, 4, 5, 6, 7, 8, 9, 10, 11, 12, 1, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 2, 25] i
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

def copyColBank : Fin 3 ⊕ Fin 23 ≃ Fin 26 := finSumFinEquiv.trans copyColPerm

private def rowPerm : Fin 26 ≃ Fin 26 where
  toFun i := ![6, 2, 7, 8, 3, 9, 10, 0, 1, 4, 5, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25] i
  invFun i := ![7, 8, 1, 4, 9, 10, 0, 2, 3, 5, 6, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25] i
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

def rowBank : Fin 7 ⊕ Fin 19 ≃ Fin 26 := finSumFinEquiv.trans rowPerm

private def columnPerm : Fin 26 ≃ Fin 26 where
  toFun i := ![11, 4, 12, 14, 15, 13, 16, 17, 18, 5, 19, 20, 21, 22, 23, 0, 1, 2, 3, 6, 7, 8, 9, 10, 24, 25] i
  invFun i := ![15, 16, 17, 18, 1, 9, 19, 20, 21, 22, 23, 0, 2, 5, 3, 4, 6, 7, 8, 10, 11, 12, 13, 14, 24, 25] i
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

def columnBank : Fin 15 ⊕ Fin 11 ≃ Fin 26 := finSumFinEquiv.trans columnPerm

def copyLabels : Label ≃ Label where
  toFun := Sum.elim (fun l => .inr (.inl l))
    (Sum.elim Sum.inl (fun l => .inr (.inr l)))
  invFun := Sum.elim (fun l => .inr (.inl l))
    (Sum.elim Sum.inl (fun l => .inr (.inr l)))
  left_inv l := by rcases l with l | (l | l) <;> rfl
  right_inv l := by rcases l with l | (l | l) <;> rfl

def copyControls : Control ≃ Control where
  toFun s := (s.2.1, s.1, s.2.2)
  invFun s := (s.2.1, s.1, s.2.2)
  left_inv _ := rfl
  right_inv _ := rfl

def rowLabels : RLabel ⊕ (CLabel ⊕ (CLabel ⊕ HLabel)) ≃ Label where
  toFun := Sum.elim (fun l => .inr (.inr (.inl l)))
    (Sum.elim Sum.inl (Sum.elim (fun l => .inr (.inl l)) (fun l => .inr (.inr (.inr l)))))
  invFun := Sum.elim (fun l => .inr (.inl l))
    (Sum.elim (fun l => .inr (.inr (.inl l)))
      (Sum.elim Sum.inl (fun l => .inr (.inr (.inr l)))))
  left_inv l := by rcases l with l | (l | (l | l)) <;> rfl
  right_inv l := by rcases l with l | (l | (l | l)) <;> rfl

def rowControls :
    MatrixRowDecode.Control × (Option Bool × (Option Bool × MatrixColumnHeader.Control)) ≃ Control where
  toFun s := (s.2.1, s.2.2.1, s.1, s.2.2.2)
  invFun s := (s.2.2.1, s.1, s.2.1, s.2.2.2)
  left_inv _ := rfl
  right_inv _ := rfl

def columnLabels : HLabel ⊕ (CLabel ⊕ (CLabel ⊕ RLabel)) ≃ Label where
  toFun := Sum.elim (fun l => .inr (.inr (.inr l)))
    (Sum.elim Sum.inl (Sum.elim (fun l => .inr (.inl l)) (fun l => .inr (.inr (.inl l)))))
  invFun := Sum.elim (fun l => .inr (.inl l))
    (Sum.elim (fun l => .inr (.inr (.inl l)))
      (Sum.elim (fun l => .inr (.inr (.inr l))) Sum.inl))
  left_inv l := by rcases l with l | (l | (l | l)) <;> rfl
  right_inv l := by rcases l with l | (l | (l | l)) <;> rfl

def columnControls :
    MatrixColumnHeader.Control × (Option Bool × (Option Bool × MatrixRowDecode.Control)) ≃ Control where
  toFun s := (s.2.1, s.2.2.1, s.2.2.2, s.1)
  invFun s := (s.2.2.2, s.1, s.2.1, s.2.2.1)
  left_inv _ := rfl
  right_inv _ := rfl

def rowInitial : MatrixRowDecode.Control := ((false, true), false, (0, false))
def headerControl (h : Header) : MatrixColumnHeader.Control :=
  (MatrixColumnHeader.decoderControl, h, none, none)

def columnStart : HLabel := .inl (.inl (.inl (.inl .start)))
def rowNext : CLabel ⊕ (CLabel ⊕ HLabel) := .inr (.inr columnStart)

def program : Label → TM2.Stmt (fun _ : Fin 26 => Bool) Label Control
  | .inl l => renameStmt copyRowBank (Equiv.refl _) (Equiv.refl _)
      (liftStmt (some (.inl BitMachineCopy.Label.scan)) (BitMachineCopy.program l))
  | .inr (.inl l) => renameStmt copyColBank copyLabels copyControls
      (liftStmt (some (.inr (.inl (.inl .scan)))) (BitMachineCopy.program l))
  | .inr (.inr (.inl l)) => renameStmt rowBank rowLabels rowControls
      (liftStmt (some rowNext) (MatrixRowDecode.program l))
  | .inr (.inr (.inr l)) => renameStmt columnBank columnLabels columnControls
      (liftStmt none (MatrixColumnHeader.program l))

structure Data where
  row : List Bool
  column : List Bool
  rowCut : List Bool
  n₂ : List Bool
  base : List Bool
  n₁ : List Bool
  rowWork : List Bool := []
  templateIndex : List Bool := []
  columnWork : List Bool := []
  family : Fin 4 → List Bool := fun _ => []
  coordinate : Fin 4 → List Bool := fun _ => []
  spare : List Bool := []

def Data.contents (v : Data) : Fin 26 → List Bool :=
  ![v.row, v.column, v.rowCut, v.n₂, v.base, v.n₁, v.rowWork, [], [], v.templateIndex,
    [], v.columnWork, [], [], v.family 2, v.family 3, v.family 1, v.family 0, [],
    v.coordinate 3, v.coordinate 2, v.coordinate 1, v.coordinate 0, [], [], v.spare]

def cfg (l : Option Label) (r : MatrixRowDecode.Control) (h : Header) (v : Data) : Config :=
  ⟨l, (none, none, r, headerControl h), v.contents⟩

def run (t : ℕ) (c : Config) := ((advance program)^[t]) c

private theorem run_add {c d : Config} {m : ℕ} (h : run m c = d) (n : ℕ) :
    run (m + n) c = run n d := by
  rw [Nat.add_comm m n]
  simp only [run, Function.iterate_add_apply] at h ⊢
  rw [h]

def Data.copyRowForeign (v : Data) : Fin 23 → List Bool :=
  ![v.column, v.rowCut, v.n₂, v.base, v.n₁, [], [], v.templateIndex, [],
    v.columnWork, [], [], v.family 2, v.family 3, v.family 1, v.family 0, [],
    v.coordinate 3, v.coordinate 2, v.coordinate 1, v.coordinate 0, [], v.spare]

def Data.copyColForeign (v : Data) : Fin 23 → List Bool :=
  ![v.row, v.rowCut, v.n₂, v.base, v.n₁, v.rowWork, [], [], v.templateIndex, [],
    [], [], v.family 2, v.family 3, v.family 1, v.family 0, [],
    v.coordinate 3, v.coordinate 2, v.coordinate 1, v.coordinate 0, [], v.spare]

def Data.rowForeign (v : Data) : Fin 19 → List Bool :=
  ![v.row, v.column, v.base, v.n₁, v.columnWork, [], [],
    v.family 2, v.family 3, v.family 1, v.family 0, [],
    v.coordinate 3, v.coordinate 2, v.coordinate 1, v.coordinate 0, [], [], v.spare]

def Data.columnForeign (v : Data) : Fin 11 → List Bool :=
  ![v.row, v.column, v.rowCut, v.n₂, v.rowWork, [], [], v.templateIndex, [], [], v.spare]

private theorem copyRow_cfg (l : Option CLabel) (r : MatrixRowDecode.Control)
    (h : Header) (v : Data) (target : List Bool) :
    renameCfg copyRowBank (Equiv.refl _) (Equiv.refl _)
      (liftCfg (some (.inl BitMachineCopy.Label.scan)) (none, r, headerControl h) v.copyRowForeign
        (BitMachineCopy.cfg l none v.row target [])) =
      cfg (l.elim (some (.inr (.inl .scan))) (fun l => some (.inl l))) r h
        { v with rowWork := target } := by
  cases l <;> apply congrArg (fun S => (⟨_, (none, none, r, headerControl h), S⟩ : Config)) <;>
    funext k <;> fin_cases k <;> rfl

private theorem copyCol_cfg (l : Option CLabel) (r : MatrixRowDecode.Control)
    (h : Header) (v : Data) (target : List Bool) :
    renameCfg copyColBank copyLabels copyControls
      (liftCfg (some (.inr (.inl (.inl .scan)))) (none, r, headerControl h) v.copyColForeign
        (BitMachineCopy.cfg l none v.column target [])) =
      cfg (l.elim (some (.inr (.inr (.inl (.inl .scan)))))
        (fun l => some (.inr (.inl l)))) r h { v with columnWork := target } := by
  cases l <;> apply congrArg (fun S => (⟨_, (none, none, r, headerControl h), S⟩ : Config)) <;>
    funext k <;> fin_cases k <;> rfl

private theorem row_cfg (l : Option RLabel) (r : MatrixRowDecode.Control)
    (h : Header) (v : Data) (rowWork z : List Bool) :
    renameCfg rowBank rowLabels rowControls
      (liftCfg (some rowNext) (none, none, headerControl h) v.rowForeign
        (MatrixRowDecode.cfg l r rowWork v.rowCut v.n₂ z [])) =
      cfg (l.elim (some (.inr (.inr (.inr columnStart))))
        (fun l => some (.inr (.inr (.inl l))))) r h { v with rowWork := rowWork, templateIndex := z } := by
  cases l <;> apply congrArg (fun S => (⟨_, (none, none, r, headerControl h), S⟩ : Config)) <;>
    funext k <;> fin_cases k <;> rfl

private theorem column_cfg (l : Option HLabel) (r : MatrixRowDecode.Control)
    (h : Header) (v : Data) (columnWork : List Bool) (family coordinate : Fin 4 → List Bool) :
    renameCfg columnBank columnLabels columnControls
      (liftCfg none (none, none, r) v.columnForeign
        (MatrixColumnHeader.cfg l h columnWork v.base (family 2) (family 3)
          (family 1) (family 0) [] v.n₁ (coordinate 3) (coordinate 2) (coordinate 1) (coordinate 0) [])) =
      cfg (l.map (fun l => .inr (.inr (.inr l)))) r h
        { v with columnWork := columnWork, family := family, coordinate := coordinate } := by
  cases l <;> apply congrArg (fun S => (⟨_, (none, none, r, headerControl h), S⟩ : Config)) <;>
    funext k <;> fin_cases k <;> rfl


def initialControl : Control :=
  (none, none, rowInitial, headerControl MatrixColumnHeader.initialHeader)

def preparedControl {d N₁ N₂ n : ℕ}
    (r : (Fin 4 × Fin N₂) ⊕ Fin n) (c : ExactConstruction.Columns d N₁) : Control :=
  (none, none, MatrixRowDecode.rowControl r,
    headerControl (MatrixMaterializationMachine.header (decide (ExactConstruction.aligned c)) c.1))

def sourceFlag (s : Control) : Bool := s.2.2.1.1.1
def templateSelector (s : Control) : Fin 4 := s.2.2.1.2.2.1
def entryHeader (s : Control) : Header := s.2.2.2.2.1

def inputData (row column N₂ d N₁ : ℕ) (spare : List Bool := []) : Data where
  row := List.replicate row true
  column := List.replicate column true
  rowCut := List.replicate (4 * N₂) true
  n₂ := List.replicate N₂ true
  base := List.replicate (d * N₁) true
  n₁ := List.replicate N₁ true
  spare := spare

def preparedData {d N₁ N₂ n : ℕ} (v : Data)
    (r : (Fin 4 × Fin N₂) ⊕ Fin n) (c : ExactConstruction.Columns d N₁) : Data :=
  { v with
    rowWork := List.replicate (MatrixRowDecode.sourceIndex r) true
    templateIndex := List.replicate (MatrixRowDecode.templateIndex r) true
    columnWork := []
    family := fun p => List.replicate (c.2 p).2.val true
    coordinate := fun p => List.replicate (c.2 p).1.val true }

/-- All control supplied to the entry branch is computed from physical
copies of the two original counters. The copies are consumed or turned into
the actual source/template index and selector registers. -/
theorem prepare_run {d N₁ N₂ n : ℕ} (r : (Fin 4 × Fin N₂) ⊕ Fin n)
    (code : Fin (8 * (d * N₁) ^ 4)) (spare : List Bool) :
    let c := (MatrixMaterialization.columnCode d N₁).symm code
    let x := (MatrixMaterialization.rowCode N₂ n r).val
    let v := inputData x code.val N₂ d N₁ spare
    ∃ t ≤ 14 * x + 66 * code.val + 16 * N₂ + 12 * (d * N₁) + 12 * N₁ + 12 * d + 72,
      run t (⟨some (.inl .scan), initialControl, v.contents⟩ : Config) =
        (⟨none, preparedControl r c, (preparedData v r c).contents⟩ : Config) := by
  dsimp only
  let c := (MatrixMaterialization.columnCode d N₁).symm code
  let x := (MatrixMaterialization.rowCode N₂ n r).val
  let v := inputData x code.val N₂ d N₁ spare
  let v₁ := { v with rowWork := v.row }
  let v₂ := { v₁ with columnWork := v.column }
  let v₃ := { v₂ with
    rowWork := List.replicate (MatrixRowDecode.sourceIndex r) true
    templateIndex := List.replicate (MatrixRowDecode.templateIndex r) true }
  have hcr := BitMachineCopy.run_correct none v.row []
  simp only [BitMachineCopy.run, List.append_nil] at hcr
  have hhcr : (((advance BitMachineCopy.program)^[2 * v.row.length + 2])
      (BitMachineCopy.cfg (some .scan) none v.row [] [])).l = none := by rw [hcr]; rfl
  obtain ⟨tr, htr, hr⟩ := lift_outputs_renamed copyRowBank (Equiv.refl _) (Equiv.refl _)
    BitMachineCopy.program program (some (.inl BitMachineCopy.Label.scan)) (fun _ => rfl)
    (none, rowInitial, headerControl MatrixColumnHeader.initialHeader) v.copyRowForeign
    (BitMachineCopy.cfg (some .scan) none v.row [] []) _ hhcr
  rw [hcr, copyRow_cfg, copyRow_cfg] at hr
  change run tr (cfg (some (.inl .scan)) rowInitial MatrixColumnHeader.initialHeader v) =
    cfg (some (.inr (.inl .scan))) rowInitial MatrixColumnHeader.initialHeader v₁ at hr
  have hcc := BitMachineCopy.run_correct none v.column []
  simp only [BitMachineCopy.run, List.append_nil] at hcc
  have hhcc : (((advance BitMachineCopy.program)^[2 * v.column.length + 2])
      (BitMachineCopy.cfg (some .scan) none v.column [] [])).l = none := by rw [hcc]; rfl
  obtain ⟨tc, htc, hc⟩ := lift_outputs_renamed copyColBank copyLabels copyControls
    BitMachineCopy.program program (some (.inr (.inl (.inl .scan)))) (fun _ => rfl)
    (none, rowInitial, headerControl MatrixColumnHeader.initialHeader) v₁.copyColForeign
    (BitMachineCopy.cfg (some .scan) none v.column [] []) _ hhcc
  rw [hcc, copyCol_cfg, copyCol_cfg] at hc
  change run tc (cfg (some (.inr (.inl .scan))) rowInitial MatrixColumnHeader.initialHeader v₁) =
    cfg (some (.inr (.inr (.inl (.inl .scan))))) rowInitial MatrixColumnHeader.initialHeader v₂ at hc
  obtain ⟨kr, hkr, hrr⟩ := MatrixRowDecode.row_run r
  change MatrixRowDecode.run kr
    (MatrixRowDecode.cfg (some (.inl .scan)) rowInitial v.row v.rowCut v.n₂ [] []) =
    MatrixRowDecode.cfg none (MatrixRowDecode.rowControl r)
      (List.replicate (MatrixRowDecode.sourceIndex r) true) v.rowCut v.n₂
      (List.replicate (MatrixRowDecode.templateIndex r) true) [] at hrr
  have hhrr : (((advance MatrixRowDecode.program)^[kr])
      (MatrixRowDecode.cfg (some (.inl .scan)) rowInitial v.row v.rowCut v.n₂ [] [])).l = none := by
    change (MatrixRowDecode.run kr _).l = none
    rw [hrr]
    rfl
  obtain ⟨ur, hur, hrow⟩ := lift_outputs_renamed rowBank rowLabels rowControls
    MatrixRowDecode.program program (some rowNext) (fun _ => rfl)
    (none, none, headerControl MatrixColumnHeader.initialHeader) v₂.rowForeign
    (MatrixRowDecode.cfg (some (.inl .scan)) rowInitial v.row v.rowCut v.n₂ [] []) kr hhrr
  change (((advance MatrixRowDecode.program)^[kr]) _) = _ at hrr
  rw [hrr, row_cfg, row_cfg] at hrow
  change run ur (cfg (some (.inr (.inr (.inl (.inl .scan)))))
      rowInitial MatrixColumnHeader.initialHeader v₂) =
    cfg (some (.inr (.inr (.inr columnStart))))
      (MatrixRowDecode.rowControl r) MatrixColumnHeader.initialHeader v₃ at hrow
  obtain ⟨kh, hkh, hhr⟩ := MatrixColumnHeader.header_run code
  change MatrixColumnHeader.run kh
    (MatrixColumnHeader.cfg (some columnStart) MatrixColumnHeader.initialHeader
      v.column v.base [] [] [] [] [] v.n₁ [] [] [] [] []) =
    MatrixColumnHeader.cfg none
      (MatrixMaterializationMachine.header (decide (ExactConstruction.aligned c)) c.1)
      [] v.base (List.replicate (c.2 2).2.val true) (List.replicate (c.2 3).2.val true)
      (List.replicate (c.2 1).2.val true) (List.replicate (c.2 0).2.val true) [] v.n₁
      (List.replicate (c.2 3).1.val true) (List.replicate (c.2 2).1.val true)
      (List.replicate (c.2 1).1.val true) (List.replicate (c.2 0).1.val true) [] at hhr
  have hhhh : (((advance MatrixColumnHeader.program)^[kh])
      (MatrixColumnHeader.cfg (some columnStart) MatrixColumnHeader.initialHeader
        v.column v.base [] [] [] [] [] v.n₁ [] [] [] [] [])).l = none := by
    change (MatrixColumnHeader.run kh _).l = none
    rw [hhr]
    rfl
  obtain ⟨uh, huh, hheader⟩ := lift_outputs_renamed columnBank columnLabels columnControls
    MatrixColumnHeader.program program none (fun _ => rfl)
    (none, none, MatrixRowDecode.rowControl r) v₃.columnForeign
    (MatrixColumnHeader.cfg (some columnStart) MatrixColumnHeader.initialHeader
      v.column v.base [] [] [] [] [] v.n₁ [] [] [] [] []) kh hhhh
  change (((advance MatrixColumnHeader.program)^[kh]) _) = _ at hhr
  rw [hhr,
    column_cfg (some columnStart) (MatrixRowDecode.rowControl r)
      MatrixColumnHeader.initialHeader v₃ v.column (fun _ => []) (fun _ => []),
    column_cfg none (MatrixRowDecode.rowControl r)
      (MatrixMaterializationMachine.header (decide (ExactConstruction.aligned c)) c.1)
      v₃ [] (fun p => List.replicate (c.2 p).2.val true)
      (fun p => List.replicate (c.2 p).1.val true)] at hheader
  change run uh (cfg (some (.inr (.inr (.inr columnStart))))
      (MatrixRowDecode.rowControl r) MatrixColumnHeader.initialHeader v₃) =
    cfg none (MatrixRowDecode.rowControl r)
      (MatrixMaterializationMachine.header (decide (ExactConstruction.aligned c)) c.1)
      (preparedData v r c) at hheader
  refine ⟨tr + tc + ur + uh, ?_, ?_⟩
  · simp only [v, inputData, List.length_replicate] at htr htc
    change kr ≤ 12 * x + 16 * N₂ + 16 at hkr
    omega
  · exact (run_add ((run_add ((run_add hr tc).trans hc) ur).trans hrow) uh).trans hheader

@[simp] theorem prepared_sourceFlag {d N₁ N₂ n : ℕ}
    (r : (Fin 4 × Fin N₂) ⊕ Fin n) (c : ExactConstruction.Columns d N₁) :
    sourceFlag (preparedControl r c) = r.isRight := by cases r <;> rfl

@[simp] theorem prepared_templateSelector {d N₁ N₂ n : ℕ}
    (p : Fin 4) (z : Fin N₂) (c : ExactConstruction.Columns d N₁) :
    templateSelector (preparedControl (n := n) (.inl (p, z)) c) = p := rfl

@[simp] theorem prepared_entryHeader {d N₁ N₂ n : ℕ}
    (r : (Fin 4 × Fin N₂) ⊕ Fin n) (c : ExactConstruction.Columns d N₁) :
    entryHeader (preparedControl r c) =
      MatrixMaterializationMachine.header (decide (ExactConstruction.aligned c)) c.1 := rfl

end EthInapproximability.CurrentPaper.MatrixEntryPreparation
