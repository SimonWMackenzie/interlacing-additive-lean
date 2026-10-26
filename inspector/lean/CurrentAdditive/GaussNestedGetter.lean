import CurrentAdditive.CylinderContextScanRun
import CurrentAdditive.PreservingV2Run

/-!
Two physical source-preserving counted-V2 selectors, arranged for a nested
matrix packet. The first selects a row using unary bank 10; the second selects
a cell from that row using unary bank 11. The outer matrix remains on bank 8.
The second selector writes the cell to bank 18; a final physical transfer to
bank 6 is a separate stage.
-/

namespace CurrentAdditive.GaussNestedGetter

open EthInapproximability.CurrentPaper
open CurrentAdditive.GaussListContext
open CurrentAdditive.CylinderContextScanStep
open Turing Turing.TM2.Stmt BitMachineEncoding

abbrev Stack := Fin 22

inductive Admin where
  | afterFirst | afterSecond | done
  deriving DecidableEq, Fintype

abbrev Label := CylinderContextScanStep.Label ⊕
  (PreservingV2Program.Label ⊕ Admin)
abbrev Control := CylinderContextScanStep.Control ×
  PreservingV2Program.Control
abbrev Config := TM2.Cfg (fun _ : Stack => Bool) Label Control

def firstMap : CylinderContextScanStep.Stack ↪ Stack where
  toFun j := ![0, 1, 2, 3, 4, 5, 6, 7, 8, 14, 10, 20] j
  inj' := by intro a b h; fin_cases a <;> fin_cases b <;> simp_all

def secondMap : PreservingV2Program.Stack ↪ Stack where
  toFun j := ![12, 13, 14, 15, 16, 17, 18, 11, 6, 20] j
  inj' := by intro a b h; fin_cases a <;> fin_cases b <;> simp_all

def firstControl (v : CylinderContextScanStep.Control) : Control :=
  (v, PreservingV2Program.copyControl ((), none))
def secondControl (v : PreservingV2Program.Control) : Control :=
  (CylinderContextScanStep.copyControl ((), none), v)

def program : Label → TM2.Stmt (fun _ : Stack => Bool) Label Control
  | .inl l => BitMachineStackEmbedding.stmt firstMap Sum.inl
      firstControl Prod.fst (some (.inr (.inr .afterFirst)))
      (CylinderContextScanStep.program l)
  | .inr (.inl l) => BitMachineStackEmbedding.stmt secondMap
      (fun l => .inr (.inl l)) secondControl Prod.snd
      (some (.inr (.inr .afterSecond)))
      (PreservingV2Program.program l)
  | .inr (.inr .afterFirst) =>
      load (fun _ => secondControl
        (PreservingV2Program.copyControl ((), none)))
        (goto (fun _ => .inr (.inl (.inl .scan))))
  | .inr (.inr .afterSecond) => goto (fun _ => .inr (.inr .done))
  | .inr (.inr .done) => halt

def run (t : Nat) (c : Config) : Config := ((advance program)^[t]) c

def inputForeign (column : Nat) : Stack → List Bool :=
  fun j => if j = 11 then List.replicate column true else []

noncomputable def firstFrame (foreign : Stack → List Bool)
    (c : CylinderContextScanStep.Config) : Config :=
  BitMachineStackEmbedding.cfg firstMap foreign Sum.inl firstControl
    (some (.inr (.inr .afterFirst))) c

noncomputable def secondFrame (foreign : Stack → List Bool)
    (c : PreservingV2Program.Config) : Config :=
  BitMachineStackEmbedding.cfg secondMap foreign
    (fun l => .inr (.inl l)) secondControl
    (some (.inr (.inr .afterSecond))) c

theorem program_finite :
    Finite Stack ∧ Finite Label ∧ Finite Control :=
  ⟨inferInstance, inferInstance, inferInstance⟩

theorem first_lookup (pre : List (List Bool)) (row : List Bool)
    (suffix : List (List Bool)) (foreign : Stack → List Bool) :
    let matrix := SourceListEncoding.encode (pre ++ row :: suffix)
    ∃ t ≤ 2 * pre.length + 5 +
        (2 * matrix.length + 5 +
          (4 * (pre ++ row :: suffix).length.bits.length + 6 +
            IndexedFieldProgram.fieldCost (pre ++ [row]))),
      run t (firstFrame foreign
        (CylinderContextScanStep.initial matrix pre.length)) =
        firstFrame foreign
          ⟨none,
           CylinderContextScanStep.getterControl
             (PreservingV2Program.v2Control
               (IndexedV2Program.indexControl
                 (SourceListMachineFields.coreControl (some true, false), none))),
           CylinderContextScanStep.selectedBank matrix
             (SourceListEncoding.fields suffix) row pre.length⟩ := by
  dsimp only
  obtain ⟨t, ht, hr⟩ := CylinderContextScanStep.scan_step pre row suffix
  obtain ⟨u, hu, he⟩ := BitMachineStackEmbedding.outputs
    firstMap foreign Sum.inl firstControl Prod.fst
    (by intro v; rfl) (some (.inr (.inr .afterFirst)))
    CylinderContextScanStep.program program (by intro l; rfl)
    (CylinderContextScanStep.initial
      (SourceListEncoding.encode (pre ++ row :: suffix)) pre.length)
    t (by change (CylinderContextScanStep.run t _).l = none; rw [hr])
  change run u (firstFrame foreign _) =
    firstFrame foreign (CylinderContextScanStep.run t _) at he
  rw [hr] at he
  exact ⟨u, hu.trans ht, he⟩

theorem second_lookup (pre : List (List Bool)) (cell : List Bool)
    (suffix : List (List Bool)) (foreign : Stack → List Bool) :
    let row := SourceListEncoding.encode (pre ++ cell :: suffix)
    ∃ t ≤ 2 * row.length + 5 +
        (4 * (pre ++ cell :: suffix).length.bits.length + 6 +
          IndexedFieldProgram.fieldCost (pre ++ [cell])),
      run t (secondFrame foreign
        (PreservingV2Program.initial row pre.length)) =
        secondFrame foreign
          ⟨none,
           PreservingV2Program.v2Control
             (IndexedV2Program.indexControl
               (SourceListMachineFields.coreControl (some true, false), none)),
           ![SourceListEncoding.fields suffix, [], [], [], [],
             List.replicate cell.length true, cell, [], row, []]⟩ := by
  dsimp only
  obtain ⟨t, ht, hr⟩ := PreservingV2Program.select_preserving
    pre cell suffix
  obtain ⟨u, hu, he⟩ := BitMachineStackEmbedding.outputs
    secondMap foreign (fun l => .inr (.inl l)) secondControl Prod.snd
    (by intro v; rfl) (some (.inr (.inr .afterSecond)))
    PreservingV2Program.program program (by intro l; rfl)
    (PreservingV2Program.initial
      (SourceListEncoding.encode (pre ++ cell :: suffix)) pre.length)
    t (by change (PreservingV2Program.run t _).l = none; rw [hr])
  change run u (secondFrame foreign _) =
    secondFrame foreign (PreservingV2Program.run t _) at he
  rw [hr] at he
  exact ⟨u, hu.trans ht, he⟩

theorem first_preserves_column (foreign : Stack → List Bool)
    (c : CylinderContextScanStep.Config) :
    (firstFrame foreign c).stk 11 = foreign 11 := by
  apply BitMachineStackEmbedding.bank_outside
  rintro ⟨j, hj⟩
  fin_cases j <;> cases hj

theorem first_selected_row (foreign : Stack → List Bool)
    (c : CylinderContextScanStep.Config) :
    (firstFrame foreign c).stk 6 = c.stk 6 := by
  exact BitMachineStackEmbedding.bank_at firstMap foreign c.stk 6

theorem second_preserves_matrix (foreign : Stack → List Bool)
    (c : PreservingV2Program.Config) :
    (secondFrame foreign c).stk 8 = foreign 8 := by
  apply BitMachineStackEmbedding.bank_outside
  rintro ⟨j, hj⟩
  fin_cases j <;> cases hj

theorem second_selected_cell (foreign : Stack → List Bool)
    (c : PreservingV2Program.Config) :
    (secondFrame foreign c).stk 18 = c.stk 6 := by
  exact BitMachineStackEmbedding.bank_at secondMap foreign c.stk 6

def firstDone (matrix suffix row : List Bool) (index : Nat) :
    CylinderContextScanStep.Config :=
  ⟨none,
   CylinderContextScanStep.getterControl
     (PreservingV2Program.v2Control
       (IndexedV2Program.indexControl
         (SourceListMachineFields.coreControl (some true, false), none))),
   CylinderContextScanStep.selectedBank matrix suffix row index⟩

theorem after_first_step (matrix suffix row : List Bool)
    (rowIndex columnIndex : Nat) :
    advance program
      (firstFrame (inputForeign columnIndex)
        (firstDone matrix suffix row rowIndex)) =
      secondFrame
        (firstFrame (inputForeign columnIndex)
          (firstDone matrix suffix row rowIndex)).stk
        (PreservingV2Program.initial row columnIndex) := by
  unfold program secondFrame firstFrame firstDone
    BitMachineStackEmbedding.cfg BitMachineStackEmbedding.stackCfg
    BitMachineInline.cfg
  simp only [advance, TM2.step, TM2.stepAux]
  simp only [Option.getD_some, PreservingV2Program.initial]
  congr 1
  symm
  apply BitMachineStackEmbedding.bank_eq_self
  intro k
  fin_cases k <;>
    simp only [secondMap, PreservingV2Program.initialBank,
      CylinderContextScanStep.selectedBank]
  all_goals first
    | (rw [BitMachineStackEmbedding.bank_outside]
       · simp [inputForeign]
       · rintro ⟨j, hj⟩; fin_cases j <;> cases hj)
    | (simpa [firstMap] using
        (BitMachineStackEmbedding.bank_at firstMap
          (inputForeign columnIndex)
          (CylinderContextScanStep.selectedBank matrix suffix row rowIndex)
          (6 : CylinderContextScanStep.Stack)).symm)
    | (simpa [firstMap] using
        (BitMachineStackEmbedding.bank_at firstMap
          (inputForeign columnIndex)
          (CylinderContextScanStep.selectedBank matrix suffix row rowIndex)
          (9 : CylinderContextScanStep.Stack)))
    | (simpa [firstMap] using
        (BitMachineStackEmbedding.bank_at firstMap
          (inputForeign columnIndex)
          (CylinderContextScanStep.selectedBank matrix suffix row rowIndex)
          (11 : CylinderContextScanStep.Stack)))

#print axioms after_first_step

#print axioms first_lookup
#print axioms second_lookup
#print axioms first_preserves_column
#print axioms second_preserves_matrix

end CurrentAdditive.GaussNestedGetter
