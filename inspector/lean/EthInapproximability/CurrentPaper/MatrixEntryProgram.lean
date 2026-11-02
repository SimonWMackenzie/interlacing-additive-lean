import EthInapproximability.CurrentPaper.MatrixEntryPreparation
import EthInapproximability.CurrentPaper.MatrixTemplateEntry
import EthInapproximability.CurrentPaper.MatrixSourceEntry
import EthInapproximability.CurrentPaper.BitMachineClearBank
import EthInapproximability.CurrentPaper.BitMachineStackEmbedding

/-!
# A single finite program for an exact matrix entry

This file defines the physical dispatch between the already compiled label
decoder, template query, and source query. All indices are read from stacks.
The only branch data in instruction labels or control are finite selectors
and the finite source-row header. The complete correctness and time theorem
is proved separately; defining this program alone is not a runtime claim.
-/

namespace EthInapproximability.CurrentPaper.MatrixEntryProgram

open Turing Turing.TM2.Stmt BitMachineEncoding

abbrev Header := MatrixMaterializationMachine.Control
abbrev Stack := Fin 54

def preparationInitial : MatrixEntryPreparation.Control :=
  (none, none, MatrixEntryPreparation.rowInitial,
    MatrixEntryPreparation.headerControl MatrixColumnHeader.initialHeader)

def sourceInitial (h : Header) : MatrixSourceEntry.Control :=
  (((MatrixStrideGather.baseControl, false), h), none)

inductive State where
  | prepare (v : MatrixEntryPreparation.Control)
  | template (v : MatrixTemplateEntry.Control)
  | source (v : MatrixSourceEntry.Control)
  | copy (v : Option Bool)
  deriving Fintype

abbrev Control := State × Option Bool

def initial : Control := (.prepare preparationInitial, none)

def getPreparation : Control → MatrixEntryPreparation.Control
  | (.prepare v, _) => v
  | _ => preparationInitial

def getTemplate : Control → MatrixTemplateEntry.Control
  | (.template v, _) => v
  | _ => MatrixTemplateEntry.base

def getSource : Control → MatrixSourceEntry.Control
  | (.source v, _) => v
  | _ => sourceInitial {}

def getCopy : Control → Option Bool
  | (.copy v, _) => v
  | _ => none

def sourceFlag (v : MatrixEntryPreparation.Control) : Bool := v.2.2.1.1.1
def templateSelector (v : MatrixEntryPreparation.Control) : Fin 4 := v.2.2.1.2.2.1
def entryHeader (v : MatrixEntryPreparation.Control) : Header := v.2.2.2.2.1

inductive Label where
  | prepare (l : MatrixEntryPreparation.Label)
  | dispatch
  | templateInit (p : Fin 4)
  | template (p : Fin 4) (l : MatrixTemplateEntry.Label)
  | sourceCopyInit (h : Header)
  | sourceCopy (h : Header) (l : BitMachineCopy.Label)
  | sourceInit (h : Header)
  | source (l : MatrixSourceEntry.Label)
  | clear (i : Fin 40)
  | done
  deriving Fintype

abbrev Config := TM2.Cfg (fun _ : Stack => Bool) Label Control

def preparationSlots : Fin 26 ↪ Stack where
  toFun i := ⟨i.val, by omega⟩
  inj' := by intro i j h; apply Fin.ext; exact congrArg (fun k : Stack => k.val) h

def templateSlots (p : Fin 4) : Fin 23 ↪ Stack where
  toFun := ![(![17, 16, 14, 15] : Fin 4 → Stack) p,
    29, 9, 27, (![22, 21, 20, 19] : Fin 4 → Stack) p,
    26, 33, 7, 8, 35, 36, 37, 28, 38, 39, 30, 31, 40, 41, 34, 42, 43, 44]
  inj' := by fin_cases p <;> decide

def sourceCopySlots : Fin 3 ↪ Stack where
  toFun := ![22, 45, 24]
  inj' := by decide

def sourceSlots : MatrixSourceEntry.Stack ↪ Stack where
  toFun := Sum.elim (![45, 46, 47, 32, 48, 49, 50, 51, 27, 52, 34]) (![6, 53])
  inj' := by decide

/-- Precisely the work registers, excluding the input indices, parameters,
three payload arrays, zero register, and answer stack. -/
def workSlot (i : Fin 39) : Stack :=
  if h : i.val < 20 then ⟨i.val + 6, by omega⟩ else ⟨i.val - 20 + 35, by omega⟩

theorem workSlot_injective : Function.Injective workSlot := by
  intro i j h
  apply Fin.ext
  have hv := congrArg Fin.val h
  dsimp [workSlot] at hv
  split_ifs at hv <;> dsimp only at hv <;> omega

def program : Label → TM2.Stmt (fun _ : Stack => Bool) Label Control
  | .prepare l => BitMachineStackEmbedding.stmt preparationSlots Label.prepare
      (fun v => (.prepare v, none)) getPreparation (some .dispatch)
      (MatrixEntryPreparation.program l)
  | .dispatch => branch (fun s => sourceFlag (getPreparation s))
      (goto (fun s => .sourceCopyInit (entryHeader (getPreparation s))))
      (goto (fun s => .templateInit (templateSelector (getPreparation s))))
  | .templateInit p => load (fun _ => (.template MatrixTemplateEntry.base, none))
      (goto (fun _ => .template p (.inl (0, .outer))))
  | .template p l => BitMachineStackEmbedding.stmt (templateSlots p) (Label.template p)
      (fun v => (.template v, none)) getTemplate (some (.clear 0))
      (MatrixTemplateEntry.program l)
  | .sourceCopyInit h => load (fun _ => (.copy none, none))
      (goto (fun _ => .sourceCopy h .scan))
  | .sourceCopy h l => BitMachineStackEmbedding.stmt sourceCopySlots (Label.sourceCopy h)
      (fun v => (.copy v, none)) getCopy (some (.sourceInit h)) (BitMachineCopy.program l)
  | .sourceInit h => load (fun _ => (.source (sourceInitial h), none))
      (goto (fun _ => .source (.inr false)))
  | .source l => BitMachineStackEmbedding.stmt sourceSlots Label.source
      (fun v => (.source v, none)) getSource (some (.clear 0)) (MatrixSourceEntry.program l)
  | .clear i => if h : i.val < 39 then
      BitMachineClearBank.clearStep (workSlot ⟨i.val, h⟩) (.clear i)
        (.clear ⟨i.val + 1, by omega⟩)
      else BitMachineClearBank.finishStep (fun _ => initial.1) .done
  | .done => halt

def start : Label := .prepare (.inl .scan)
def cfg (l : Option Label) (s : Control) (bank : Stack → List Bool) : Config := ⟨l, s, bank⟩
def run (n : ℕ) (c : Config) := ((advance program)^[n]) c

theorem run_add {c d : Config} {m : ℕ} (h : run m c = d) (n : ℕ) :
    run (m + n) c = run n d := by
  rw [Nat.add_comm m n]
  simp only [run, Function.iterate_add_apply] at h ⊢
  rw [h]

theorem clear_run (v : State) (bank : Stack → List Bool) :
    run ((∑ i, (bank (workSlot i)).length) + 41)
      (cfg (some (.clear 0)) (v, none) bank) =
      cfg none initial (BitMachineClearBank.cleared workSlot bank) := by
  have hs (i : Fin 39) : program (.clear i.castSucc) =
      BitMachineClearBank.clearStep (workSlot i) (.clear i.castSucc) (.clear i.succ) := by
    simp only [program, Fin.val_castSucc, dif_pos i.isLt]
    rfl
  have hf : program (.clear (Fin.last 39)) =
      BitMachineClearBank.finishStep (fun _ => initial.1) .done := by
    simp only [program, Fin.val_last, lt_self_iff_false, ↓reduceDIte]
  have hr := BitMachineClearBank.clear_bank_run program (fun _ => initial.1) .done
    39 workSlot workSlot_injective Label.clear hs hf v bank
  have hd : run 1 (cfg (some .done) initial (BitMachineClearBank.cleared workSlot bank)) =
      cfg none initial (BitMachineClearBank.cleared workSlot bank) := rfl
  simpa only [Nat.add_assoc] using (run_add hr 1).trans hd

end EthInapproximability.CurrentPaper.MatrixEntryProgram
