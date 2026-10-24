import EthInapproximability.CurrentPaper.SourceListMachineItemPrefix
import EthInapproximability.CurrentPaper.SourceListMachineInitialize
import EthInapproximability.CurrentPaper.SourceListMachineCounter

/-!
# Literal outer loop for a framed source list

The unread input is the item controller's source stack. The binary branch
count and reversed output accumulator live on permanent stacks. One positive
counter step runs one item. Only after the zero count and empty unread input
does the machine reverse the accumulator into its designated output stack.
This file defines the program; correctness and the sum of per-item costs are
separate obligations.
-/

namespace EthInapproximability.CurrentPaper.SourceListMachineOuter

open Turing TM2.Stmt BitMachine BitMachineEncoding

variable (M : Machine)

inductive Admin where
  | startInit | afterInit | afterCounter | afterItem | checkTail | finalize | done
  deriving DecidableEq, Fintype

abbrev Stack := SourceListMachineItem.Stack M ⊕ Fin 3
abbrev Label := SourceListMachineItem.Label M ⊕
  (SourceListMachineInitialize.Label ⊕ (SourceListMachineCounter.Label ⊕ Admin))
abbrev Control := ((SourceListMachineItem.Control M × SourceListMachineInitialize.Control) ×
  SourceListMachineCounter.Control) × Option Bool
abbrev Config := TM2.Cfg (fun _ : Stack M => Bool) (Label M) (Control M)

def itemLabel (l : SourceListMachineItem.Label M) : Label M := .inl l
def initLabel (l : SourceListMachineInitialize.Label) : Label M := .inr (.inl l)
def counterLabel (l : SourceListMachineCounter.Label) : Label M := .inr (.inr (.inl l))
def adminLabel (l : Admin) : Label M := .inr (.inr (.inr l))

def itemStack : SourceListMachineItem.Stack M ↪ Stack M :=
  ⟨Sum.inl, Sum.inl_injective⟩

def initStack : SourceListMachineInitialize.Stack ↪ Stack M where
  toFun
    | 0 => .inl (.inr 0)
    | 1 => .inl (.inr 1)
    | 2 => .inr 0
    | 3 => .inr 1
    | 4 => .inl (.inr 7)
  inj' := by
    intro a b h
    fin_cases a <;> fin_cases b <;> simp_all

def counterStack : SourceListMachineCounter.Stack ↪ Stack M where
  toFun
    | 0 => .inr 0
    | 1 => .inr 1
  inj' := by
    intro a b h
    fin_cases a <;> fin_cases b <;> simp_all

def itemControl (v : SourceListMachineItem.Control M) : Control M :=
  (((v,SourceListMachineInitialize.initialControl),
    SourceListMachineCounter.initialControl),none)
def initControl (v : SourceListMachineInitialize.Control) : Control M :=
  (((SourceListMachineItem.fieldControl M SourceListMachineFields.initialControl,v),
    SourceListMachineCounter.initialControl),none)
def counterControl (v : SourceListMachineCounter.Control) : Control M :=
  (((SourceListMachineItem.fieldControl M SourceListMachineFields.initialControl,
    SourceListMachineInitialize.initialControl),v),none)

def initialControl : Control M := initControl M SourceListMachineInitialize.initialControl
def rejected (v : Control M) : Control M := (v.1,some false)
def accepted (v : Control M) : Control M := (v.1,some true)

def program : Label M → TM2.Stmt (fun _ : Stack M => Bool) (Label M) (Control M)
  | .inl l => BitMachineStackEmbedding.stmt (itemStack M) (itemLabel M)
      (itemControl M) (fun v => v.1.1.1) (some (adminLabel M .afterItem))
      (SourceListMachineItem.program M l)
  | .inr (.inl l) => BitMachineStackEmbedding.stmt (initStack M) (initLabel M)
      (initControl M) (fun v => v.1.1.2) (some (adminLabel M .afterInit))
      (SourceListMachineInitialize.program l)
  | .inr (.inr (.inl l)) => BitMachineStackEmbedding.stmt (counterStack M)
      (counterLabel M) (counterControl M) (fun v => v.1.2)
      (some (adminLabel M .afterCounter)) (SourceListMachineCounter.program l)
  | .inr (.inr (.inr .startInit)) =>
      load (fun _ => initControl M SourceListMachineInitialize.initialControl)
        (goto (fun _ => initLabel M (.inl .scan)))
  | .inr (.inr (.inr .afterInit)) =>
      branch (fun v => v.1.1.2.2 == some true)
        (load (fun _ => counterControl M SourceListMachineCounter.initialControl)
          (goto (fun _ => counterLabel M (.inr .scan))))
        (load (rejected M) halt)
  | .inr (.inr (.inr .afterCounter)) =>
      branch (fun v => v.1.2.2.1 == some true)
        (load (fun _ => itemControl M
          (SourceListMachineItem.fieldControl M SourceListMachineFields.initialControl))
          (goto (fun _ => itemLabel M (SourceListMachineItem.fieldLabel M (.inl .scan)))))
        (goto (fun _ => adminLabel M .checkTail))
  | .inr (.inr (.inr .afterItem)) =>
      branch (fun v => v.1.1.1.2 == some true)
        (load (fun _ => counterControl M SourceListMachineCounter.initialControl)
          (goto (fun _ => counterLabel M (.inr .scan))))
        (load (rejected M) halt)
  | .inr (.inr (.inr .checkTail)) =>
      pop (.inl (.inr 0)) (fun v b => (v.1,b))
        (branch (fun v => v.2.isSome)
          (load (rejected M) halt)
          (goto (fun _ => adminLabel M .finalize)))
  | .inr (.inr (.inr .finalize)) =>
      BitMachineBroadcast.scanStep (.inl (.inr 7)) (.inr 2)
        (adminLabel M .finalize) (adminLabel M .done)
  | .inr (.inr (.inr .done)) => load (accepted M) halt

/-- The designated input/output stacks of the finite controller. -/
noncomputable def machine : Machine :=
  ofFinite (.inl (.inr 0) : Stack M) (.inr (2 : Fin 3))
    (adminLabel M .startInit) (initialControl M) (program M)

end EthInapproximability.CurrentPaper.SourceListMachineOuter
