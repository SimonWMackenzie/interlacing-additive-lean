import EthInapproximability.CurrentPaper.SourceListMachineFields
import EthInapproximability.CurrentPaper.BitMachineStackEmbedding

/-!
A new fixed finite-control repeated field scanner. Input stack zero holds
`SourceListEncoding.fields xs`, stack seven a unary zero-based item index.
Each iteration uses the inherited strict one-field parser and physically
clears its scratch before the next item. Correctness/clock are separate.
-/

namespace CurrentAdditive.GaussListContext.IndexedFieldProgram

open EthInapproximability.CurrentPaper
open Turing Turing.TM2.Stmt BitMachineEncoding

abbrev Stack := Fin 8

inductive Admin where
  | start | afterField | clearPayload | clearCount | again
  deriving DecidableEq, Fintype

abbrev Label := SourceListMachineFields.Label ⊕ Admin
abbrev Control := SourceListMachineFields.Control × Option Bool
abbrev Config := TM2.Cfg (fun _ : Stack => Bool) Label Control

def fieldStack : SourceListMachineFields.Stack ↪ Stack where
  toFun j := ⟨j.val, by omega⟩
  inj' := by
    intro i j h
    apply Fin.ext
    simpa using congrArg Fin.val h

def fieldControl (v : SourceListMachineFields.Control) : Control := (v, none)

def program : Label → TM2.Stmt (fun _ : Stack => Bool) Label Control
  | .inl l => BitMachineStackEmbedding.stmt fieldStack Sum.inl
      fieldControl Prod.fst (some (.inr .afterField))
      (SourceListMachineFields.program l)
  | .inr .start =>
      load (fun _ => fieldControl SourceListMachineFields.initialControl)
        (goto (fun _ => .inl (.inl .scan)))
  | .inr .afterField =>
      branch (fun v => v.1.2.1 == some true)
        (pop 7 (fun v b => (v.1,b))
          (branch (fun v => v.2.isSome)
            (goto (fun _ => .inr .clearPayload)) halt))
        halt
  | .inr .clearPayload =>
      pop 6 (fun v b => (v.1,b))
        (branch (fun v => v.2.isSome)
          (goto (fun _ => .inr .clearPayload))
          (goto (fun _ => .inr .clearCount)))
  | .inr .clearCount =>
      pop 5 (fun v b => (v.1,b))
        (branch (fun v => v.2.isSome)
          (goto (fun _ => .inr .clearCount))
          (goto (fun _ => .inr .again)))
  | .inr .again =>
      load (fun _ => fieldControl SourceListMachineFields.initialControl)
        (goto (fun _ => .inl (.inl .scan)))

def initialBank (input : List Bool) (index : Nat) : Stack → List Bool :=
  fun j => if j = 0 then input else
    if j = 7 then List.replicate index true else []

def initial (input : List Bool) (index : Nat) : Config :=
  ⟨some (.inr .start), fieldControl SourceListMachineFields.initialControl,
    initialBank input index⟩

def run (t : Nat) (c : Config) := ((advance program)^[t]) c

theorem program_finite : Finite Stack ∧ Finite Label ∧ Finite Control :=
  ⟨inferInstance, inferInstance, inferInstance⟩

#print axioms program_finite

end CurrentAdditive.GaussListContext.IndexedFieldProgram
