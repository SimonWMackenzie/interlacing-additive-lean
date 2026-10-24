import CurrentAdditive.PreservingV2Run

/-! One literal step of the repeated indexed scan. A unary index is kept on
bank 10 while a physical copy enters the preserving V2 getter on bank 7.
The encoded list remains on bank 8; the selected item appears on bank 6.
The program has a fixed finite stack set and no data-dependent instruction. -/

namespace CurrentAdditive.CylinderContextScanStep

open EthInapproximability.CurrentPaper
open CurrentAdditive.GaussListContext
open Turing Turing.TM2.Stmt BitMachineEncoding

abbrev Stack := Fin 12

inductive Admin where
  | afterCopy | done
  deriving DecidableEq, Fintype

abbrev Label := SourceClausePreservingBroadcast.Label ⊕
  (PreservingV2Program.Label ⊕ Admin)

abbrev Control := (Unit × Option Bool) × PreservingV2Program.Control
abbrev Config := TM2.Cfg (fun _ : Stack => Bool) Label Control

def getterStack : PreservingV2Program.Stack ↪ Stack where
  toFun j := ⟨j.val, by omega⟩
  inj' := by
    intro i j h
    apply Fin.ext
    simpa using congrArg Fin.val h

def copyControl (v : Unit × Option Bool) : Control :=
  (v, PreservingV2Program.copyControl ((), none))

def getterControl (v : PreservingV2Program.Control) : Control :=
  (((), none), v)

def program : Label → TM2.Stmt (fun _ : Stack => Bool) Label Control
  | .inl l => BitMachineStackEmbedding.stmt
      (Function.Embedding.refl Stack) Sum.inl copyControl Prod.fst
      (some (.inr (.inr .afterCopy)))
      (SourceClausePreservingBroadcast.program 10 11 [7] l)
  | .inr (.inl l) => BitMachineStackEmbedding.stmt
      getterStack (fun l => .inr (.inl l)) getterControl Prod.snd
      (some (.inr (.inr .done))) (PreservingV2Program.program l)
  | .inr (.inr .afterCopy) =>
      load (fun _ => getterControl (PreservingV2Program.copyControl ((), none)))
        (goto (fun _ => .inr (.inl (.inl .scan))))
  | .inr (.inr .done) => halt

def initialBank (source : List Bool) (index : Nat) : Stack → List Bool :=
  ![[], [], [], [], [], [], [], [], source, [],
    List.replicate index true, []]

def initial (source : List Bool) (index : Nat) : Config :=
  ⟨some (.inl .scan), copyControl ((), none), initialBank source index⟩

def run (t : Nat) (c : Config) := ((advance program)^[t]) c

theorem program_finite : Finite Stack ∧ Finite Label ∧ Finite Control :=
  ⟨inferInstance, inferInstance, inferInstance⟩

#print axioms program_finite

end CurrentAdditive.CylinderContextScanStep
