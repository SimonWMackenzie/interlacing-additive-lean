import CurrentAdditive.IndexedV2HeaderRun
import EthInapproximability.CurrentPaper.SourceClausePreservingBroadcast

/-! A fixed physical wrapper retains the counted list on bank 8 while
selecting an item from a copy on banks 0–7. Bank 9 is copy scratch. -/

namespace CurrentAdditive.GaussListContext.PreservingV2Program

open EthInapproximability.CurrentPaper
open Turing Turing.TM2.Stmt BitMachineEncoding

abbrev Stack := Fin 10

inductive Admin where
  | afterCopy | done
  deriving DecidableEq, Fintype

abbrev Label := SourceClausePreservingBroadcast.Label ⊕
  (IndexedV2Program.Label ⊕ Admin)

abbrev Control := (Unit × Option Bool) × IndexedV2Program.Control
abbrev Config := TM2.Cfg (fun _ : Stack => Bool) Label Control

def v2Stack : IndexedV2Program.Stack ↪ Stack where
  toFun j := ⟨j.val, by omega⟩
  inj' := by
    intro i j h
    apply Fin.ext
    simpa using congrArg Fin.val h

def copyControl (v : Unit × Option Bool) : Control :=
  (v, IndexedV2Program.headerControl (none, none))

def v2Control (v : IndexedV2Program.Control) : Control :=
  (((), none), v)

def program : Label → TM2.Stmt (fun _ : Stack => Bool) Label Control
  | .inl l => BitMachineStackEmbedding.stmt
      (Function.Embedding.refl Stack) Sum.inl copyControl Prod.fst
      (some (.inr (.inr .afterCopy)))
      (SourceClausePreservingBroadcast.program 8 9 [0] l)
  | .inr (.inl l) => BitMachineStackEmbedding.stmt
      v2Stack (fun l => .inr (.inl l)) v2Control Prod.snd
      (some (.inr (.inr .done))) (IndexedV2Program.program l)
  | .inr (.inr .afterCopy) =>
      load (fun _ => v2Control (IndexedV2Program.headerControl (none, none)))
        (goto (fun _ => .inr (.inl (.inl .scan))))
  | .inr (.inr .done) => halt

def initialBank (source : List Bool) (index : Nat) : Stack → List Bool :=
  ![[], [], [], [], [], [], [], List.replicate index true,
    source, []]

def initial (source : List Bool) (index : Nat) : Config :=
  ⟨some (.inl .scan), copyControl ((), none), initialBank source index⟩

def run (t : Nat) (c : Config) := ((advance program)^[t]) c

theorem program_finite : Finite Stack ∧ Finite Label ∧ Finite Control :=
  ⟨inferInstance, inferInstance, inferInstance⟩

#print axioms program_finite

end CurrentAdditive.GaussListContext.PreservingV2Program
