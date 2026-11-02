import CurrentAdditive.IndexedFieldRun
import EthInapproximability.CurrentPaper.ProtocolBinaryHeader

/-! A fixed finite-control program parses the counted V2 list header using
`ProtocolBinaryHeader`, then enters the indexed framed-item scanner. Bank 7
holds the zero-based unary index. The input is consumed. -/

namespace CurrentAdditive.GaussListContext.IndexedV2Program

open EthInapproximability.CurrentPaper
open Turing Turing.TM2.Stmt BitMachineEncoding

abbrev Stack := IndexedFieldProgram.Stack

inductive Admin where
  | afterHeader | clearHeaderCount | startIndex | done
  deriving DecidableEq, Fintype

abbrev Label := ProtocolBinaryHeader.Label ⊕
  (IndexedFieldProgram.Label ⊕ Admin)

abbrev Control := ProtocolBinaryHeader.Control ×
  IndexedFieldProgram.Control × Option Bool

abbrev Config := TM2.Cfg (fun _ : Stack => Bool) Label Control

def headerStack : Fin 3 ↪ Stack where
  toFun j := ⟨j.val, by omega⟩
  inj' := by
    intro i j h
    apply Fin.ext
    simpa using congrArg Fin.val h

def headerControl (v : ProtocolBinaryHeader.Control) : Control :=
  (v, IndexedFieldProgram.fieldControl SourceListMachineFields.initialControl, none)

def indexControl (v : IndexedFieldProgram.Control) : Control :=
  ((none, none), v, none)

def program : Label → TM2.Stmt (fun _ : Stack => Bool) Label Control
  | .inl l => BitMachineStackEmbedding.stmt
      headerStack Sum.inl headerControl (fun v => v.1)
      (some (.inr (.inr .afterHeader))) (ProtocolBinaryHeader.program l)
  | .inr (.inl l) => BitMachineStackEmbedding.stmt
      (Function.Embedding.refl Stack) (fun l => .inr (.inl l)) indexControl
      (fun v => v.2.1) (some (.inr (.inr .done)))
      (IndexedFieldProgram.program l)
  | .inr (.inr .afterHeader) =>
      pop 2 (fun v b => (v.1, v.2.1, b))
        (branch (fun v => v.2.2.getD false)
          (goto (fun _ => .inr (.inr .clearHeaderCount))) halt)
  | .inr (.inr .clearHeaderCount) =>
      pop 2 (fun v b => (v.1, v.2.1, b))
        (branch (fun v => v.2.2.isSome)
          (goto (fun _ => .inr (.inr .clearHeaderCount)))
          (goto (fun _ => .inr (.inr .startIndex))))
  | .inr (.inr .startIndex) =>
      load (fun _ => indexControl
        (IndexedFieldProgram.fieldControl SourceListMachineFields.initialControl))
        (goto (fun _ => .inr (.inl (.inl (.inl .scan)))))
  | .inr (.inr .done) => halt

def initial (input : List Bool) (index : Nat) : Config :=
  ⟨some (.inl .scan),
   headerControl (none, none),
   IndexedFieldProgram.initialBank input index⟩

def run (t : Nat) (c : Config) := ((advance program)^[t]) c

theorem program_finite : Finite Stack ∧ Finite Label ∧ Finite Control :=
  ⟨inferInstance, inferInstance, inferInstance⟩

#print axioms program_finite

end CurrentAdditive.GaussListContext.IndexedV2Program
