import Paper2.GeneratorSerialization
import EthInapproximability.CurrentPaper.BitMachineCopy
import EthInapproximability.CurrentPaper.BitMachineRawSequence

/-! Physical serializers for the atomic code constructors needed by the
scheduled generator. No derived syntax word is installed in a starting bank. -/

namespace Paper2.CodeAtomConstructor

open Turing Turing.TM2.Stmt
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open Paper2.GeneratorCode Paper2.GeneratorSerialization

namespace Ticket

inductive HeaderLabel where
  | write | accept
  deriving DecidableEq, Fintype

def headerProgram : HeaderLabel →
    TM2.Stmt (fun _ : Fin 3 => Bool) HeaderLabel Unit
  | .write =>
      push 1 (fun _ => true)
        (push 1 (fun _ => false)
          (push 1 (fun _ => false) (goto (fun _ => .accept))))
  | .accept => halt

abbrev Label := BitMachineRawSequence.Label BitMachineCopy.Label HeaderLabel
abbrev Control := BitMachineRawSequence.Control (Option Bool) Unit

def program : Label → TM2.Stmt (fun _ : Fin 3 => Bool) Label Control :=
  BitMachineRawSequence.program BitMachineCopy.program headerProgram
    .write none ()

def initial (n : Nat) : TM2.Cfg (fun _ : Fin 3 => Bool) Label Control :=
  ⟨some (BitMachineRawSequence.leftLabel .scan), (none,()),
    (BitMachineCopy.cfg (some .scan) none (unary n) [] []).stk⟩

def final (n : Nat) : TM2.Cfg (fun _ : Fin 3 => Bool) Label Control :=
  ⟨none, (none,()),
    (BitMachineCopy.cfg none none (unary n)
      (encodeCode (.ticket n)) []).stk⟩

private theorem header_run (n : Nat) :
    ((advance headerProgram)^[2])
      (⟨some .write, (),
        (BitMachineCopy.cfg none none (unary n)
          (unary n) []).stk⟩ :
        TM2.Cfg (fun _ : Fin 3 => Bool) HeaderLabel Unit) =
      ⟨none, (),
        (BitMachineCopy.cfg none none (unary n)
          (encodeCode (.ticket n)) []).stk⟩ := by
  simp [advance, TM2.step, TM2.stepAux, headerProgram,
    BitMachineCopy.cfg, BitMachineCopy.stackContents,
    encodeCode, unary, Function.update]
  funext i
  fin_cases i <;> rfl

theorem run_ticket (n : Nat) :
    ∃ t ≤ 2*n+7,
      ((advance program)^[t]) (initial n) = final n := by
  have hc := BitMachineCopy.run_correct none (unary n) []
  simp only [unary_length, List.append_nil] at hc
  have hr := header_run n
  obtain ⟨t,ht,he⟩ := BitMachineRawSequence.runs
    BitMachineCopy.program headerProgram
    BitMachineCopy.Label.scan HeaderLabel.write
    none none () ()
    (BitMachineCopy.cfg (some .scan) none (unary n) [] []).stk
    (BitMachineCopy.cfg none none (unary n)
      (unary n) []).stk
    (BitMachineCopy.cfg none none (unary n)
      (encodeCode (.ticket n)) []).stk
    (2*(n+1)+2) 2 hc hr
  exact ⟨t, by omega, by simpa [program, initial, final] using he⟩

end Ticket

namespace Fixed

inductive Atom where
  | bit | emitEmpty | emitFalse | emitTrue | emitTrueFalse | emitTrueTrue
  deriving DecidableEq, Fintype

def atomCode : Atom → Code
  | .bit => .bit
  | .emitEmpty => .emit []
  | .emitFalse => .emit [false]
  | .emitTrue => .emit [true]
  | .emitTrueFalse => .emit [true,false]
  | .emitTrueTrue => .emit [true,true]

def word (a : Atom) : List Bool := encodeCode (atomCode a)

inductive Label where
  | write (a : Atom) | accept
  deriving DecidableEq, Fintype

def pushWord : List Bool → TM2.Stmt (fun _ : Fin 3 => Bool) Label Unit
  | [] => goto (fun _ => .accept)
  | b :: bs => push 1 (fun _ => b) (pushWord bs)

def program : Label → TM2.Stmt (fun _ : Fin 3 => Bool) Label Unit
  | .write a => pushWord (word a).reverse
  | .accept => halt

def initial (a : Atom) : TM2.Cfg (fun _ : Fin 3 => Bool) Label Unit :=
  ⟨some (.write a), (), fun _ => []⟩

def final (a : Atom) : TM2.Cfg (fun _ : Fin 3 => Bool) Label Unit :=
  ⟨none, (), fun i => if i = 1 then word a else []⟩

theorem run_atom (a : Atom) :
    ((advance program)^[2]) (initial a) = final a := by
  cases a <;>
    simp [advance, TM2.step, TM2.stepAux, initial, final,
      program, pushWord, word, atomCode, encodeCode, unary, Function.update] <;>
    funext i <;> fin_cases i <;> rfl

end Fixed

#print axioms Ticket.run_ticket
#print axioms Fixed.run_atom

end Paper2.CodeAtomConstructor
