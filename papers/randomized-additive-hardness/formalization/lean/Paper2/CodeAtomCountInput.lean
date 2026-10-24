import Paper2.CodeAtomConstructor

/-! Ticket syntax from a delimiter-free unary count cell. The full-unary
constructor remains separate: this adapter physically supplies its terminator. -/

namespace Paper2.CodeAtomCountInput

open Turing Turing.TM2.Stmt
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open Paper2.GeneratorCode Paper2.GeneratorSerialization

inductive InitLabel where
  | write | accept
  deriving DecidableEq, Fintype

def initProgram : InitLabel →
    TM2.Stmt (fun _ : Fin 3 => Bool) InitLabel Unit
  | .write => push 1 (fun _ => false) (goto (fun _ => .accept))
  | .accept => halt

abbrev PreLabel := BitMachineRawSequence.Label InitLabel BitMachineCopy.Label
abbrev PreControl := BitMachineRawSequence.Control Unit (Option Bool)

def preProgram : PreLabel → TM2.Stmt (fun _ : Fin 3 => Bool) PreLabel PreControl :=
  BitMachineRawSequence.program initProgram BitMachineCopy.program .scan () none

abbrev Label := BitMachineRawSequence.Label PreLabel CodeAtomConstructor.Ticket.HeaderLabel
abbrev Control := BitMachineRawSequence.Control PreControl Unit

def program : Label → TM2.Stmt (fun _ : Fin 3 => Bool) Label Control :=
  BitMachineRawSequence.program preProgram CodeAtomConstructor.Ticket.headerProgram
    .write ((),none) ()

def initial (n : Nat) : TM2.Cfg (fun _ : Fin 3 => Bool) Label Control :=
  ⟨some (BitMachineRawSequence.leftLabel
    (BitMachineRawSequence.leftLabel .write)), (((),none),()),
    (BitMachineCopy.cfg none none (List.replicate n true) [] []).stk⟩

def final (n : Nat) : TM2.Cfg (fun _ : Fin 3 => Bool) Label Control :=
  ⟨none, (((),none),()),
    (BitMachineCopy.cfg none none (List.replicate n true)
      (encodeCode (.ticket n)) []).stk⟩

private theorem init_run (n : Nat) :
    ((advance initProgram)^[2])
      (⟨some .write, (),
        (BitMachineCopy.cfg none none (List.replicate n true) [] []).stk⟩ :
        TM2.Cfg (fun _ : Fin 3 => Bool) InitLabel Unit) =
      ⟨none, (),
        (BitMachineCopy.cfg none none (List.replicate n true) [false] []).stk⟩ := by
  simp [advance, TM2.step, TM2.stepAux, initProgram,
    BitMachineCopy.cfg, BitMachineCopy.stackContents]
  funext i
  fin_cases i <;> rfl

private theorem header_run (n : Nat) :
    ((advance CodeAtomConstructor.Ticket.headerProgram)^[2])
      (⟨some .write, (),
        (BitMachineCopy.cfg none none (List.replicate n true)
          (unary n) []).stk⟩ :
        TM2.Cfg (fun _ : Fin 3 => Bool) CodeAtomConstructor.Ticket.HeaderLabel Unit) =
      ⟨none, (),
        (BitMachineCopy.cfg none none (List.replicate n true)
          (encodeCode (.ticket n)) []).stk⟩ := by
  simp [advance, TM2.step, TM2.stepAux, CodeAtomConstructor.Ticket.headerProgram,
    BitMachineCopy.cfg, BitMachineCopy.stackContents,
    encodeCode, unary, Function.update]
  funext i
  fin_cases i <;> rfl

theorem run_ticket_count (n : Nat) :
    ∃ t ≤ 2*n+8,
      ((advance program)^[t]) (initial n) = final n := by
  have hi := init_run n
  have hc := BitMachineCopy.run_correct none (List.replicate n true) [false]
  simp only [List.length_replicate] at hc
  obtain ⟨a,ha,har⟩ := BitMachineRawSequence.runs
    initProgram BitMachineCopy.program InitLabel.write BitMachineCopy.Label.scan
    () () none none
    (BitMachineCopy.cfg none none (List.replicate n true) [] []).stk
    (BitMachineCopy.cfg none none (List.replicate n true) [false] []).stk
    (BitMachineCopy.cfg none none (List.replicate n true)
      (unary n) []).stk
    2 (2*n+2) hi (by simpa [unary] using hc)
  have hr := header_run n
  obtain ⟨t,ht,he⟩ := BitMachineRawSequence.runs
    preProgram CodeAtomConstructor.Ticket.headerProgram
    (BitMachineRawSequence.leftLabel InitLabel.write)
    CodeAtomConstructor.Ticket.HeaderLabel.write
    ((),none) ((),none) () ()
    (BitMachineCopy.cfg none none (List.replicate n true) [] []).stk
    (BitMachineCopy.cfg none none (List.replicate n true)
      (unary n) []).stk
    (BitMachineCopy.cfg none none (List.replicate n true)
      (encodeCode (.ticket n)) []).stk
    a 2 har hr
  exact ⟨t, by omega, by simpa [program, initial, final] using he⟩

#print axioms run_ticket_count

end Paper2.CodeAtomCountInput
