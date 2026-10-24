import EthInapproximability.CurrentPaper.BitMachineCopy
import EthInapproximability.CurrentPaper.BitMachineRawSequence
import Paper2.GeneratorSerialization

/-! A reusable physical adapter from a delimiter-free public count cell to
the terminated unary word required inside a serialized constructor. -/

namespace Paper2.CodeRawCountTerm

open Turing Turing.TM2.Stmt
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open Paper2.GeneratorSerialization

inductive DelimiterLabel where
  | write | accept
  deriving DecidableEq, Fintype

def delimiterProgram : DelimiterLabel →
    TM2.Stmt (fun _ : Fin 3 => Bool) DelimiterLabel Unit
  | .write => push 1 (fun _ => false) (goto (fun _ => .accept))
  | .accept => halt

abbrev Label :=
  BitMachineRawSequence.Label DelimiterLabel BitMachineCopy.Label
abbrev Control :=
  BitMachineRawSequence.Control Unit (Option Bool)

def program : Label → TM2.Stmt (fun _ : Fin 3 => Bool) Label Control :=
  BitMachineRawSequence.program delimiterProgram BitMachineCopy.program
    BitMachineCopy.Label.scan () none

def initial (n : Nat) : TM2.Cfg (fun _ : Fin 3 => Bool) Label Control :=
  ⟨some (BitMachineRawSequence.leftLabel DelimiterLabel.write),
    ((),none), (BitMachineCopy.cfg none none
      (List.replicate n true) [] []).stk⟩

def afterDelimiter (n : Nat) : Fin 3 → List Bool :=
  (BitMachineCopy.cfg none none (List.replicate n true) [false] []).stk

def final (n : Nat) : TM2.Cfg (fun _ : Fin 3 => Bool) Label Control :=
  ⟨none, ((),none), (BitMachineCopy.cfg none none
    (List.replicate n true) (unary n) []).stk⟩

theorem delimiter_run (n : Nat) :
    ((advance delimiterProgram)^[2])
      (⟨some .write, (),
        (BitMachineCopy.cfg none none
          (List.replicate n true) [] []).stk⟩ :
        TM2.Cfg (fun _ : Fin 3 => Bool) DelimiterLabel Unit) =
      ⟨none, (), afterDelimiter n⟩ := by
  simp [advance, TM2.step, TM2.stepAux,
    delimiterProgram, afterDelimiter,
    BitMachineCopy.cfg, BitMachineCopy.stackContents]
  funext i
  fin_cases i <;> rfl

theorem copy_run (n : Nat) :
    ((advance BitMachineCopy.program)^[2*n+2])
      (⟨some .scan, none, afterDelimiter n⟩ :
        TM2.Cfg (fun _ : Fin 3 => Bool)
          BitMachineCopy.Label (Option Bool)) =
      ⟨none, none,
        (BitMachineCopy.cfg none none
          (List.replicate n true) (unary n) []).stk⟩ := by
  have h := BitMachineCopy.run_correct none
    (List.replicate n true) [false]
  simp only [List.length_replicate] at h
  simpa only [BitMachineCopy.run, afterDelimiter,
    BitMachineCopy.cfg, List.replicate_append_replicate,
    unary] using h

theorem run_exact (n : Nat) :
    ∃ t ≤ 2*n+5,
      ((advance program)^[t]) (initial n) = final n := by
  obtain ⟨t,ht,hr⟩ := BitMachineRawSequence.runs
    delimiterProgram BitMachineCopy.program DelimiterLabel.write
    BitMachineCopy.Label.scan () () none none
    (BitMachineCopy.cfg none none
      (List.replicate n true) [] []).stk
    (afterDelimiter n)
    (BitMachineCopy.cfg none none
      (List.replicate n true) (unary n) []).stk
    2 (2*n+2) (delimiter_run n) (copy_run n)
  exact ⟨t, by omega, hr⟩

#print axioms run_exact

end Paper2.CodeRawCountTerm
