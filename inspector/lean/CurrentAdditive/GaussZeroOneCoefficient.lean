import EthInapproximability.CurrentPaper.BitMachineEncoding

/-! Fixed TM2 writer for the canonical RawRat records 0 and 1. The program
branches on one input bit; both output words are literal finite constants. -/

namespace CurrentAdditive.GaussZeroOneCoefficient

open Turing TM2.Stmt
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding

def zeroWord : List Bool := [false, false, true, true, false]
def oneWord : List Bool := [false, true, true, false, true, true, false]

def write : List Bool → TM2.Stmt (fun _ : Fin 2 => Bool) Unit (Option Bool)
  | [] => halt
  | b :: bs => push 1 (fun _ => b) (write bs)

def program : Unit → TM2.Stmt (fun _ : Fin 2 => Bool) Unit (Option Bool)
  | () => pop 0 (fun _ b => b)
      (branch (fun b => b == some true)
        (write oneWord.reverse) (write zeroWord.reverse))

def cfg (l : Option Unit) (v : Option Bool)
    (input output : List Bool) :
    TM2.Cfg (fun _ : Fin 2 => Bool) Unit (Option Bool) :=
  ⟨l, v, ![input, output]⟩

private theorem write_correct (w : List Bool) (v : Option Bool)
    (S : Fin 2 → List Bool) :
    TM2.stepAux (write w) v S =
      ⟨none, v, Function.update S 1 (w.reverse ++ S 1)⟩ := by
  induction w generalizing S with
  | nil =>
      simp [write, TM2.stepAux, Function.update_eq_self]
  | cons b bs ih =>
      simp only [write, TM2.stepAux]
      rw [ih]
      simp [List.reverse_cons, List.append_assoc,
        Function.update_self, Function.update_idem]

private theorem step_one (input : List Bool) (b : Bool) (output : List Bool) :
    advance program (cfg (some ()) none (b :: input) output) =
      cfg none (some b) input
        ((if b then oneWord else zeroWord) ++ output) := by
  cases b with
  | false =>
      simp [advance, program, cfg, TM2.step, TM2.stepAux,
        write_correct, zeroWord]
      funext i
      fin_cases i <;> simp
  | true =>
      simp [advance, program, cfg, TM2.step, TM2.stepAux,
        write_correct, oneWord]
      funext i
      fin_cases i <;> simp

def result (input : List Bool) : List Bool :=
  if input.head?.getD false then oneWord else zeroWord

noncomputable def machine : BitMachine.Machine :=
  ofFinite (0 : Fin 2) 1 () none program

theorem initial_cfg (input : List Bool) :
    rawInit (0 : Fin 2) () (none : Option Bool) input =
      cfg (some ()) none input [] := by
  unfold rawInit cfg
  congr 1
  funext i
  fin_cases i <;> rfl

theorem outputs_bit (b : Bool) :
    machine.OutputsWithin [b] (if b then oneWord else zeroWord) 1 := by
  apply outputsWithin_of_raw_run (0 : Fin 2) 1 () (none : Option Bool)
    program [b] (if b then oneWord else zeroWord) 1 1 (by omega)
  · rw [initial_cfg]
    change (advance program (cfg (some ()) none [b] [])).l = none
    rw [step_one]
    rfl
  · rw [initial_cfg]
    change (advance program (cfg (some ()) none [b] [])).stk 1 =
      if b then oneWord else zeroWord
    rw [step_one]
    simp [cfg]

#print axioms outputs_bit

end CurrentAdditive.GaussZeroOneCoefficient
