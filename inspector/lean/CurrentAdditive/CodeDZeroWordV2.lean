import EthInapproximability.CurrentPaper.BitMachineBinaryZeroTest
import EthInapproximability.CurrentPaper.BitMachineEncoding

/-!
A physical zero predicate for the little-endian numerator word in a raw
rational.  The output is one bit, true exactly when every input bit is false.
The scan consumes its input; the controller calls this only on a copy.
-/

namespace CurrentAdditive.CodeDZeroWordV2

open Turing TM2.Stmt
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding

inductive Label where
  | scan | emit
  deriving DecidableEq, Fintype

structure Control where
  seenOne : Bool
  bit : Option Bool
  deriving DecidableEq, Fintype

def initial : Control := ⟨false, none⟩

def program : Label → TM2.Stmt (fun _ : Fin 2 => Bool) Label Control
  | .scan => pop 0 (fun s b => ⟨s.seenOne || b.getD false, b⟩)
      (branch (fun s => s.bit.isSome)
        (goto (fun _ => .scan))
        (goto (fun _ => .emit)))
  | .emit => push 1 (fun s => !s.seenOne) halt

def cfg (l : Option Label) (s : Control) (input output : List Bool) :
    TM2.Cfg (fun _ : Fin 2 => Bool) Label Control :=
  ⟨l, s, ![input, output]⟩

def run (t : Nat) (c : TM2.Cfg (fun _ : Fin 2 => Bool) Label Control) :=
  ((advance program)^[t]) c

theorem run_succ (n : Nat) (c : TM2.Cfg (fun _ : Fin 2 => Bool) Label Control) :
    run (n + 1) c = run n (advance program c) := by
  simp only [run, Function.iterate_succ_apply]

theorem run_add (n m : Nat) (c : TM2.Cfg (fun _ : Fin 2 => Bool) Label Control) :
    run (n + m) c = run m (run n c) := by
  simp only [run, Nat.add_comm n m, Function.iterate_add_apply]

theorem step_cons (s : Control) (b : Bool) (rest out : List Bool) :
    advance program (cfg (some .scan) s (b :: rest) out) =
      cfg (some .scan) ⟨s.seenOne || b, some b⟩ rest out := by
  simp [advance, program, cfg, TM2.step, TM2.stepAux]
  funext k; fin_cases k <;> rfl

theorem step_nil (s : Control) (out : List Bool) :
    advance program (cfg (some .scan) s [] out) =
      cfg (some .emit) ⟨s.seenOne, none⟩ [] out := by
  simp [advance, program, cfg, TM2.step, TM2.stepAux]

theorem step_emit (s : Control) (out : List Bool) :
    advance program (cfg (some .emit) s [] out) =
      cfg none s [] ((!s.seenOne) :: out) := by
  simp [advance, program, cfg, TM2.step, TM2.stepAux]
  funext k; fin_cases k <;> rfl

theorem scan_run (s : Control) (input out : List Bool) :
    run (input.length + 1) (cfg (some .scan) s input out) =
      cfg (some .emit) ⟨s.seenOne || input.any id, none⟩ [] out := by
  induction input generalizing s with
  | nil => simpa [run] using step_nil s out
  | cons b rest ih =>
      rw [List.length_cons, show (rest.length + 1 + 1) = (rest.length + 1) + 1 by omega,
        run_succ, step_cons]
      simpa [Bool.or_assoc] using ih ⟨s.seenOne || b, some b⟩

theorem complete_run (input : List Bool) :
    run (input.length + 2) (cfg (some .scan) initial input []) =
      cfg none ⟨input.any id, none⟩ [] [!input.any id] := by
  rw [show input.length + 2 = (input.length + 1) + 1 by omega]
  rw [run_add, scan_run]
  simpa [initial, run] using step_emit ⟨input.any id, none⟩ []

noncomputable def machine : BitMachine.Machine :=
  ofFinite (0 : Fin 2) 1 .scan initial program

theorem outputs (input : List Bool) :
    machine.OutputsWithin input [!input.any id] (input.length + 2) := by
  have hi : rawInit (0 : Fin 2) Label.scan initial input =
      cfg (some .scan) initial input [] := by
    simp only [rawInit, cfg]
    congr 1
    funext k; fin_cases k <;> rfl
  apply outputsWithin_of_raw_run (0 : Fin 2) 1 .scan initial program
    input [!input.any id] (input.length + 2) (input.length + 2) (le_refl _)
  · rw [hi]
    exact congrArg (fun c => c.l) (complete_run input)
  · rw [hi]
    exact congrArg (fun c => c.stk (1 : Fin 2)) (complete_run input)

theorem output_true_iff_zero (input : List Bool) :
    (!input.any id) = true ↔ EncodedCommunication.bitsValue input = 0 := by
  simpa using BitMachineBinaryZeroTest.any_false_iff_value_zero input

#print axioms outputs
#print axioms output_true_iff_zero

end CurrentAdditive.CodeDZeroWordV2
