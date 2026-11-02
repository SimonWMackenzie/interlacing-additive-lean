import EthInapproximability.CurrentPaper.EncodedCommunication
import EthInapproximability.CurrentPaper.BitMachineEncoding

/-!
A literal finite-stack initializer for the four-field Gauss state.  It takes
the already encoded matrix as its sole input and writes the matrix field,
two empty unary cursor fields, and the encoded empty pivot-list field.
-/

namespace CurrentAdditive.GaussInitialMachine

open Turing TM2.Stmt
open EthInapproximability.CurrentPaper
open BitMachineEncoding EncodedCommunication

inductive Label where
  | scan | flush
  deriving DecidableEq, Fintype

def suffix : List Bool := [false, false, true, false, false]

def program : Label → TM2.Stmt (fun _ : Fin 3 => Bool) Label (Option Bool)
  | .scan => pop 0 (fun _ b => b)
      (branch Option.isSome
        (push 1 (fun _ => true)
          (push 1 (fun b => b.getD false) (goto (fun _ => .scan))))
        (push 1 (fun _ => false)
          (push 1 (fun _ => false)
            (push 1 (fun _ => false)
              (push 1 (fun _ => true)
                (push 1 (fun _ => false)
                  (push 1 (fun _ => false) (goto (fun _ => .flush)))))))))
  | .flush => pop 1 (fun _ b => b)
      (branch Option.isSome
        (push 2 (fun b => b.getD false) (goto (fun _ => .flush)))
        halt)

def contents (input saved output : List Bool) : Fin 3 → List Bool :=
  fun j => if j = 0 then input else if j = 1 then saved else output

def cfg (l : Option Label) (v : Option Bool)
    (input saved output : List Bool) :
    TM2.Cfg (fun _ : Fin 3 => Bool) Label (Option Bool) :=
  ⟨l, v, contents input saved output⟩

def run (n : Nat) (c : TM2.Cfg (fun _ : Fin 3 => Bool) Label (Option Bool)) :=
  ((advance program)^[n]) c

theorem run_succ (n : Nat) (c : TM2.Cfg (fun _ : Fin 3 => Bool) Label (Option Bool)) :
    run (n+1) c = run n (advance program c) :=
  Function.iterate_succ_apply _ _ _

theorem run_add (m n : Nat) (c : TM2.Cfg (fun _ : Fin 3 => Bool) Label (Option Bool)) :
    run (m+n) c = run n (run m c) := by
  simpa only [run, Nat.add_comm] using Function.iterate_add_apply (advance program) n m c

theorem scan_cons (v : Option Bool) (b : Bool) (q saved output : List Bool) :
    advance program (cfg (some .scan) v (b :: q) saved output) =
      cfg (some .scan) (some b) q (b :: true :: saved) output := by
  simp [advance, cfg, contents, TM2.step, TM2.stepAux, program]
  funext j
  fin_cases j <;> rfl

theorem scan_nil (v : Option Bool) (saved output : List Bool) :
    advance program (cfg (some .scan) v [] saved output) =
      cfg (some .flush) none [] (suffix.reverse ++ [false] ++ saved) output := by
  simp [advance, cfg, contents, TM2.step, TM2.stepAux, program, suffix]
  funext j
  fin_cases j <;> rfl

theorem scan_run (v : Option Bool) (q saved output : List Bool) :
    run (q.length+1) (cfg (some .scan) v q saved output) =
      cfg (some .flush) none [] (suffix.reverse ++ (field q).reverse ++ saved) output := by
  induction q generalizing v saved with
  | nil =>
      rw [show ([] : List Bool).length + 1 = 0 + 1 by rfl, run_succ, scan_nil]
      simp [run, field]
  | cons b q ih =>
      rw [List.length_cons, run_succ, scan_cons, ih]
      simp [field, List.reverse_cons, List.append_assoc]

theorem flush_cons (v : Option Bool) (b : Bool) (input saved output : List Bool) :
    advance program (cfg (some .flush) v input (b :: saved) output) =
      cfg (some .flush) (some b) input saved (b :: output) := by
  simp [advance, cfg, contents, TM2.step, TM2.stepAux, program]
  funext j
  fin_cases j <;> rfl

theorem flush_nil (v : Option Bool) (input output : List Bool) :
    advance program (cfg (some .flush) v input [] output) =
      cfg none none input [] output := by
  simp [advance, cfg, contents, TM2.step, TM2.stepAux, program]

theorem flush_run (v : Option Bool) (input saved output : List Bool) :
    run (saved.length+1) (cfg (some .flush) v input saved output) =
      cfg none none input [] (saved.reverse ++ output) := by
  induction saved generalizing v output with
  | nil => simp [flush_nil, run]
  | cons b saved ih =>
      rw [List.length_cons, run_succ, flush_cons, ih]
      simp [List.append_assoc]

theorem raw_correct (q : List Bool) :
    run (3*q.length+8) (cfg (some .scan) none q [] []) =
      cfg none none [] [] (field q ++ suffix) := by
  have hs := scan_run none q [] []
  simp only [List.append_nil] at hs
  have hf := flush_run none [] (suffix.reverse ++ (field q).reverse) []
  rw [show 3*q.length+8 = (q.length+1) +
      ((suffix.reverse ++ (field q).reverse).length+1) by
        simp [field_length, suffix]; omega]
  rw [run_add, hs, hf]
  simp [List.reverse_append]

noncomputable def machine : BitMachine.Machine :=
  ofFinite (0 : Fin 3) 2 .scan (none : Option Bool) program

theorem output (q : List Bool) :
    machine.OutputsWithin q (field q ++ suffix) (3*q.length+8) := by
  apply outputsWithin_of_raw_run (0 : Fin 3) 2 .scan (none : Option Bool)
    program q (field q ++ suffix) (3*q.length+8) (3*q.length+8) le_rfl
  · change (run (3*q.length+8) _).l = none
    have hi : rawInit (0 : Fin 3) .scan (none : Option Bool) q =
        cfg (some .scan) none q [] [] := by
      unfold rawInit cfg contents
      congr 1
      funext j
      fin_cases j <;> rfl
    rw [hi, raw_correct]
    rfl

  · change (run (3*q.length+8) _).stk 2 = field q ++ suffix
    have hi : rawInit (0 : Fin 3) .scan (none : Option Bool) q =
        cfg (some .scan) none q [] [] := by
      unfold rawInit cfg contents
      congr 1
      funext j
      fin_cases j <;> rfl
    rw [hi, raw_correct]
    rfl

theorem polytime : BitMachine.Polytime (fun q => field q ++ suffix) := by
  refine ⟨machine, 11, 1, ?_⟩
  intro q
  exact BitMachine.outputsWithin_mono machine (output q) (by simp only [pow_one]; omega)

#print axioms polytime

end CurrentAdditive.GaussInitialMachine
