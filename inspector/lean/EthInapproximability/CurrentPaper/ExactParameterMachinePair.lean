import EthInapproximability.CurrentPaper.MatrixUnaryArithmetic

/-!
# Physical packing of two unary operands

The multiplier and extension-degree programs expect the separated word
`true^n ++ false :: true^m`. This fixed three-stack program constructs it
from two unary operand stacks. It scans the second operand first because
stacks push at the front. The source stacks are consumed; callers pass
source-preserving copies when the operands must survive.
-/

namespace EthInapproximability.CurrentPaper.ExactParameterMachinePair

open Turing Turing.TM2.Stmt BitMachineEncoding

inductive Label where
  | right | separator | left
  deriving DecidableEq, Fintype

def program : Label → TM2.Stmt (fun _ : Fin 3 => Bool) Label Bool
  | .right => pop 1 (fun _ b => b.isSome)
      (branch id (push 2 (fun _ => true) (goto (fun _ => .right)))
        (goto (fun _ => .separator)))
  | .separator => push 2 (fun _ => false) (goto (fun _ => .left))
  | .left => pop 0 (fun _ b => b.isSome)
      (branch id (push 2 (fun _ => true) (goto (fun _ => .left))) halt)

abbrev Config := TM2.Cfg (fun _ : Fin 3 => Bool) Label Bool

def cfg (l : Option Label) (flag : Bool) (left right out : List Bool) : Config :=
  ⟨l, flag, ![left, right, out]⟩

def run (t : ℕ) (c : Config) : Config := ((advance program)^[t]) c

theorem run_add (m n : ℕ) (c : Config) : run (m+n) c = run n (run m c) := by
  simpa only [run, Nat.add_comm] using Function.iterate_add_apply (advance program) n m c

private theorem replicate_commute (n : ℕ) (out : List Bool) :
    List.replicate n true ++ true :: out =
      true :: (List.replicate n true ++ out) := by
  induction n with
  | zero => rfl
  | succ n ih => simpa [List.replicate_succ, List.append_assoc] using ih

private theorem right_cons (left q out : List Bool) (flag : Bool) :
    advance program (cfg (some .right) flag left (true :: q) out) =
      cfg (some .right) true left q (true :: out) := by
  simp [advance, program, cfg, TM2.step, TM2.stepAux]
  funext k
  fin_cases k <;> rfl

private theorem right_nil (left out : List Bool) (flag : Bool) :
    advance program (cfg (some .right) flag left [] out) =
      cfg (some .separator) false left [] out := by
  simp [advance, program, cfg, TM2.step, TM2.stepAux]

private theorem separator_step (left out : List Bool) (flag : Bool) :
    advance program (cfg (some .separator) flag left [] out) =
      cfg (some .left) flag left [] (false :: out) := by
  simp [advance, program, cfg, TM2.step, TM2.stepAux]
  funext k
  fin_cases k <;> rfl

private theorem left_cons (q out : List Bool) (flag : Bool) :
    advance program (cfg (some .left) flag (true :: q) [] out) =
      cfg (some .left) true q [] (true :: out) := by
  simp [advance, program, cfg, TM2.step, TM2.stepAux]
  funext k
  fin_cases k <;> rfl

private theorem left_nil (out : List Bool) (flag : Bool) :
    advance program (cfg (some .left) flag [] [] out) =
      cfg none false [] [] out := by
  simp [advance, program, cfg, TM2.step, TM2.stepAux]

private theorem right_run (m : ℕ) (left out : List Bool) (flag : Bool) :
    run (m+1) (cfg (some .right) flag left (List.replicate m true) out) =
      cfg (some .separator) false left [] (List.replicate m true ++ out) := by
  induction m generalizing out flag with
  | zero => simpa [run] using right_nil left out flag
  | succ m ih =>
      rw [run, Function.iterate_succ_apply]
      simp only [List.replicate_succ]
      rw [right_cons]
      have hh := ih (true :: out) true
      rw [replicate_commute] at hh
      simpa [run, List.replicate_succ] using hh

private theorem left_run (n : ℕ) (out : List Bool) (flag : Bool) :
    run (n+1) (cfg (some .left) flag (List.replicate n true) [] out) =
      cfg none false [] [] (List.replicate n true ++ out) := by
  induction n generalizing out flag with
  | zero => simpa [run] using left_nil out flag
  | succ n ih =>
      rw [run, Function.iterate_succ_apply]
      simp only [List.replicate_succ]
      rw [left_cons]
      have hh := ih (true :: out) true
      rw [replicate_commute] at hh
      simpa [run, List.replicate_succ] using hh

theorem exact_run (n m : ℕ) :
    run (n+m+3) (cfg (some .right) false
      (List.replicate n true) (List.replicate m true) []) =
      cfg none false [] [] (MatrixUnaryArithmetic.encodeInput n m) := by
  have hr := right_run m (List.replicate n true) [] false
  simp only [List.append_nil] at hr
  have hs := separator_step (List.replicate n true) (List.replicate m true) false
  have hl := left_run n (false :: List.replicate m true) false
  rw [show n+m+3 = (m+1)+(1+(n+1)) by omega, run_add, hr,
    run_add]
  change run (n+1) (advance program
    (cfg (some .separator) false (List.replicate n true) []
      (List.replicate m true))) = _
  rw [hs, hl]
  rfl

end EthInapproximability.CurrentPaper.ExactParameterMachinePair
