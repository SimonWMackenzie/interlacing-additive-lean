import EthInapproximability.CurrentPaper.ExactParameterMachineLog

/-!
# Physical scaling and the nested source logarithms

The first stage turns a unary graph-edge count `e` into `max 1 (5*e)`.
Each consumed cell writes five cells. The empty branch writes one cell.
The two subsequent ceiling logarithms are the separately proved physical
program in `ExactParameterMachineLog`.

Source: frozen v8 `03-exact-hardness.tex`, polynomial source padding;
`E-exact-details.tex`, exact scalar choices.
-/

namespace EthInapproximability.CurrentPaper.ExactParameterMachineScale

open Turing Turing.TM2.Stmt BitMachineEncoding BitMachineComposition

/-- The final empty-input branch distinguishes an empty source from a
nonempty source. -/
inductive Label where
  | start | loop
  deriving DecidableEq, Fintype

def pushFive (q : TM2.Stmt (fun _ : Fin 2 => Bool) Label Bool) :
    TM2.Stmt (fun _ : Fin 2 => Bool) Label Bool :=
  push 1 (fun _ => true) (push 1 (fun _ => true) (push 1 (fun _ => true)
    (push 1 (fun _ => true) (push 1 (fun _ => true) q))))

def exactProgram : Label → TM2.Stmt (fun _ : Fin 2 => Bool) Label Bool
  | .start => pop 0 (fun _ b => b.isSome)
      (branch id
        (pushFive (goto (fun _ => .loop)))
        (push 1 (fun _ => true) halt))
  | .loop => pop 0 (fun _ b => b.isSome)
      (branch id
        (pushFive (goto (fun _ => .loop)))
        halt)

def cfg (l : Option Label) (s : Bool) (input output : List Bool) :
    TM2.Cfg (fun _ : Fin 2 => Bool) Label Bool := ⟨l, s, ![input, output]⟩

def run (t : ℕ) (c : TM2.Cfg (fun _ : Fin 2 => Bool) Label Bool) :=
  ((advance exactProgram)^[t]) c

private theorem start_nil :
    advance exactProgram (cfg (some .start) false [] []) =
      cfg none false [] [true] := by
  simp [advance, exactProgram, cfg, TM2.step, TM2.stepAux]
  funext k
  fin_cases k <;> rfl

private theorem start_cons (q : List Bool) :
    advance exactProgram (cfg (some .start) false (true :: q) []) =
      cfg (some .loop) true q (List.replicate 5 true) := by
  simp [advance, exactProgram, pushFive, cfg, TM2.step, TM2.stepAux]
  funext k
  fin_cases k <;> rfl

private theorem loop_nil (out : List Bool) :
    advance exactProgram (cfg (some .loop) true [] out) =
      cfg none false [] out := by
  simp [advance, exactProgram, cfg, TM2.step, TM2.stepAux]

private theorem loop_cons (q out : List Bool) :
    advance exactProgram (cfg (some .loop) true (true :: q) out) =
      cfg (some .loop) true q (List.replicate 5 true ++ out) := by
  simp [advance, exactProgram, pushFive, cfg, TM2.step, TM2.stepAux]
  funext k
  fin_cases k <;> rfl

private theorem loop_run (n : ℕ) (out : List Bool) :
    run (n + 1) (cfg (some .loop) true (List.replicate n true) out) =
      cfg none false [] (List.replicate (5*n) true ++ out) := by
  induction n generalizing out with
  | zero => simp [run, loop_nil]
  | succ n ih =>
      rw [run, Function.iterate_succ_apply]
      simp only [List.replicate_succ]
      rw [loop_cons]
      simpa [run, List.replicate_add, List.append_assoc, Nat.mul_add,
        Nat.add_mul, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
        ih (List.replicate 5 true ++ out)

theorem exact_run (n : ℕ) :
    run (n + 1) (cfg (some .start) false (List.replicate n true) []) =
      cfg none false [] (List.replicate (max 1 (5*n)) true) := by
  cases n with
  | zero => simp [run, start_nil]
  | succ n =>
      rw [run, Function.iterate_succ_apply]
      simp only [List.replicate_succ]
      rw [start_cons]
      simpa [run, List.replicate_add, List.append_assoc,
        Nat.mul_add, Nat.add_mul, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
        using loop_run n (List.replicate 5 true)

noncomputable def machine : BitMachine.Machine :=
  ofFinite (0 : Fin 2) (1 : Fin 2) .start false exactProgram

theorem outputs (n : ℕ) :
    machine.OutputsWithin (List.replicate n true)
      (List.replicate (max 1 (5*n)) true) (n + 1) := by
  have hi : rawInit (0 : Fin 2) Label.start false (List.replicate n true) =
      cfg (some .start) false (List.replicate n true) [] := by
    simp [rawInit, cfg]
    congr 1
    funext k
    fin_cases k <;> rfl
  apply outputsWithin_of_raw_run (0 : Fin 2) (1 : Fin 2) .start false exactProgram
    (List.replicate n true) (List.replicate (max 1 (5*n)) true)
    (n + 1) (n + 1) (by omega)
  · rw [hi]; exact congrArg TM2.Cfg.l (exact_run n)
  · rw [hi]; exact congrArg (fun c => c.stk 1) (exact_run n)

noncomputable def nestedLogMachine : BitMachine.Machine :=
  composition (composition machine ExactParameterMachineLog.machine)
    ExactParameterMachineLog.machine

theorem nestedLog_outputs (n : ℕ) :
    nestedLogMachine.OutputsWithin (List.replicate n true)
      (List.replicate (Nat.clog 2 (Nat.clog 2 (max 1 (5*n)))) true)
      ((n+1) + 2*(max 1 (5*n)) + 2 +
       (UnaryBinaryEncoding.coefficient+6)*(max 1 (5*n)+1)^2 +
       2*(Nat.clog 2 (max 1 (5*n))) + 2 +
       (UnaryBinaryEncoding.coefficient+6)*(Nat.clog 2 (max 1 (5*n))+1)^2) := by
  simpa only [List.length_replicate] using composition_outputsWithin
    (composition machine ExactParameterMachineLog.machine) ExactParameterMachineLog.machine
    (composition_outputsWithin machine ExactParameterMachineLog.machine
      (outputs n) (ExactParameterMachineLog.outputs _))
    (ExactParameterMachineLog.outputs _)

end EthInapproximability.CurrentPaper.ExactParameterMachineScale
