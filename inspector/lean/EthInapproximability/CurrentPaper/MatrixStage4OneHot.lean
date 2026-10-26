import EthInapproximability.CurrentPaper.BitMachineEncoding

/-!
# Physical one-hot family-field decoder

The fixed two-stack machine consumes a literal one-hot word and writes the
selected coordinate as a unary stack. It does not receive that coordinate
in control. Selecting the one-hot word from a flat family table is a
separate charged stage.
-/

namespace EthInapproximability.CurrentPaper.MatrixStage4OneHot

open Turing Turing.TM2.Stmt BitMachineEncoding

abbrev Config := TM2.Cfg (fun _ : Fin 2 => Bool) Unit (Option Bool)

def program : Unit → TM2.Stmt (fun _ : Fin 2 => Bool) Unit (Option Bool)
  | () => pop 0 (fun _ b => b)
      (branch Option.isSome
        (branch (fun v => v.getD false)
          (load (fun _ => none) halt)
          (push 1 (fun _ => true) (goto (fun _ => ()))))
        (load (fun _ => none) halt))

def cfg (l : Option Unit) (v : Option Bool)
    (input output : List Bool) : Config := ⟨l,v,![input,output]⟩

def run (t : ℕ) (c : Config) : Config := ((advance program)^[t]) c

theorem step_false (v : Option Bool) (input output : List Bool) :
    advance program (cfg (some ()) v (false::input) output) =
      cfg (some ()) (some false) input (true::output) := by
  simp [advance,TM2.step,TM2.stepAux,program,cfg]
  funext k
  fin_cases k <;> rfl

theorem step_true (v : Option Bool) (input output : List Bool) :
    advance program (cfg (some ()) v (true::input) output) =
      cfg none none input output := by
  simp [advance,TM2.step,TM2.stepAux,program,cfg]
  funext k
  fin_cases k <;> rfl

theorem one_hot_run (index count : ℕ) (suffix : List Bool)
    (v : Option Bool) :
    run (index+1) (cfg (some ()) v
      (List.replicate index false ++ true::suffix)
      (List.replicate count true)) =
      cfg none none suffix (List.replicate (index+count) true) := by
  induction index generalizing count v with
  | zero =>
    simpa only [List.replicate_zero,List.nil_append,Nat.zero_add,
      run,Function.iterate_succ_apply,Function.iterate_zero,Function.id_def]
      using step_true v suffix (List.replicate count true)
  | succ n ih =>
    simp only [List.replicate_succ,List.cons_append]
    rw [show n+1+1 = (n+1)+1 by omega]
    simp only [run,Function.iterate_succ_apply]
    rw [step_false v]
    simpa only [List.replicate_succ,Nat.succ_add,Nat.add_assoc,
      Nat.add_comm,Nat.add_left_comm] using ih (count+1) (some false)

end EthInapproximability.CurrentPaper.MatrixStage4OneHot
