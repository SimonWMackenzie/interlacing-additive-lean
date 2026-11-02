import EthInapproximability.CurrentPaper.MatrixSourceColumnMachine

/-!
# Unsaturated active-rank counting for variable-bin Stage--4

The exact-NP source controller saturates its finite-control rank at two.
This fixed two-stack controller instead records the full count in unary,
so the number of bins `s` is not in finite control.
-/

namespace EthInapproximability.CurrentPaper.MatrixStage4ActiveCount

open Turing Turing.TM2.Stmt BitMachineEncoding

abbrev Stack := Fin 2
abbrev Control := Option Bool
abbrev Config := TM2.Cfg (fun _ : Stack => Bool) Unit Control

def initial : Control := none

def program : Unit → TM2.Stmt (fun _ : Stack => Bool) Unit Control
  | () => pop 0 (fun _ b => b)
      (branch Option.isSome
        (branch (fun v => v.getD false)
          (push 1 (fun _ => true) (goto (fun _ => ())))
          (goto (fun _ => ())))
        (load (fun _ => none) halt))

def cfg (l : Option Unit) (v : Control) (input count : List Bool) : Config :=
  ⟨l,v,![input,count]⟩

def run (t : ℕ) (c : Config) : Config := ((advance program)^[t]) c

theorem step_true (v : Control) (rest count : List Bool) :
    advance program (cfg (some ()) v (true::rest) count) =
      cfg (some ()) (some true) rest (true::count) := by
  simp [advance,TM2.step,TM2.stepAux,program,cfg]
  funext k
  fin_cases k <;> rfl

theorem step_false (v : Control) (rest count : List Bool) :
    advance program (cfg (some ()) v (false::rest) count) =
      cfg (some ()) (some false) rest count := by
  simp [advance,TM2.step,TM2.stepAux,program,cfg]
  funext k
  fin_cases k <;> rfl

theorem step_nil (v : Control) (count : List Bool) :
    advance program (cfg (some ()) v [] count) =
      cfg none initial [] count := by
  simp [advance,TM2.step,TM2.stepAux,program,cfg,initial]

theorem count_run (input : List Bool) (count : ℕ) (v : Control) :
    run (input.length+1) (cfg (some ()) v input
      (List.replicate count true)) =
    cfg none initial []
      (List.replicate (count+(input.filter id).length) true) := by
  induction input generalizing count v with
  | nil =>
    simpa only [List.length_nil, List.filter_nil, Nat.add_zero,
      run, Function.iterate_succ_apply, Function.iterate_zero,
      Function.id_def] using step_nil v (List.replicate count true)
  | cons b rest ih =>
    cases b with
    | false =>
      simp only [List.length_cons, List.filter_cons]
      rw [show rest.length+1+1 = (rest.length+1)+1 by omega]
      simp only [run,Function.iterate_succ_apply]
      rw [show advance program
        (cfg (some ()) v (false::rest) (List.replicate count true)) =
        cfg (some ()) (some false) rest (List.replicate count true) from
          step_false v rest (List.replicate count true)]
      exact ih count (some false)
    | true =>
      simp only [List.length_cons, List.filter_cons]
      rw [show rest.length+1+1 = (rest.length+1)+1 by omega]
      simp only [run,Function.iterate_succ_apply]
      rw [show advance program
        (cfg (some ()) v (true::rest) (List.replicate count true)) =
        cfg (some ()) (some true) rest (true::List.replicate count true) from
          step_true v rest (List.replicate count true)]
      simpa only [List.replicate_succ, Nat.add_assoc,
        Nat.add_comm, Nat.add_left_comm] using ih (count+1) (some true)

theorem active_rank_run {n q : ℕ}
    (vectors : Fin n → Fin q → Bool) (i : Fin n) (α : Fin q) :
    run (i.val+1) (cfg (some ()) initial
      (MatrixSourceColumnMachine.beforeColumn vectors i α).reverse []) =
    cfg none initial []
      (List.replicate (Construction.activeRank vectors α i) true) := by
  have h := count_run
    (MatrixSourceColumnMachine.beforeColumn vectors i α).reverse 0 initial
  simp only [List.length_reverse, MatrixSourceColumnMachine.beforeColumn_length,
    List.replicate_zero, Nat.zero_add, List.filter_reverse,
    List.length_reverse, MatrixSourceColumnMachine.beforeColumn_count] at h
  exact h

end EthInapproximability.CurrentPaper.MatrixStage4ActiveCount
