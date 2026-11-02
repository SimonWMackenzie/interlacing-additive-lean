import Paper2.GeneratorSerialization
import Paper2.UnaryLabelParser
import EthInapproximability.CurrentPaper.BitMachineEncoding

/-! A physical fixed-control header reader for first-order generator syntax.
It extracts a constructor and scalar operands, not recursive child meanings. -/

namespace Paper2.CodeHeaderMachine

open Turing Turing.TM2.Stmt
open EthInapproximability.CurrentPaper.BitMachineEncoding
open Paper2.GeneratorCode Paper2.GeneratorSerialization

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000

inductive Kind where
  | emit | ticket | bit | append | branch3
  deriving DecidableEq, Fintype, Repr

inductive Label where
  | first | secondF | secondT | thirdFF | thirdFT | thirdTF | thirdTT
  | unaryEmit | unaryTicket | unaryBranchN | unaryBranchA | unaryBranchB
  | emitCopy | emitRestore | emitReverse
  | acceptEmit | acceptTicket | acceptBit | acceptAppend | acceptBranch
  | reject
  deriving DecidableEq, Fintype

/-- Only a one-bit register and one of five finite constructor tags. -/
abbrev Control := Option Bool × Option Kind

def program : Label → TM2.Stmt (fun _ : Fin 7 => Bool) Label Control
  | .first =>
      pop 0 (fun s b => (b, s.2))
        (branch (fun s => s.1.isSome)
          (branch (fun s => s.1.getD false)
            (goto (fun _ => .secondT)) (goto (fun _ => .secondF)))
          (goto (fun _ => .reject)))
  | .secondF =>
      pop 0 (fun s b => (b, s.2))
        (branch (fun s => s.1.isSome)
          (branch (fun s => s.1.getD false)
            (goto (fun _ => .thirdFT)) (goto (fun _ => .thirdFF)))
          (goto (fun _ => .reject)))
  | .secondT =>
      pop 0 (fun s b => (b, s.2))
        (branch (fun s => s.1.isSome)
          (branch (fun s => s.1.getD false)
            (goto (fun _ => .thirdTT)) (goto (fun _ => .thirdTF)))
          (goto (fun _ => .reject)))
  | .thirdFF =>
      pop 0 (fun s b => (b, s.2))
        (branch (fun s => s.1.isSome)
          (branch (fun s => s.1.getD false)
            (goto (fun _ => .unaryTicket)) (goto (fun _ => .unaryEmit)))
          (goto (fun _ => .reject)))
  | .thirdFT =>
      pop 0 (fun s b => (b, s.2))
        (branch (fun s => s.1.isSome)
          (branch (fun s => s.1.getD false)
            (goto (fun _ => .acceptAppend)) (goto (fun _ => .acceptBit)))
          (goto (fun _ => .reject)))
  | .thirdTF =>
      pop 0 (fun s b => (b, s.2))
        (branch (fun s => s.1.isSome)
          (branch (fun s => s.1.getD false)
            (goto (fun _ => .reject)) (goto (fun _ => .unaryBranchN)))
          (goto (fun _ => .reject)))
  | .thirdTT => pop 0 (fun s bit => (bit, s.2)) (goto (fun _ => .reject))
  | .unaryEmit =>
      pop 0 (fun s b => (b, s.2))
        (branch (fun s => s.1.isSome)
          (branch (fun s => s.1.getD false)
            (push 1 (fun _ => true) (goto (fun _ => .unaryEmit)))
            (goto (fun _ => .emitCopy)))
          (goto (fun _ => .reject)))
  | .unaryTicket =>
      pop 0 (fun s b => (b, s.2))
        (branch (fun s => s.1.isSome)
          (branch (fun s => s.1.getD false)
            (push 1 (fun _ => true) (goto (fun _ => .unaryTicket)))
            (goto (fun _ => .acceptTicket)))
          (goto (fun _ => .reject)))
  | .unaryBranchN =>
      pop 0 (fun s b => (b, s.2))
        (branch (fun s => s.1.isSome)
          (branch (fun s => s.1.getD false)
            (push 1 (fun _ => true) (goto (fun _ => .unaryBranchN)))
            (goto (fun _ => .unaryBranchA)))
          (goto (fun _ => .reject)))
  | .unaryBranchA =>
      pop 0 (fun s b => (b, s.2))
        (branch (fun s => s.1.isSome)
          (branch (fun s => s.1.getD false)
            (push 2 (fun _ => true) (goto (fun _ => .unaryBranchA)))
            (goto (fun _ => .unaryBranchB)))
          (goto (fun _ => .reject)))
  | .unaryBranchB =>
      pop 0 (fun s b => (b, s.2))
        (branch (fun s => s.1.isSome)
          (branch (fun s => s.1.getD false)
            (push 3 (fun _ => true) (goto (fun _ => .unaryBranchB)))
            (goto (fun _ => .acceptBranch)))
          (goto (fun _ => .reject)))
  | .emitCopy =>
      pop 1 (fun s mark => (mark, s.2))
        (branch (fun s => s.1.isSome)
          (push 6 (fun _ => true)
            (pop 0 (fun s b => (b, s.2))
              (branch (fun s => s.1.isSome)
                (push 4 (fun s => s.1.getD false) (goto (fun _ => .emitCopy)))
                (goto (fun _ => .reject)))))
          (goto (fun _ => .emitRestore)))
  | .emitRestore =>
      pop 6 (fun s mark => (mark, s.2))
        (branch (fun s => s.1.isSome)
          (push 1 (fun _ => true) (goto (fun _ => .emitRestore)))
          (goto (fun _ => .emitReverse)))
  | .emitReverse =>
      pop 4 (fun s bit => (bit, s.2))
        (branch (fun s => s.1.isSome)
          (push 5 (fun s => s.1.getD false) (goto (fun _ => .emitReverse)))
          (goto (fun _ => .acceptEmit)))
  | .acceptEmit => load (fun _ => (none, some .emit)) halt
  | .acceptTicket => load (fun _ => (none, some .ticket)) halt
  | .acceptBit => load (fun _ => (none, some .bit)) halt
  | .acceptAppend => load (fun _ => (none, some .append)) halt
  | .acceptBranch => load (fun _ => (none, some .branch3)) halt
  | .reject => load (fun _ => (none, none)) halt

def contents (input n a b work word used : List Bool) : Fin 7 → List Bool :=
  fun i => if i = 0 then input else if i = 1 then n else
    if i = 2 then a else if i = 3 then b else if i = 4 then work else
      if i = 5 then word else used

def cfg (label : Option Label) (control : Control)
    (input n a b work word used : List Bool) :
    TM2.Cfg (fun _ : Fin 7 => Bool) Label Control :=
  ⟨label, control, contents input n a b work word used⟩

def initial (input : List Bool) :=
  cfg (some .first) (none, none) input [] [] [] [] [] []

def run (steps : Nat) (c : TM2.Cfg (fun _ : Fin 7 => Bool) Label Control) :=
  ((advance program)^[steps]) c

private theorem run_succ {c d : TM2.Cfg (fun _ : Fin 7 => Bool) Label Control}
    (h : TM2.step program c = some d) (n : Nat) :
    run (n + 1) c = run n d := by
  simp only [run, Function.iterate_succ_apply, advance, h, Option.getD_some]

private theorem step_first_false (control : Control)
    (input n a b work word used : List Bool) :
    TM2.step program (cfg (some .first) control
      (false :: input) n a b work word used) =
      some (cfg (some .secondF) (some false, control.2)
        input n a b work word used) := by
  simp [TM2.step, TM2.stepAux, program, cfg, contents]
  funext i
  fin_cases i <;> rfl

private theorem step_secondF_true (control : Control)
    (input n a b work word used : List Bool) :
    TM2.step program (cfg (some .secondF) control
      (true :: input) n a b work word used) =
      some (cfg (some .thirdFT) (some true, control.2)
        input n a b work word used) := by
  simp [TM2.step, TM2.stepAux, program, cfg, contents]
  funext i
  fin_cases i <;> rfl

private theorem step_thirdFT_false (control : Control)
    (input n a b work word used : List Bool) :
    TM2.step program (cfg (some .thirdFT) control
      (false :: input) n a b work word used) =
      some (cfg (some .acceptBit) (some false, control.2)
        input n a b work word used) := by
  simp [TM2.step, TM2.stepAux, program, cfg, contents]
  funext i
  fin_cases i <;> rfl

theorem tag_bit (rest : List Bool) :
    run 3 (initial ([false, true, false] ++ rest)) =
      cfg (some .acceptBit) (some false, none) rest [] [] [] [] [] [] := by
  change run 3 (cfg (some .first) (none, none)
    (false :: true :: false :: rest) [] [] [] [] [] []) = _
  rw [show (3 : Nat) = (1 + 1) + 1 by omega,
    run_succ (step_first_false (none, none) _ _ _ _ _ _ _) ,
    run_succ (step_secondF_true (some false, none) _ _ _ _ _ _ _),
    run_succ (step_thirdFT_false (some true, none) _ _ _ _ _ _ _)]
  rfl

private theorem step_first_true (control : Control)
    (input n a b work word used : List Bool) :
    TM2.step program (cfg (some .first) control
      (true :: input) n a b work word used) =
      some (cfg (some .secondT) (some true, control.2)
        input n a b work word used) := by
  simp [TM2.step, TM2.stepAux, program, cfg, contents]
  funext i
  fin_cases i <;> rfl

private theorem step_secondF_false (control : Control)
    (input n a b work word used : List Bool) :
    TM2.step program (cfg (some .secondF) control
      (false :: input) n a b work word used) =
      some (cfg (some .thirdFF) (some false, control.2)
        input n a b work word used) := by
  simp [TM2.step, TM2.stepAux, program, cfg, contents]
  funext i
  fin_cases i <;> rfl

private theorem step_secondT_false (control : Control)
    (input n a b work word used : List Bool) :
    TM2.step program (cfg (some .secondT) control
      (false :: input) n a b work word used) =
      some (cfg (some .thirdTF) (some false, control.2)
        input n a b work word used) := by
  simp [TM2.step, TM2.stepAux, program, cfg, contents]
  funext i
  fin_cases i <;> rfl

private theorem step_thirdFF_false (control : Control)
    (input n a b work word used : List Bool) :
    TM2.step program (cfg (some .thirdFF) control
      (false :: input) n a b work word used) =
      some (cfg (some .unaryEmit) (some false, control.2)
        input n a b work word used) := by
  simp [TM2.step, TM2.stepAux, program, cfg, contents]
  funext i
  fin_cases i <;> rfl

private theorem step_thirdFF_true (control : Control)
    (input n a b work word used : List Bool) :
    TM2.step program (cfg (some .thirdFF) control
      (true :: input) n a b work word used) =
      some (cfg (some .unaryTicket) (some true, control.2)
        input n a b work word used) := by
  simp [TM2.step, TM2.stepAux, program, cfg, contents]
  funext i
  fin_cases i <;> rfl

private theorem step_thirdFT_true (control : Control)
    (input n a b work word used : List Bool) :
    TM2.step program (cfg (some .thirdFT) control
      (true :: input) n a b work word used) =
      some (cfg (some .acceptAppend) (some true, control.2)
        input n a b work word used) := by
  simp [TM2.step, TM2.stepAux, program, cfg, contents]
  funext i
  fin_cases i <;> rfl

private theorem step_thirdTF_false (control : Control)
    (input n a b work word used : List Bool) :
    TM2.step program (cfg (some .thirdTF) control
      (false :: input) n a b work word used) =
      some (cfg (some .unaryBranchN) (some false, control.2)
        input n a b work word used) := by
  simp [TM2.step, TM2.stepAux, program, cfg, contents]
  funext i
  fin_cases i <;> rfl



theorem tag_emit (rest : List Bool) :
    run 3 (initial ([false, false, false] ++ rest)) =
      cfg (some .unaryEmit) (some false, none) rest [] [] [] [] [] [] := by
  change run 3 (cfg (some .first) (none, none)
    (false :: false :: false :: rest) [] [] [] [] [] []) = _
  rw [show (3 : Nat) = (1 + 1) + 1 by omega,
    run_succ (step_first_false (none, none) _ _ _ _ _ _ _),
    run_succ (step_secondF_false (some false, none) _ _ _ _ _ _ _),
    run_succ (step_thirdFF_false (some false, none) _ _ _ _ _ _ _)]
  rfl

theorem tag_ticket (rest : List Bool) :
    run 3 (initial ([false, false, true] ++ rest)) =
      cfg (some .unaryTicket) (some true, none) rest [] [] [] [] [] [] := by
  change run 3 (cfg (some .first) (none, none)
    (false :: false :: true :: rest) [] [] [] [] [] []) = _
  rw [show (3 : Nat) = (1 + 1) + 1 by omega,
    run_succ (step_first_false (none, none) _ _ _ _ _ _ _),
    run_succ (step_secondF_false (some false, none) _ _ _ _ _ _ _),
    run_succ (step_thirdFF_true (some false, none) _ _ _ _ _ _ _)]
  rfl

theorem tag_append (rest : List Bool) :
    run 3 (initial ([false, true, true] ++ rest)) =
      cfg (some .acceptAppend) (some true, none) rest [] [] [] [] [] [] := by
  change run 3 (cfg (some .first) (none, none)
    (false :: true :: true :: rest) [] [] [] [] [] []) = _
  rw [show (3 : Nat) = (1 + 1) + 1 by omega,
    run_succ (step_first_false (none, none) _ _ _ _ _ _ _),
    run_succ (step_secondF_true (some false, none) _ _ _ _ _ _ _),
    run_succ (step_thirdFT_true (some true, none) _ _ _ _ _ _ _)]
  rfl

theorem tag_branch (rest : List Bool) :
    run 3 (initial ([true, false, false] ++ rest)) =
      cfg (some .unaryBranchN) (some false, none) rest [] [] [] [] [] [] := by
  change run 3 (cfg (some .first) (none, none)
    (true :: false :: false :: rest) [] [] [] [] [] []) = _
  rw [show (3 : Nat) = (1 + 1) + 1 by omega,
    run_succ (step_first_true (none, none) _ _ _ _ _ _ _),
    run_succ (step_secondT_false (some true, none) _ _ _ _ _ _ _),
    run_succ (step_thirdTF_false (some false, none) _ _ _ _ _ _ _)]
  rfl

private theorem run_add {c d : TM2.Cfg (fun _ : Fin 7 => Bool) Label Control}
    {m : Nat} (h : run m c = d) (n : Nat) : run (m + n) c = run n d := by
  rw [Nat.add_comm m n]
  simp only [run, Function.iterate_add_apply] at h ⊢
  rw [h]

private theorem true_comm (v : Nat) (tail : List Bool) :
    List.replicate v true ++ true :: tail =
      true :: (List.replicate v true ++ tail) := by
  induction v with
  | zero => rfl
  | succ v ih => simp [List.replicate_succ, ih]

private theorem step_ticket_true (control : Control)
    (input n a b work word used : List Bool) :
    TM2.step program (cfg (some .unaryTicket) control
      (true :: input) n a b work word used) =
      some (cfg (some .unaryTicket) (some true, control.2)
        input (true :: n) a b work word used) := by
  simp [TM2.step, TM2.stepAux, program, cfg, contents]
  funext i
  fin_cases i <;> rfl

private theorem step_ticket_false (control : Control)
    (input n a b work word used : List Bool) :
    TM2.step program (cfg (some .unaryTicket) control
      (false :: input) n a b work word used) =
      some (cfg (some .acceptTicket) (some false, control.2)
        input n a b work word used) := by
  simp [TM2.step, TM2.stepAux, program, cfg, contents]
  funext i
  fin_cases i <;> rfl

theorem run_ticket_unary (v : Nat) (rest n a b work word used : List Bool)
    (control : Control) :
    run (v + 1) (cfg (some .unaryTicket) control
      (List.replicate v true ++ false :: rest) n a b work word used) =
      cfg (some .acceptTicket) (some false, control.2)
        rest (List.replicate v true ++ n) a b work word used := by
  induction v generalizing n control with
  | zero =>
      simpa [run] using run_succ
        (step_ticket_false control rest n a b work word used) 0
  | succ v ih =>
      simp only [List.replicate_succ, List.cons_append]
      rw [run_succ (step_ticket_true control
        (List.replicate v true ++ false :: rest) n a b work word used) (v + 1)]
      simpa only [true_comm] using ih (true :: n) (some true, control.2)


private theorem step_emit_true (control : Control)
    (input n a b work word used : List Bool) :
    TM2.step program (cfg (some .unaryEmit) control
      (true :: input) n a b work word used) =
      some (cfg (some .unaryEmit) (some true, control.2)
        input (true :: n) a b work word used) := by
  simp [TM2.step, TM2.stepAux, program, cfg, contents]
  funext i
  fin_cases i <;> rfl

private theorem step_emit_false (control : Control)
    (input n a b work word used : List Bool) :
    TM2.step program (cfg (some .unaryEmit) control
      (false :: input) n a b work word used) =
      some (cfg (some .emitCopy) (some false, control.2)
        input n a b work word used) := by
  simp [TM2.step, TM2.stepAux, program, cfg, contents]
  funext i
  fin_cases i <;> rfl

theorem run_emit_unary (v : Nat) (rest n a b work word used : List Bool)
    (control : Control) :
    run (v + 1) (cfg (some .unaryEmit) control
      (List.replicate v true ++ false :: rest) n a b work word used) =
      cfg (some .emitCopy) (some false, control.2)
        rest (List.replicate v true ++ n) a b work word used := by
  induction v generalizing n control with
  | zero =>
      simpa [run] using run_succ
        (step_emit_false control rest n a b work word used) 0
  | succ v ih =>
      simp only [List.replicate_succ, List.cons_append]
      rw [run_succ (step_emit_true control
        (List.replicate v true ++ false :: rest) n a b work word used) (v + 1)]
      simpa only [true_comm] using ih (true :: n) (some true, control.2)

private theorem step_branchN_true (control : Control)
    (input n a b work word used : List Bool) :
    TM2.step program (cfg (some .unaryBranchN) control
      (true :: input) n a b work word used) =
      some (cfg (some .unaryBranchN) (some true, control.2)
        input (true :: n) a b work word used) := by
  simp [TM2.step, TM2.stepAux, program, cfg, contents]
  funext i
  fin_cases i <;> rfl

private theorem step_branchN_false (control : Control)
    (input n a b work word used : List Bool) :
    TM2.step program (cfg (some .unaryBranchN) control
      (false :: input) n a b work word used) =
      some (cfg (some .unaryBranchA) (some false, control.2)
        input n a b work word used) := by
  simp [TM2.step, TM2.stepAux, program, cfg, contents]
  funext i
  fin_cases i <;> rfl

theorem run_branchN_unary (v : Nat) (rest n a b work word used : List Bool)
    (control : Control) :
    run (v + 1) (cfg (some .unaryBranchN) control
      (List.replicate v true ++ false :: rest) n a b work word used) =
      cfg (some .unaryBranchA) (some false, control.2)
        rest (List.replicate v true ++ n) a b work word used := by
  induction v generalizing n control with
  | zero =>
      simpa [run] using run_succ
        (step_branchN_false control rest n a b work word used) 0
  | succ v ih =>
      simp only [List.replicate_succ, List.cons_append]
      rw [run_succ (step_branchN_true control
        (List.replicate v true ++ false :: rest) n a b work word used) (v + 1)]
      simpa only [true_comm] using ih (true :: n) (some true, control.2)

private theorem step_branchA_true (control : Control)
    (input n a b work word used : List Bool) :
    TM2.step program (cfg (some .unaryBranchA) control
      (true :: input) n a b work word used) =
      some (cfg (some .unaryBranchA) (some true, control.2)
        input n (true :: a) b work word used) := by
  simp [TM2.step, TM2.stepAux, program, cfg, contents]
  funext i
  fin_cases i <;> rfl

private theorem step_branchA_false (control : Control)
    (input n a b work word used : List Bool) :
    TM2.step program (cfg (some .unaryBranchA) control
      (false :: input) n a b work word used) =
      some (cfg (some .unaryBranchB) (some false, control.2)
        input n a b work word used) := by
  simp [TM2.step, TM2.stepAux, program, cfg, contents]
  funext i
  fin_cases i <;> rfl

theorem run_branchA_unary (v : Nat) (rest n a b work word used : List Bool)
    (control : Control) :
    run (v + 1) (cfg (some .unaryBranchA) control
      (List.replicate v true ++ false :: rest) n a b work word used) =
      cfg (some .unaryBranchB) (some false, control.2)
        rest n (List.replicate v true ++ a) b work word used := by
  induction v generalizing a control with
  | zero =>
      simpa [run] using run_succ
        (step_branchA_false control rest n a b work word used) 0
  | succ v ih =>
      simp only [List.replicate_succ, List.cons_append]
      rw [run_succ (step_branchA_true control
        (List.replicate v true ++ false :: rest) n a b work word used) (v + 1)]
      simpa only [true_comm] using ih (true :: a) (some true, control.2)

private theorem step_branchB_true (control : Control)
    (input n a b work word used : List Bool) :
    TM2.step program (cfg (some .unaryBranchB) control
      (true :: input) n a b work word used) =
      some (cfg (some .unaryBranchB) (some true, control.2)
        input n a (true :: b) work word used) := by
  simp [TM2.step, TM2.stepAux, program, cfg, contents]
  funext i
  fin_cases i <;> rfl

private theorem step_branchB_false (control : Control)
    (input n a b work word used : List Bool) :
    TM2.step program (cfg (some .unaryBranchB) control
      (false :: input) n a b work word used) =
      some (cfg (some .acceptBranch) (some false, control.2)
        input n a b work word used) := by
  simp [TM2.step, TM2.stepAux, program, cfg, contents]
  funext i
  fin_cases i <;> rfl

theorem run_branchB_unary (v : Nat) (rest n a b work word used : List Bool)
    (control : Control) :
    run (v + 1) (cfg (some .unaryBranchB) control
      (List.replicate v true ++ false :: rest) n a b work word used) =
      cfg (some .acceptBranch) (some false, control.2)
        rest n a (List.replicate v true ++ b) work word used := by
  induction v generalizing b control with
  | zero =>
      simpa [run] using run_succ
        (step_branchB_false control rest n a b work word used) 0
  | succ v ih =>
      simp only [List.replicate_succ, List.cons_append]
      rw [run_succ (step_branchB_true control
        (List.replicate v true ++ false :: rest) n a b work word used) (v + 1)]
      simpa only [true_comm] using ih (true :: b) (some true, control.2)


private theorem step_acceptEmit (control : Control)
    (input n a b work word used : List Bool) :
    TM2.step program (cfg (some .acceptEmit) control
      input n a b work word used) =
      some (cfg none (none, some .emit)
        input n a b work word used) := by
  simp [TM2.step, TM2.stepAux, program, cfg]

private theorem step_acceptTicket (control : Control)
    (input n a b work word used : List Bool) :
    TM2.step program (cfg (some .acceptTicket) control
      input n a b work word used) =
      some (cfg none (none, some .ticket)
        input n a b work word used) := by
  simp [TM2.step, TM2.stepAux, program, cfg]

private theorem step_acceptBit (control : Control)
    (input n a b work word used : List Bool) :
    TM2.step program (cfg (some .acceptBit) control
      input n a b work word used) =
      some (cfg none (none, some .bit)
        input n a b work word used) := by
  simp [TM2.step, TM2.stepAux, program, cfg]

private theorem step_acceptAppend (control : Control)
    (input n a b work word used : List Bool) :
    TM2.step program (cfg (some .acceptAppend) control
      input n a b work word used) =
      some (cfg none (none, some .append)
        input n a b work word used) := by
  simp [TM2.step, TM2.stepAux, program, cfg]

private theorem step_acceptBranch (control : Control)
    (input n a b work word used : List Bool) :
    TM2.step program (cfg (some .acceptBranch) control
      input n a b work word used) =
      some (cfg none (none, some .branch3)
        input n a b work word used) := by
  simp [TM2.step, TM2.stepAux, program, cfg]

theorem run_bit (rest : List Bool) :
    run 4 (initial (encodeCode .bit ++ rest)) =
      cfg none (none, some .bit) rest [] [] [] [] [] [] := by
  change run 4 (initial ([false, true, false] ++ rest)) = _
  rw [show (4 : Nat) = 3 + 1 by omega, run_add (tag_bit rest) 1,
    run_succ (step_acceptBit (some false, none) rest [] [] [] [] [] []) 0]
  rfl

theorem run_append (left right : Code) (rest : List Bool) :
    run 4 (initial (encodeCode (.append left right) ++ rest)) =
      cfg none (none, some .append)
        (encodeCode left ++ encodeCode right ++ rest) [] [] [] [] [] [] := by
  change run 4 (initial ([false, true, true] ++
    (encodeCode left ++ encodeCode right ++ rest))) = _
  rw [show (4 : Nat) = 3 + 1 by omega,
    run_add (tag_append (encodeCode left ++ encodeCode right ++ rest)) 1,
    run_succ (step_acceptAppend (some true, none) _ _ _ _ _ _ _) 0]
  rfl

theorem run_ticket (n : Nat) (rest : List Bool) :
    run (n + 5) (initial (encodeCode (.ticket n) ++ rest)) =
      cfg none (none, some .ticket) rest (List.replicate n true) [] [] [] [] [] := by
  suffices h : run (n + 5) (initial ([false, false, true] ++
      (List.replicate n true ++ false :: rest))) =
      cfg none (none, some .ticket) rest (List.replicate n true) [] [] [] [] [] by
    simpa [encodeCode, unary, List.append_assoc] using h
  rw [show n + 5 = 3 + ((n + 1) + 1) by omega,
    run_add (tag_ticket (List.replicate n true ++ false :: rest)) ((n + 1) + 1),
    run_add (run_ticket_unary n rest [] [] [] [] [] [] (some true, none)) 1,
    run_succ (step_acceptTicket (some false, none) _ _ _ _ _ _ _) 0]
  simp [run]

theorem run_branch3 (n a b : Nat) (first second third : Code)
    (rest : List Bool) :
    run (n + a + b + 7)
      (initial (encodeCode (.branch3 n a b first second third) ++ rest)) =
      cfg none (none, some .branch3)
        (encodeCode first ++ encodeCode second ++ encodeCode third ++ rest)
        (List.replicate n true) (List.replicate a true)
        (List.replicate b true) [] [] [] := by
  let tail := encodeCode first ++ encodeCode second ++ encodeCode third ++ rest
  suffices h : run (n + a + b + 7) (initial ([true, false, false] ++
      (List.replicate n true ++ false ::
        (List.replicate a true ++ false ::
          (List.replicate b true ++ false :: tail))))) =
      cfg none (none, some .branch3) tail
        (List.replicate n true) (List.replicate a true)
        (List.replicate b true) [] [] [] by
    simpa [tail, encodeCode, unary, List.append_assoc] using h
  rw [show n + a + b + 7 =
      3 + ((n + 1) + ((a + 1) + ((b + 1) + 1))) by omega,
    run_add (tag_branch _) _,
    run_add (run_branchN_unary n _ [] [] [] [] [] [] (some false, none)) _,
    run_add (run_branchA_unary a _ (List.replicate n true ++ [])
      [] [] [] [] [] (some false, none)) _,
    run_add (run_branchB_unary b _ (List.replicate n true ++ [])
      (List.replicate a true ++ []) [] [] [] [] (some false, none)) _,
    run_succ (step_acceptBranch (some false, none) _ _ _ _ _ _ _) 0]
  simp [run]

private theorem step_emitCopy_cons (control : Control) (bit : Bool)
    (input count a b work word used : List Bool) :
    TM2.step program (cfg (some .emitCopy) control
      (bit :: input) (true :: count) a b work word used) =
      some (cfg (some .emitCopy) (some bit, control.2)
        input count a b (bit :: work) word (true :: used)) := by
  simp [TM2.step, TM2.stepAux, program, cfg, contents]
  funext i
  fin_cases i <;> rfl

private theorem step_emitCopy_done (control : Control)
    (input a b work word used : List Bool) :
    TM2.step program (cfg (some .emitCopy) control
      input [] a b work word used) =
      some (cfg (some .emitRestore) (none, control.2)
        input [] a b work word used) := by
  simp [TM2.step, TM2.stepAux, program, cfg, contents]

private theorem step_emitRestore_cons (control : Control)
    (input n a b work word used : List Bool) :
    TM2.step program (cfg (some .emitRestore) control
      input n a b work word (true :: used)) =
      some (cfg (some .emitRestore) (some true, control.2)
        input (true :: n) a b work word used) := by
  simp [TM2.step, TM2.stepAux, program, cfg, contents]
  funext i
  fin_cases i <;> rfl

private theorem step_emitRestore_done (control : Control)
    (input n a b work word : List Bool) :
    TM2.step program (cfg (some .emitRestore) control
      input n a b work word []) =
      some (cfg (some .emitReverse) (none, control.2)
        input n a b work word []) := by
  simp [TM2.step, TM2.stepAux, program, cfg, contents]

private theorem step_emitReverse_cons (control : Control) (bit : Bool)
    (input n a b work word used : List Bool) :
    TM2.step program (cfg (some .emitReverse) control
      input n a b (bit :: work) word used) =
      some (cfg (some .emitReverse) (some bit, control.2)
        input n a b work (bit :: word) used) := by
  simp [TM2.step, TM2.stepAux, program, cfg, contents]
  funext i
  fin_cases i <;> rfl

private theorem step_emitReverse_done (control : Control)
    (input n a b word used : List Bool) :
    TM2.step program (cfg (some .emitReverse) control
      input n a b [] word used) =
      some (cfg (some .acceptEmit) (none, control.2)
        input n a b [] word used) := by
  simp [TM2.step, TM2.stepAux, program, cfg, contents]

theorem run_emitCopy_prefix (bits rest a b work word used : List Bool)
    (control : Control) :
    ∃ next : Control,
      run bits.length (cfg (some .emitCopy) control
        (bits ++ rest) (List.replicate bits.length true) a b work word used) =
      cfg (some .emitCopy) next rest [] a b
        (bits.reverse ++ work) word
        (List.replicate bits.length true ++ used) := by
  induction bits generalizing work used control with
  | nil => exact ⟨control, by simp [run]⟩
  | cons bit bits ih =>
      obtain ⟨next, h⟩ := ih (bit :: work) (true :: used)
        (some bit, control.2)
      refine ⟨next, ?_⟩
      simp only [List.length_cons, List.replicate_succ, List.cons_append]
      rw [run_succ (step_emitCopy_cons control bit
        (bits ++ rest) (List.replicate bits.length true) a b work word used)
        bits.length, h]
      simp [List.reverse_cons, List.append_assoc, true_comm]

theorem run_emitRestore_prefix (v : Nat) (control : Control)
    (input n a b work word used : List Bool) :
    ∃ next : Control,
      run v (cfg (some .emitRestore) control
        input n a b work word (List.replicate v true ++ used)) =
      cfg (some .emitRestore) next input
        (List.replicate v true ++ n) a b work word used := by
  induction v generalizing n control with
  | zero => exact ⟨control, by simp [run]⟩
  | succ v ih =>
      obtain ⟨next, h⟩ := ih (some true, control.2) (true :: n)
      refine ⟨next, ?_⟩
      simp only [List.replicate_succ, List.cons_append]
      rw [run_succ (step_emitRestore_cons control input n a b work word
        (List.replicate v true ++ used)) v, h]
      simp only [true_comm]

theorem run_emitReverse_prefix (bits : List Bool) (control : Control)
    (input n a b word used : List Bool) :
    ∃ next : Control,
      run bits.length (cfg (some .emitReverse) control
        input n a b bits word used) =
      cfg (some .emitReverse) next input n a b []
        (bits.reverse ++ word) used := by
  induction bits generalizing word control with
  | nil => exact ⟨control, by simp [run]⟩
  | cons bit bits ih =>
      obtain ⟨next, h⟩ := ih (some bit, control.2) (bit :: word)
      refine ⟨next, ?_⟩
      simp only [List.length_cons]
      rw [run_succ (step_emitReverse_cons control bit input n a b bits word used)
        bits.length, h]
      simp [List.reverse_cons, List.append_assoc]

theorem run_emit (bits rest : List Bool) :
    run (4 * bits.length + 8) (initial (encodeCode (.emit bits) ++ rest)) =
      cfg none (none, some .emit) rest (List.replicate bits.length true)
        [] [] [] bits [] := by
  let m := bits.length
  have h1 : run (3 + (m + 1))
      (initial ([false, false, false] ++
        (List.replicate m true ++ false :: (bits ++ rest)))) =
      cfg (some .emitCopy) (some false, none) (bits ++ rest)
        (List.replicate m true) [] [] [] [] [] := by
    rw [run_add (tag_emit _) (m + 1)]
    simpa [m] using
      run_emit_unary m (bits ++ rest) [] [] [] [] [] [] (some false, none)
  obtain ⟨afterCopy, hc⟩ :=
    run_emitCopy_prefix bits rest [] [] [] [] [] (some false, none)
  have h2 : run (3 + (m + 1) + m)
      (initial ([false, false, false] ++
        (List.replicate m true ++ false :: (bits ++ rest)))) =
      cfg (some .emitCopy) afterCopy rest [] [] [] bits.reverse []
        (List.replicate m true) := by
    rw [run_add h1 m]
    simpa [m] using hc
  have h3 : run (3 + (m + 1) + m + 1)
      (initial ([false, false, false] ++
        (List.replicate m true ++ false :: (bits ++ rest)))) =
      cfg (some .emitRestore) (none, afterCopy.2) rest [] [] [] bits.reverse []
        (List.replicate m true) := by
    rw [run_add h2 1, run_succ
      (step_emitCopy_done afterCopy rest [] [] bits.reverse []
        (List.replicate m true)) 0]
    rfl
  obtain ⟨afterRestore, hr⟩ :=
    run_emitRestore_prefix m (none, afterCopy.2) rest [] [] [] bits.reverse [] []
  have h4 : run (3 + (m + 1) + m + 1 + m)
      (initial ([false, false, false] ++
        (List.replicate m true ++ false :: (bits ++ rest)))) =
      cfg (some .emitRestore) afterRestore rest
        (List.replicate m true) [] [] bits.reverse [] [] := by
    rw [run_add h3 m]
    simpa [m] using hr
  have h5 : run (3 + (m + 1) + m + 1 + m + 1)
      (initial ([false, false, false] ++
        (List.replicate m true ++ false :: (bits ++ rest)))) =
      cfg (some .emitReverse) (none, afterRestore.2) rest
        (List.replicate m true) [] [] bits.reverse [] [] := by
    rw [run_add h4 1, run_succ
      (step_emitRestore_done afterRestore rest (List.replicate m true)
        [] [] bits.reverse []) 0]
    rfl
  obtain ⟨afterReverse, hv⟩ :=
    run_emitReverse_prefix bits.reverse (none, afterRestore.2) rest
      (List.replicate m true) [] [] [] []
  have h6 : run (3 + (m + 1) + m + 1 + m + 1 + m)
      (initial ([false, false, false] ++
        (List.replicate m true ++ false :: (bits ++ rest)))) =
      cfg (some .emitReverse) afterReverse rest
        (List.replicate m true) [] [] [] bits [] := by
    rw [run_add h5 m]
    simpa [m] using hv
  have h7 : run (3 + (m + 1) + m + 1 + m + 1 + m + 1)
      (initial ([false, false, false] ++
        (List.replicate m true ++ false :: (bits ++ rest)))) =
      cfg (some .acceptEmit) (none, afterReverse.2) rest
        (List.replicate m true) [] [] [] bits [] := by
    rw [run_add h6 1, run_succ
      (step_emitReverse_done afterReverse rest (List.replicate m true)
        [] [] bits []) 0]
    rfl
  have h8 : run (3 + (m + 1) + m + 1 + m + 1 + m + 1 + 1)
      (initial ([false, false, false] ++
        (List.replicate m true ++ false :: (bits ++ rest)))) =
      cfg none (none, some .emit) rest (List.replicate m true)
        [] [] [] bits [] := by
    rw [run_add h7 1, run_succ
      (step_acceptEmit (none, afterReverse.2) rest
        (List.replicate m true) [] [] [] bits []) 0]
    rfl
  have htime : 4 * bits.length + 8 =
      3 + (m + 1) + m + 1 + m + 1 + m + 1 + 1 := by
    simp [m]; omega
  rw [htime]
  simpa [m, encodeCode, unary, List.append_assoc] using h8

/-- A constructor's children remain as consecutive unread code words. -/
def headerTail : Code → List Bool → List Bool
  | .emit _, rest | .ticket _, rest | .bit, rest => rest
  | .append left right, rest => encodeCode left ++ encodeCode right ++ rest
  | .branch3 _ _ _ first second third, rest =>
      encodeCode first ++ encodeCode second ++ encodeCode third ++ rest

def headerKind : Code → Kind
  | .emit _ => .emit
  | .ticket _ => .ticket
  | .bit => .bit
  | .append _ _ => .append
  | .branch3 _ _ _ _ _ _ => .branch3

def headerN : Code → List Bool
  | .emit bits => List.replicate bits.length true
  | .ticket n => List.replicate n true
  | .bit | .append _ _ => []
  | .branch3 n _ _ _ _ _ => List.replicate n true

def headerA : Code → List Bool
  | .branch3 _ a _ _ _ _ => List.replicate a true
  | _ => []

def headerB : Code → List Bool
  | .branch3 _ _ b _ _ _ => List.replicate b true
  | _ => []

def headerWord : Code → List Bool
  | .emit bits => bits
  | _ => []

def headerCost : Code → Nat
  | .emit bits => 4 * bits.length + 8
  | .ticket n => n + 5
  | .bit | .append _ _ => 4
  | .branch3 n a b _ _ _ => n + a + b + 7

/-- Physical header extraction for every source-syntax constructor. The
machine has fixed finite control, and each equality specifies all seven
physical stacks after exactly `headerCost c` TM2 transitions. -/
theorem run_header (c : Code) (rest : List Bool) :
    run (headerCost c) (initial (encodeCode c ++ rest)) =
      cfg none (none, some (headerKind c)) (headerTail c rest)
        (headerN c) (headerA c) (headerB c) [] (headerWord c) [] := by
  cases c with
  | emit bits => simpa [headerCost, headerKind, headerTail, headerN,
      headerA, headerB, headerWord] using run_emit bits rest
  | ticket n => simpa [headerCost, headerKind, headerTail, headerN,
      headerA, headerB, headerWord] using run_ticket n rest
  | bit => simpa [headerCost, headerKind, headerTail, headerN,
      headerA, headerB, headerWord] using run_bit rest
  | append left right => simpa [headerCost, headerKind, headerTail, headerN,
      headerA, headerB, headerWord] using run_append left right rest
  | branch3 n a b first second third =>
      simpa [headerCost, headerKind, headerTail, headerN,
        headerA, headerB, headerWord] using
        run_branch3 n a b first second third rest

theorem run_ticket_zero (rest : List Bool) :
    run 5 (initial (encodeCode (.ticket 0) ++ rest)) =
      cfg none (none, some .ticket) rest [] [] [] [] [] [] := by
  simpa using run_ticket 0 rest

private theorem step_first_empty :
    TM2.step program (initial []) =
      some (cfg (some .reject) (none, none) [] [] [] [] [] [] []) := by
  simp [initial, TM2.step, TM2.stepAux, program, cfg, contents]

private theorem step_reject (control : Control)
    (input n a b work word used : List Bool) :
    TM2.step program (cfg (some .reject) control
      input n a b work word used) =
      some (cfg none (none, none) input n a b work word used) := by
  simp [TM2.step, TM2.stepAux, program, cfg]

/-- An empty (truncated) header is rejected after two charged transitions. -/
theorem run_empty_reject :
    run 2 (initial []) = cfg none (none, none) [] [] [] [] [] [] [] := by
  rw [show (2 : Nat) = 1 + 1 by omega,
    run_succ step_first_empty 1,
    run_succ (step_reject (none, none) [] [] [] [] [] [] []) 0]
  rfl

#print axioms run_bit
#print axioms run_append
#print axioms run_ticket
#print axioms run_branch3
#print axioms run_emit
#print axioms run_header
#print axioms run_ticket_zero
#print axioms run_empty_reject

end Paper2.CodeHeaderMachine
