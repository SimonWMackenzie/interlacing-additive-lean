import EthInapproximability.CurrentPaper.ProtocolBinaryHeader
import EthInapproximability.CurrentPaper.ProtocolBoundedUnary
import EthInapproximability.CurrentPaper.BitMachineSubroutine
import EthInapproximability.CurrentPaper.EncodedCNF

/-! A finite inlinable evaluator for one canonical literal. The caller has
already validated syntax and the assignment length. This module consumes the
literal's sign and self-delimiting binary index, preserves every assignment
bit and the unused source suffix, and clears all local scratch stacks. -/

namespace CurrentAdditive.V39CNFLiteral

set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

open Turing TM2.Stmt
open EthInapproximability.CurrentPaper
open BitMachineEncoding BitMachineComposition BitMachineSubroutine


inductive Foreign where | source | assignment | output | saved
  deriving DecidableEq, Fintype
abbrev Stack := Fin 4 ⊕ Foreign
namespace Stack
def source : Stack := .inr .source
def assignment : Stack := .inr .assignment
def output : Stack := .inr .output
def saved : Stack := .inr .saved
def binary : Stack := .inl 0
def budget : Stack := .inl 1
def work : Stack := .inl 2
def index : Stack := .inl 3
end Stack

inductive Outer where
  | start | copyAssignment | restoreAssignment | scan | payload
  | restoreHeader | afterUnary | clearBinary | clearBudget | lookup
  | restoreLookup | finish
  deriving DecidableEq, Fintype
abbrev Label := ProtocolBoundedUnary.Label ⊕ Outer
structure Register where
  sign : Bool
  popped : Option Bool
  answer : Bool
  deriving DecidableEq, Fintype
abbrev Control := ProtocolBoundedUnary.Control × Register
def initial : Control := ((none, false), ⟨false, none, false⟩)
def start : Label := .inr .start
def remembered (s : Control) (b : Option Bool) : Control :=
  (s.1, {s.2 with popped := b})
def again (l : Outer) : TM2.Stmt (fun _ : Stack => Bool) Label Control :=
  goto (fun _ => .inr l)

def program : Label → TM2.Stmt (fun _ : Stack => Bool) Label Control
  | .inl l => liftStmt (some Outer.afterUnary) (ProtocolBoundedUnary.program l)
  | .inr .start => pop Stack.source (fun _ b =>
      ((none, false), ⟨b.getD false, none, false⟩)) (again .copyAssignment)
  | .inr .copyAssignment =>
      pop Stack.assignment remembered
        (branch (fun s => s.2.popped.isSome)
          (push Stack.saved (fun s => s.2.popped.getD false)
            (push Stack.budget (fun s => s.2.popped.getD false) (again .copyAssignment)))
          (again .restoreAssignment))
  | .inr .restoreAssignment =>
      pop Stack.saved remembered
        (branch (fun s => s.2.popped.isSome)
          (push Stack.assignment (fun s => s.2.popped.getD false) (again .restoreAssignment))
          (again .scan))
  | .inr .scan => pop Stack.source remembered
      (branch (fun s => s.2.popped.getD false) (again .payload) (again .restoreHeader))
  | .inr .payload => pop Stack.source remembered
      (push Stack.work (fun s => s.2.popped.getD false) (again .scan))
  | .inr .restoreHeader => pop Stack.work remembered
      (branch (fun s => s.2.popped.isSome)
        (push Stack.binary (fun s => s.2.popped.getD false) (again .restoreHeader))
        (load (fun s => ((none, false), {s.2 with popped := none}))
          (goto (fun _ => .inl .zeroScan))))
  | .inr .afterUnary => pop Stack.index remembered (again .clearBinary)
  | .inr .clearBinary => pop Stack.binary remembered
      (branch (fun s => s.2.popped.isSome) (again .clearBinary) (again .clearBudget))
  | .inr .clearBudget => pop Stack.budget remembered
      (branch (fun s => s.2.popped.isSome) (again .clearBudget) (again .lookup))
  | .inr .lookup => pop Stack.index remembered
      (branch (fun s => s.2.popped.isSome)
        (pop Stack.assignment remembered
          (push Stack.saved (fun s => s.2.popped.getD false) (again .lookup)))
        (peek Stack.assignment (fun s b =>
          (s.1, {s.2 with answer := b.getD false, popped := none})) (again .restoreLookup)))
  | .inr .restoreLookup => pop Stack.saved remembered
      (branch (fun s => s.2.popped.isSome)
        (push Stack.assignment (fun s => s.2.popped.getD false) (again .restoreLookup))
        (again .finish))
  | .inr .finish => push Stack.output
      (fun s => if s.2.sign then s.2.answer else !s.2.answer)
      (load (fun _ => initial) halt)

def bank (binary budget work index source assignment output saved : List Bool) :
    Stack → List Bool :=
  Sum.elim (ProtocolBoundedUnary.stackContents binary budget work index)
    (fun | .source => source | .assignment => assignment
         | .output => output | .saved => saved)
def ready (source assignment : List Bool) : Stack → List Bool :=
  bank [] [] [] [] source assignment [] []
def resultBank (source assignment : List Bool) (bit : Bool) : Stack → List Bool :=
  Function.update (ready source assignment) Stack.output [bit]
def cfg (label : Option Label) (s : Control)
    (binary budget work index source assignment output saved : List Bool) :
    TM2.Cfg (fun _ : Stack => Bool) Label Control :=
  ⟨label, s, bank binary budget work index source assignment output saved⟩
def run (n : ℕ) (c : TM2.Cfg (fun _ : Stack => Bool) Label Control) :=
  ((advance program)^[n]) c

@[simp] theorem ready_source (s a : List Bool) : ready s a Stack.source = s := rfl
@[simp] theorem ready_assignment (s a : List Bool) : ready s a Stack.assignment = a := rfl
@[simp] theorem ready_output (s a : List Bool) : ready s a Stack.output = [] := rfl
@[simp] theorem resultBank_source (s a : List Bool) (b : Bool) :
    resultBank s a b Stack.source = s := by simp [resultBank, Stack.source, Stack.output, ready, bank]
@[simp] theorem resultBank_assignment (s a : List Bool) (b : Bool) :
    resultBank s a b Stack.assignment = a := by simp [resultBank, Stack.assignment, Stack.output, ready, bank]
@[simp] theorem resultBank_output (s a : List Bool) (b : Bool) :
    resultBank s a b Stack.output = [b] := by simp [resultBank]

theorem run_succ (n : ℕ) (c : TM2.Cfg (fun _ : Stack => Bool) Label Control) :
    run (n + 1) c = run n (advance program c) :=
  Function.iterate_succ_apply _ _ _
theorem run_add {c d : TM2.Cfg (fun _ : Stack => Bool) Label Control}
    {m : ℕ} (h : run m c = d) (n : ℕ) : run (m + n) c = run n d := by
  rw [Nat.add_comm m n]
  simp only [run, Function.iterate_add_apply] at h ⊢
  rw [h]

macro "bank_ext" : tactic => `(tactic|
  (first | rfl | (congr 1; funext k; cases k with
    | inl k => fin_cases k <;> rfl
    | inr k => cases k <;> rfl)))

theorem start_step (sign : Bool) (source a : List Bool) :
    advance program ⟨some start, initial, ready (sign :: source) a⟩ =
      cfg (some (.inr .copyAssignment)) ((none,false),⟨sign,none,false⟩)
        [] [] [] [] source a [] [] := by
  simp only [Bool.false_eq_true, Bool.true_eq_false, eq_self, show (0:Fin 4) ≠ 1 by decide, show (0:Fin 4) ≠ 2 by decide, show (0:Fin 4) ≠ 3 by decide, show (1:Fin 4) ≠ 0 by decide, show (1:Fin 4) ≠ 2 by decide, show (1:Fin 4) ≠ 3 by decide, show (2:Fin 4) ≠ 0 by decide, show (2:Fin 4) ≠ 1 by decide, show (2:Fin 4) ≠ 3 by decide, show (3:Fin 4) ≠ 0 by decide, show (3:Fin 4) ≠ 1 by decide, show (3:Fin 4) ≠ 2 by decide, Function.update_apply, Sum.inr_ne_inl, Sum.inl_ne_inr, Stack.source, Stack.assignment, Stack.saved, Stack.output, Stack.binary, Stack.budget, Stack.work, Stack.index, ↓reduceIte, Bool.cond_true, Bool.cond_false, advance, TM2.step, TM2.stepAux, program, Option.getD_some, Sum.elim_inr, List.head?_cons, List.tail_cons, List.head?_nil, List.tail_nil, Option.isSome_some, Option.isSome_none, Option.getD_none, Bool.cond_true, Bool.cond_false, Bool.false_eq_true, ite_true, ite_false, start, initial, ready,
    cfg, bank, Stack.source, again]
  all_goals bank_ext

theorem copy_step (u : ProtocolBoundedUnary.Control) (r : Register)
    (b : Bool) (a cap saved source : List Bool) :
    advance program (cfg (some (.inr .copyAssignment)) (u,r)
      [] cap [] [] source (b::a) [] saved) =
    cfg (some (.inr .copyAssignment)) (u,{r with popped:=some b})
      [] (b::cap) [] [] source a [] (b::saved) := by
  simp only [Bool.false_eq_true, Bool.true_eq_false, eq_self, show (0:Fin 4) ≠ 1 by decide, show (0:Fin 4) ≠ 2 by decide, show (0:Fin 4) ≠ 3 by decide, show (1:Fin 4) ≠ 0 by decide, show (1:Fin 4) ≠ 2 by decide, show (1:Fin 4) ≠ 3 by decide, show (2:Fin 4) ≠ 0 by decide, show (2:Fin 4) ≠ 1 by decide, show (2:Fin 4) ≠ 3 by decide, show (3:Fin 4) ≠ 0 by decide, show (3:Fin 4) ≠ 1 by decide, show (3:Fin 4) ≠ 2 by decide, Function.update_apply, Sum.inr_ne_inl, Sum.inl_ne_inr, Stack.source, Stack.assignment, Stack.saved, Stack.output, Stack.binary, Stack.budget, Stack.work, Stack.index, ↓reduceIte, Bool.cond_true, Bool.cond_false, advance, TM2.step, TM2.stepAux, program, Option.getD_some, Sum.elim_inr, List.head?_cons, List.tail_cons, List.head?_nil, List.tail_nil, Option.isSome_some, Option.isSome_none, Option.getD_none, Bool.cond_true, Bool.cond_false, Bool.false_eq_true, ite_true, ite_false, cfg, bank, remembered,
    Stack.assignment, Stack.saved, Stack.budget, again]
  all_goals bank_ext
theorem copy_nil (u : ProtocolBoundedUnary.Control) (r : Register)
    (cap saved source : List Bool) :
    advance program (cfg (some (.inr .copyAssignment)) (u,r)
      [] cap [] [] source [] [] saved) =
    cfg (some (.inr .restoreAssignment)) (u,{r with popped:=none})
      [] cap [] [] source [] [] saved := by
  simp only [Bool.false_eq_true, Bool.true_eq_false, eq_self, show (0:Fin 4) ≠ 1 by decide, show (0:Fin 4) ≠ 2 by decide, show (0:Fin 4) ≠ 3 by decide, show (1:Fin 4) ≠ 0 by decide, show (1:Fin 4) ≠ 2 by decide, show (1:Fin 4) ≠ 3 by decide, show (2:Fin 4) ≠ 0 by decide, show (2:Fin 4) ≠ 1 by decide, show (2:Fin 4) ≠ 3 by decide, show (3:Fin 4) ≠ 0 by decide, show (3:Fin 4) ≠ 1 by decide, show (3:Fin 4) ≠ 2 by decide, Function.update_apply, Sum.inr_ne_inl, Sum.inl_ne_inr, Stack.source, Stack.assignment, Stack.saved, Stack.output, Stack.binary, Stack.budget, Stack.work, Stack.index, ↓reduceIte, Bool.cond_true, Bool.cond_false, advance, TM2.step, TM2.stepAux, program, Option.getD_some, Sum.elim_inr, List.head?_cons, List.tail_cons, List.head?_nil, List.tail_nil, Option.isSome_some, Option.isSome_none, Option.getD_none, Bool.cond_true, Bool.cond_false, Bool.false_eq_true, ite_true, ite_false, cfg, bank, remembered,
    Stack.assignment, again]
  all_goals bank_ext
theorem copy_run (u : ProtocolBoundedUnary.Control) (r : Register)
    (a cap saved source : List Bool) :
    run (a.length+1) (cfg (some (.inr .copyAssignment)) (u,r)
      [] cap [] [] source a [] saved) =
    cfg (some (.inr .restoreAssignment)) (u,{r with popped:=none})
      [] (a.reverse++cap) [] [] source [] [] (a.reverse++saved) := by
  induction a generalizing cap saved r with
  | nil => simp [run, copy_nil]
  | cons b a ih =>
      rw [List.length_cons, run_succ, copy_step, ih]
      simp [List.reverse_cons, List.append_assoc]

theorem restore_step (which : Bool) (u : ProtocolBoundedUnary.Control) (r : Register)
    (binary budget index source assignment output saved : List Bool) (b : Bool) :
    advance program (cfg (some (.inr (if which then .restoreLookup else .restoreAssignment)))
      (u,r) binary budget [] index source assignment output (b::saved)) =
    cfg (some (.inr (if which then .restoreLookup else .restoreAssignment)))
      (u,{r with popped:=some b}) binary budget [] index source (b::assignment) output saved := by
  cases which <;>
    simp only [Bool.false_eq_true, Bool.true_eq_false, eq_self, show (0:Fin 4) ≠ 1 by decide, show (0:Fin 4) ≠ 2 by decide, show (0:Fin 4) ≠ 3 by decide, show (1:Fin 4) ≠ 0 by decide, show (1:Fin 4) ≠ 2 by decide, show (1:Fin 4) ≠ 3 by decide, show (2:Fin 4) ≠ 0 by decide, show (2:Fin 4) ≠ 1 by decide, show (2:Fin 4) ≠ 3 by decide, show (3:Fin 4) ≠ 0 by decide, show (3:Fin 4) ≠ 1 by decide, show (3:Fin 4) ≠ 2 by decide, Function.update_apply, Sum.inr_ne_inl, Sum.inl_ne_inr, Stack.source, Stack.assignment, Stack.saved, Stack.output, Stack.binary, Stack.budget, Stack.work, Stack.index, ↓reduceIte, Bool.cond_true, Bool.cond_false, advance, TM2.step, TM2.stepAux, program, Option.getD_some, Sum.elim_inr, List.head?_cons, List.tail_cons, List.head?_nil, List.tail_nil, Option.isSome_some, Option.isSome_none, Option.getD_none, Bool.cond_true, Bool.cond_false, Bool.false_eq_true, ite_true, ite_false, cfg, bank, remembered,
      Stack.assignment, Stack.saved, again] <;> bank_ext
theorem restore_nil (which : Bool) (u : ProtocolBoundedUnary.Control) (r : Register)
    (binary budget index source assignment output : List Bool) :
    advance program (cfg (some (.inr (if which then .restoreLookup else .restoreAssignment)))
      (u,r) binary budget [] index source assignment output []) =
    cfg (some (.inr (if which then .finish else .scan)))
      (u,{r with popped:=none}) binary budget [] index source assignment output [] := by
  cases which <;>
    simp only [Bool.false_eq_true, Bool.true_eq_false, eq_self, show (0:Fin 4) ≠ 1 by decide, show (0:Fin 4) ≠ 2 by decide, show (0:Fin 4) ≠ 3 by decide, show (1:Fin 4) ≠ 0 by decide, show (1:Fin 4) ≠ 2 by decide, show (1:Fin 4) ≠ 3 by decide, show (2:Fin 4) ≠ 0 by decide, show (2:Fin 4) ≠ 1 by decide, show (2:Fin 4) ≠ 3 by decide, show (3:Fin 4) ≠ 0 by decide, show (3:Fin 4) ≠ 1 by decide, show (3:Fin 4) ≠ 2 by decide, Function.update_apply, Sum.inr_ne_inl, Sum.inl_ne_inr, Stack.source, Stack.assignment, Stack.saved, Stack.output, Stack.binary, Stack.budget, Stack.work, Stack.index, ↓reduceIte, Bool.cond_true, Bool.cond_false, advance, TM2.step, TM2.stepAux, program, Option.getD_some, Sum.elim_inr, List.head?_cons, List.tail_cons, List.head?_nil, List.tail_nil, Option.isSome_some, Option.isSome_none, Option.getD_none, Bool.cond_true, Bool.cond_false, Bool.false_eq_true, ite_true, ite_false, cfg, bank, remembered,
      Stack.saved, again] <;> bank_ext
theorem restore_run (which : Bool) (u : ProtocolBoundedUnary.Control) (r : Register)
    (binary budget index source assignment output saved : List Bool) :
    run (saved.length+1)
      (cfg (some (.inr (if which then .restoreLookup else .restoreAssignment)))
        (u,r) binary budget [] index source assignment output saved) =
    cfg (some (.inr (if which then .finish else .scan)))
      (u,{r with popped:=none}) binary budget [] index source
      (saved.reverse++assignment) output [] := by
  induction saved generalizing r assignment with
  | nil => simp [run, restore_nil]
  | cons b saved ih =>
      rw [List.length_cons, run_succ, restore_step, ih]
      simp [List.reverse_cons, List.append_assoc]

theorem prepared_assignment (sign : Bool) (source a : List Bool) :
    run (2*a.length+3) ⟨some start, initial, ready (sign::source) a⟩ =
    cfg (some (.inr .scan)) ((none,false),⟨sign,none,false⟩)
      [] a.reverse [] [] source a [] [] := by
  have hc := copy_run (none,false) ⟨sign,none,false⟩ a [] [] source
  have hr := restore_run false (none,false) ⟨sign,none,false⟩
    [] a.reverse [] source [] [] a.reverse
  simp only [List.append_nil, List.length_reverse, List.reverse_reverse] at hc hr
  have hs : run 1 ⟨some start, initial, ready (sign::source) a⟩ = _ := start_step sign source a
  simpa [Nat.mul_two, Nat.two_mul, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    ((run_add hs (a.length+1)).trans hc |> fun h => (run_add h (a.length+1)).trans hr)

theorem scan_true (u : ProtocolBoundedUnary.Control) (r : Register)
    (source budget work a : List Bool) :
    advance program (cfg (some (.inr .scan)) (u,r)
      [] budget work [] (true::source) a [] []) =
    cfg (some (.inr .payload)) (u,{r with popped:=some true})
      [] budget work [] source a [] [] := by
  simp only [Bool.false_eq_true, Bool.true_eq_false, eq_self, show (0:Fin 4) ≠ 1 by decide, show (0:Fin 4) ≠ 2 by decide, show (0:Fin 4) ≠ 3 by decide, show (1:Fin 4) ≠ 0 by decide, show (1:Fin 4) ≠ 2 by decide, show (1:Fin 4) ≠ 3 by decide, show (2:Fin 4) ≠ 0 by decide, show (2:Fin 4) ≠ 1 by decide, show (2:Fin 4) ≠ 3 by decide, show (3:Fin 4) ≠ 0 by decide, show (3:Fin 4) ≠ 1 by decide, show (3:Fin 4) ≠ 2 by decide, Function.update_apply, Sum.inr_ne_inl, Sum.inl_ne_inr, Stack.source, Stack.assignment, Stack.saved, Stack.output, Stack.binary, Stack.budget, Stack.work, Stack.index, ↓reduceIte, Bool.cond_true, Bool.cond_false, advance, TM2.step, TM2.stepAux, program, cfg, bank, remembered,
    Stack.source, again, Sum.elim_inr, List.head?_cons, List.tail_cons,
    Option.getD_some, ite_true]
  all_goals bank_ext
theorem scan_false (u : ProtocolBoundedUnary.Control) (r : Register)
    (source budget work a : List Bool) :
    advance program (cfg (some (.inr .scan)) (u,r)
      [] budget work [] (false::source) a [] []) =
    cfg (some (.inr .restoreHeader)) (u,{r with popped:=some false})
      [] budget work [] source a [] [] := by
  simp only [Bool.false_eq_true, Bool.true_eq_false, eq_self, show (0:Fin 4) ≠ 1 by decide, show (0:Fin 4) ≠ 2 by decide, show (0:Fin 4) ≠ 3 by decide, show (1:Fin 4) ≠ 0 by decide, show (1:Fin 4) ≠ 2 by decide, show (1:Fin 4) ≠ 3 by decide, show (2:Fin 4) ≠ 0 by decide, show (2:Fin 4) ≠ 1 by decide, show (2:Fin 4) ≠ 3 by decide, show (3:Fin 4) ≠ 0 by decide, show (3:Fin 4) ≠ 1 by decide, show (3:Fin 4) ≠ 2 by decide, Function.update_apply, Sum.inr_ne_inl, Sum.inl_ne_inr, Stack.source, Stack.assignment, Stack.saved, Stack.output, Stack.binary, Stack.budget, Stack.work, Stack.index, ↓reduceIte, Bool.cond_true, Bool.cond_false, advance, TM2.step, TM2.stepAux, program, cfg, bank, remembered,
    Stack.source, again, Sum.elim_inr, List.head?_cons, List.tail_cons,
    Option.getD_some, Bool.false_eq_true, ite_false]
  all_goals bank_ext
theorem payload_step (u : ProtocolBoundedUnary.Control) (r : Register) (b : Bool)
    (source budget work a : List Bool) :
    advance program (cfg (some (.inr .payload)) (u,r)
      [] budget work [] (b::source) a [] []) =
    cfg (some (.inr .scan)) (u,{r with popped:=some b})
      [] budget (b::work) [] source a [] [] := by
  simp only [Bool.false_eq_true, Bool.true_eq_false, eq_self, show (0:Fin 4) ≠ 1 by decide, show (0:Fin 4) ≠ 2 by decide, show (0:Fin 4) ≠ 3 by decide, show (1:Fin 4) ≠ 0 by decide, show (1:Fin 4) ≠ 2 by decide, show (1:Fin 4) ≠ 3 by decide, show (2:Fin 4) ≠ 0 by decide, show (2:Fin 4) ≠ 1 by decide, show (2:Fin 4) ≠ 3 by decide, show (3:Fin 4) ≠ 0 by decide, show (3:Fin 4) ≠ 1 by decide, show (3:Fin 4) ≠ 2 by decide, Function.update_apply, Sum.inr_ne_inl, Sum.inl_ne_inr, Stack.source, Stack.assignment, Stack.saved, Stack.output, Stack.binary, Stack.budget, Stack.work, Stack.index, ↓reduceIte, Bool.cond_true, Bool.cond_false, advance, TM2.step, TM2.stepAux, program, cfg, bank, remembered,
    Stack.source, Stack.work, again, Sum.elim_inr, List.head?_cons, List.tail_cons,
    Option.getD_some]
  all_goals bank_ext
theorem scan_run (u : ProtocolBoundedUnary.Control) (r : Register)
    (bits source budget work a : List Bool) :
    run (2*bits.length+1) (cfg (some (.inr .scan)) (u,r)
      [] budget work [] (EncodedCommunication.field bits++source) a [] []) =
    cfg (some (.inr .restoreHeader)) (u,{r with popped:=some false})
      [] budget (bits.reverse++work) [] source a [] [] := by
  induction bits generalizing r work with
  | nil => simpa [run, EncodedCommunication.field] using scan_false u r source budget work a
  | cons b bits ih =>
      rw [show 2*(b::bits).length+1=(2*bits.length+1)+1+1 by simp; omega,
        run_succ]
      simp only [EncodedCommunication.field, List.cons_append]
      rw [scan_true, run_succ, payload_step, ih]
      simp [List.reverse_cons, List.append_assoc]

theorem header_restore_step (u : ProtocolBoundedUnary.Control) (r : Register) (b : Bool)
    (binary budget work source a : List Bool) :
    advance program (cfg (some (.inr .restoreHeader)) (u,r)
      binary budget (b::work) [] source a [] []) =
    cfg (some (.inr .restoreHeader)) (u,{r with popped:=some b})
      (b::binary) budget work [] source a [] [] := by
  simp only [Bool.false_eq_true, Bool.true_eq_false, eq_self, show (0:Fin 4) ≠ 1 by decide, show (0:Fin 4) ≠ 2 by decide, show (0:Fin 4) ≠ 3 by decide, show (1:Fin 4) ≠ 0 by decide, show (1:Fin 4) ≠ 2 by decide, show (1:Fin 4) ≠ 3 by decide, show (2:Fin 4) ≠ 0 by decide, show (2:Fin 4) ≠ 1 by decide, show (2:Fin 4) ≠ 3 by decide, show (3:Fin 4) ≠ 0 by decide, show (3:Fin 4) ≠ 1 by decide, show (3:Fin 4) ≠ 2 by decide, Function.update_apply, Sum.inr_ne_inl, Sum.inl_ne_inr, Stack.source, Stack.assignment, Stack.saved, Stack.output, Stack.binary, Stack.budget, Stack.work, Stack.index, ↓reduceIte, Bool.cond_true, Bool.cond_false, advance, TM2.step, TM2.stepAux, program, cfg, bank, remembered,
    Stack.work, Stack.binary, again, Sum.elim_inl, Sum.elim_inr,
    ProtocolBoundedUnary.stackContents, List.head?_cons, List.tail_cons,
    Option.getD_some, Option.isSome_some, ite_true]
  all_goals bank_ext
theorem header_restore_nil (u : ProtocolBoundedUnary.Control) (r : Register)
    (binary budget source a : List Bool) :
    advance program (cfg (some (.inr .restoreHeader)) (u,r)
      binary budget [] [] source a [] []) =
    cfg (some (.inl .zeroScan)) ((none,false),{r with popped:=none})
      binary budget [] [] source a [] [] := by
  simp only [Bool.false_eq_true, Bool.true_eq_false, eq_self, show (0:Fin 4) ≠ 1 by decide, show (0:Fin 4) ≠ 2 by decide, show (0:Fin 4) ≠ 3 by decide, show (1:Fin 4) ≠ 0 by decide, show (1:Fin 4) ≠ 2 by decide, show (1:Fin 4) ≠ 3 by decide, show (2:Fin 4) ≠ 0 by decide, show (2:Fin 4) ≠ 1 by decide, show (2:Fin 4) ≠ 3 by decide, show (3:Fin 4) ≠ 0 by decide, show (3:Fin 4) ≠ 1 by decide, show (3:Fin 4) ≠ 2 by decide, Function.update_apply, Sum.inr_ne_inl, Sum.inl_ne_inr, Stack.source, Stack.assignment, Stack.saved, Stack.output, Stack.binary, Stack.budget, Stack.work, Stack.index, ↓reduceIte, Bool.cond_true, Bool.cond_false, advance, TM2.step, TM2.stepAux, program, cfg, bank, remembered,
    Stack.work, Sum.elim_inl, ProtocolBoundedUnary.stackContents,
    List.head?_nil, List.tail_nil, Option.getD_some, Option.isSome_none, ite_false]
  all_goals bank_ext
theorem header_restore_run (u : ProtocolBoundedUnary.Control) (r : Register)
    (binary budget work source a : List Bool) :
    run (work.length+1) (cfg (some (.inr .restoreHeader)) (u,r)
      binary budget work [] source a [] []) =
    cfg (some (.inl .zeroScan)) ((none,false),{r with popped:=none})
      (work.reverse++binary) budget [] [] source a [] [] := by
  induction work generalizing r binary with
  | nil => simpa [run] using header_restore_nil u r binary budget source a
  | cons b work ih =>
      rw [List.length_cons, run_succ, header_restore_step, ih]
      simp [List.reverse_cons, List.append_assoc]

/-- The valid-input path reads the exact canonical header format used by
`ProtocolBinaryHeader`, leaving the physical unused suffix intact. -/
theorem header_run (sign : Bool) (i : ℕ) (source budget a : List Bool) :
    run (3*i.bits.length+2)
      (cfg (some (.inr .scan)) ((none,false),⟨sign,none,false⟩)
        [] budget [] [] (EncodedCommunication.natField i++source) a [] []) =
    cfg (some (.inl .zeroScan)) ((none,false),⟨sign,none,false⟩)
      i.bits budget [] [] source a [] [] := by
  have hc : ProtocolBinaryHeader.canonical i.bits = true := ProtocolBinaryHeader.canonical_of_bits i
  have hs := scan_run (none,false) ⟨sign,none,false⟩ i.bits source budget [] a
  have hr := header_restore_run (none,false) ⟨sign,some false,false⟩
    [] budget i.bits.reverse source a
  simp only [List.append_nil, List.length_reverse, List.reverse_reverse] at hs hr
  have hh := (run_add hs (i.bits.length+1)).trans hr
  rw [show 2*i.bits.length+1+(i.bits.length+1)=3*i.bits.length+2 by omega] at hh
  exact hh

theorem afterUnary_step (u : ProtocolBoundedUnary.Control) (r : Register)
    (binary budget index source a : List Bool) :
    advance program (cfg (some (.inr .afterUnary)) (u,r)
      binary budget [] (true::index) source a [] []) =
    cfg (some (.inr .clearBinary)) (u,{r with popped:=some true})
      binary budget [] index source a [] [] := by
  simp only [Bool.false_eq_true, Bool.true_eq_false, eq_self, show (0:Fin 4) ≠ 1 by decide, show (0:Fin 4) ≠ 2 by decide, show (0:Fin 4) ≠ 3 by decide, show (1:Fin 4) ≠ 0 by decide, show (1:Fin 4) ≠ 2 by decide, show (1:Fin 4) ≠ 3 by decide, show (2:Fin 4) ≠ 0 by decide, show (2:Fin 4) ≠ 1 by decide, show (2:Fin 4) ≠ 3 by decide, show (3:Fin 4) ≠ 0 by decide, show (3:Fin 4) ≠ 1 by decide, show (3:Fin 4) ≠ 2 by decide, Function.update_apply, Sum.inr_ne_inl, Sum.inl_ne_inr, Stack.source, Stack.assignment, Stack.saved, Stack.output, Stack.binary, Stack.budget, Stack.work, Stack.index, ↓reduceIte, Bool.cond_true, Bool.cond_false, advance, TM2.step, TM2.stepAux, program, cfg, bank, remembered,
    Stack.index, again, Sum.elim_inl, ProtocolBoundedUnary.stackContents,
    List.head?_cons, List.tail_cons, Option.getD_some]
  all_goals bank_ext

theorem clear_step (which : Bool) (u : ProtocolBoundedUnary.Control) (r : Register)
    (b : Bool) (q cap index source a : List Bool) :
    advance program (cfg (some (.inr (if which then .clearBudget else .clearBinary)))
      (u,r) (if which then [] else b::q) (if which then b::cap else cap)
      [] index source a [] []) =
    cfg (some (.inr (if which then .clearBudget else .clearBinary)))
      (u,{r with popped:=some b}) (if which then [] else q) cap
      [] index source a [] [] := by
  cases which <;>
    simp only [Bool.false_eq_true, Bool.true_eq_false, eq_self, show (0:Fin 4) ≠ 1 by decide, show (0:Fin 4) ≠ 2 by decide, show (0:Fin 4) ≠ 3 by decide, show (1:Fin 4) ≠ 0 by decide, show (1:Fin 4) ≠ 2 by decide, show (1:Fin 4) ≠ 3 by decide, show (2:Fin 4) ≠ 0 by decide, show (2:Fin 4) ≠ 1 by decide, show (2:Fin 4) ≠ 3 by decide, show (3:Fin 4) ≠ 0 by decide, show (3:Fin 4) ≠ 1 by decide, show (3:Fin 4) ≠ 2 by decide, Function.update_apply, Sum.inr_ne_inl, Sum.inl_ne_inr, Stack.source, Stack.assignment, Stack.saved, Stack.output, Stack.binary, Stack.budget, Stack.work, Stack.index, ↓reduceIte, Bool.cond_true, Bool.cond_false, advance, TM2.step, TM2.stepAux, program, cfg, bank, remembered,
      Stack.binary, Stack.budget, again, Sum.elim_inl, ProtocolBoundedUnary.stackContents,
      List.head?_cons, List.tail_cons, Option.getD_some, Option.isSome_some,
      Bool.cond_true, Bool.cond_false, ite_true, ite_false] <;> bank_ext
theorem clear_nil (which : Bool) (u : ProtocolBoundedUnary.Control) (r : Register)
    (cap index source a : List Bool) :
    advance program (cfg (some (.inr (if which then .clearBudget else .clearBinary)))
      (u,r) [] (if which then [] else cap) [] index source a [] []) =
    cfg (some (.inr (if which then .lookup else .clearBudget)))
      (u,{r with popped:=none}) [] (if which then [] else cap) [] index source a [] [] := by
  cases which <;>
    simp only [Bool.false_eq_true, Bool.true_eq_false, eq_self, show (0:Fin 4) ≠ 1 by decide, show (0:Fin 4) ≠ 2 by decide, show (0:Fin 4) ≠ 3 by decide, show (1:Fin 4) ≠ 0 by decide, show (1:Fin 4) ≠ 2 by decide, show (1:Fin 4) ≠ 3 by decide, show (2:Fin 4) ≠ 0 by decide, show (2:Fin 4) ≠ 1 by decide, show (2:Fin 4) ≠ 3 by decide, show (3:Fin 4) ≠ 0 by decide, show (3:Fin 4) ≠ 1 by decide, show (3:Fin 4) ≠ 2 by decide, Function.update_apply, Sum.inr_ne_inl, Sum.inl_ne_inr, Stack.source, Stack.assignment, Stack.saved, Stack.output, Stack.binary, Stack.budget, Stack.work, Stack.index, ↓reduceIte, Bool.cond_true, Bool.cond_false, advance, TM2.step, TM2.stepAux, program, cfg, bank, remembered,
      Stack.binary, Stack.budget, again, Sum.elim_inl, ProtocolBoundedUnary.stackContents,
      List.head?_nil, List.tail_nil, Option.getD_some, Option.isSome_none,
      Bool.cond_true, Bool.cond_false, ite_true, ite_false] <;> bank_ext
theorem clear_binary_run (u : ProtocolBoundedUnary.Control) (r : Register)
    (q cap index source a : List Bool) :
    run (q.length+1) (cfg (some (.inr .clearBinary)) (u,r)
      q cap [] index source a [] []) =
    cfg (some (.inr .clearBudget)) (u,{r with popped:=none})
      [] cap [] index source a [] [] := by
  induction q generalizing r with
  | nil => simpa [run] using clear_nil false u r cap index source a
  | cons b q ih =>
      rw [List.length_cons, run_succ]
      rw [show advance program (cfg (some (.inr .clearBinary)) (u,r)
        (b::q) cap [] index source a [] []) = _ from clear_step false u r b q cap index source a]
      exact ih _
theorem clear_budget_run (u : ProtocolBoundedUnary.Control) (r : Register)
    (cap index source a : List Bool) :
    run (cap.length+1) (cfg (some (.inr .clearBudget)) (u,r)
      [] cap [] index source a [] []) =
    cfg (some (.inr .lookup)) (u,{r with popped:=none})
      [] [] [] index source a [] [] := by
  induction cap generalizing r with
  | nil => simpa [run] using clear_nil true u r [] index source a
  | cons b cap ih =>
      rw [List.length_cons, run_succ]
      rw [show advance program (cfg (some (.inr .clearBudget)) (u,r)
        [] (b::cap) [] index source a [] []) = _ from clear_step true u r b [] cap index source a]
      exact ih _

theorem lookup_step (u : ProtocolBoundedUnary.Control) (r : Register) (b : Bool)
    (index source a saved : List Bool) :
    advance program (cfg (some (.inr .lookup)) (u,r)
      [] [] [] (true::index) source (b::a) [] saved) =
    cfg (some (.inr .lookup)) (u,{r with popped:=some b})
      [] [] [] index source a [] (b::saved) := by
  simp only [Bool.false_eq_true, Bool.true_eq_false, eq_self, show (0:Fin 4) ≠ 1 by decide, show (0:Fin 4) ≠ 2 by decide, show (0:Fin 4) ≠ 3 by decide, show (1:Fin 4) ≠ 0 by decide, show (1:Fin 4) ≠ 2 by decide, show (1:Fin 4) ≠ 3 by decide, show (2:Fin 4) ≠ 0 by decide, show (2:Fin 4) ≠ 1 by decide, show (2:Fin 4) ≠ 3 by decide, show (3:Fin 4) ≠ 0 by decide, show (3:Fin 4) ≠ 1 by decide, show (3:Fin 4) ≠ 2 by decide, Function.update_apply, Sum.inr_ne_inl, Sum.inl_ne_inr, Stack.source, Stack.assignment, Stack.saved, Stack.output, Stack.binary, Stack.budget, Stack.work, Stack.index, ↓reduceIte, Bool.cond_true, Bool.cond_false, advance, TM2.step, TM2.stepAux, program, cfg, bank, remembered,
    Stack.index, Stack.assignment, Stack.saved, again, Sum.elim_inl, Sum.elim_inr,
    ProtocolBoundedUnary.stackContents, List.head?_cons, List.tail_cons,
    Option.getD_some, Option.isSome_some, Bool.cond_true, ite_true]
  all_goals bank_ext
theorem lookup_nil (u : ProtocolBoundedUnary.Control) (r : Register)
    (source a saved : List Bool) :
    advance program (cfg (some (.inr .lookup)) (u,r)
      [] [] [] [] source a [] saved) =
    cfg (some (.inr .restoreLookup))
      (u,{r with popped:=none, answer:=a.head?.getD false})
      [] [] [] [] source a [] saved := by
  simp only [Bool.false_eq_true, Bool.true_eq_false, eq_self, show (0:Fin 4) ≠ 1 by decide, show (0:Fin 4) ≠ 2 by decide, show (0:Fin 4) ≠ 3 by decide, show (1:Fin 4) ≠ 0 by decide, show (1:Fin 4) ≠ 2 by decide, show (1:Fin 4) ≠ 3 by decide, show (2:Fin 4) ≠ 0 by decide, show (2:Fin 4) ≠ 1 by decide, show (2:Fin 4) ≠ 3 by decide, show (3:Fin 4) ≠ 0 by decide, show (3:Fin 4) ≠ 1 by decide, show (3:Fin 4) ≠ 2 by decide, Function.update_apply, Sum.inr_ne_inl, Sum.inl_ne_inr, Stack.source, Stack.assignment, Stack.saved, Stack.output, Stack.binary, Stack.budget, Stack.work, Stack.index, ↓reduceIte, Bool.cond_true, Bool.cond_false, advance, TM2.step, TM2.stepAux, program, cfg, bank, remembered,
    Stack.index, Stack.assignment, again, Sum.elim_inl, Sum.elim_inr,
    ProtocolBoundedUnary.stackContents, List.head?_nil, List.tail_nil,
    Option.getD_some, Option.isSome_none, Bool.cond_false, ite_false]
  all_goals bank_ext
theorem lookup_prefix_run (u : ProtocolBoundedUnary.Control) (r : Register)
    (pref suffix source saved : List Bool) :
    run pref.length (cfg (some (.inr .lookup)) (u,r)
      [] [] [] (List.replicate pref.length true) source (pref++suffix) [] saved) =
    cfg (some (.inr .lookup))
      (u,{r with popped:=if pref=[] then r.popped else some (pref.getLast?.getD false)})
      [] [] [] [] source suffix [] (pref.reverse++saved) := by
  induction pref generalizing r saved with
  | nil => simp [run, cfg, List.replicate]
  | cons b pref ih =>
      rw [List.length_cons, run_succ]
      simp only [List.replicate_succ, List.cons_append]
      rw [lookup_step, ih]
      cases pref <;> simp [List.reverse_cons, List.append_assoc]

theorem finish_step (u : ProtocolBoundedUnary.Control) (r : Register) (source a : List Bool) :
    advance program (cfg (some (.inr .finish)) (u,r) [] [] [] [] source a [] []) =
      ⟨none,initial,resultBank source a (if r.sign then r.answer else !r.answer)⟩ := by
  simp only [Bool.false_eq_true, Bool.true_eq_false, eq_self, show (0:Fin 4) ≠ 1 by decide, show (0:Fin 4) ≠ 2 by decide, show (0:Fin 4) ≠ 3 by decide, show (1:Fin 4) ≠ 0 by decide, show (1:Fin 4) ≠ 2 by decide, show (1:Fin 4) ≠ 3 by decide, show (2:Fin 4) ≠ 0 by decide, show (2:Fin 4) ≠ 1 by decide, show (2:Fin 4) ≠ 3 by decide, show (3:Fin 4) ≠ 0 by decide, show (3:Fin 4) ≠ 1 by decide, show (3:Fin 4) ≠ 2 by decide, Function.update_apply, Sum.inr_ne_inl, Sum.inl_ne_inr, Stack.source, Stack.assignment, Stack.saved, Stack.output, Stack.binary, Stack.budget, Stack.work, Stack.index, ↓reduceIte, Bool.cond_true, Bool.cond_false, advance, TM2.step, TM2.stepAux, program, cfg, bank, resultBank, ready,
    Stack.output, Option.getD_some]
  rfl

theorem lookup_complete (u : ProtocolBoundedUnary.Control) (r : Register)
    (i : ℕ) (source a : List Bool) (hi : i < a.length) :
    run (2*i+3) (cfg (some (.inr .lookup)) (u,r)
      [] [] [] (List.replicate i true) source a [] []) =
    ⟨none,initial,resultBank source a
      (if r.sign then a.getD i false else !(a.getD i false))⟩ := by
  have hlen : (a.take i).length = i := by simp [List.length_take, min_eq_left (Nat.le_of_lt hi)]
  have hp := lookup_prefix_run u r (a.take i) (a.drop i) source []
  simp only [hlen, List.take_append_drop, List.append_nil] at hp
  have hn := lookup_nil u
    {r with popped:=if a.take i=[] then r.popped else some ((a.take i).getLast?.getD false)}
    source (a.drop i) (a.take i).reverse
  have hr := restore_run true u
    {r with popped:=none, answer:=(a.drop i).head?.getD false}
    [] [] [] source (a.drop i) [] (a.take i).reverse
  simp only [List.length_reverse, hlen, List.reverse_reverse,
    List.take_append_drop] at hr
  have hf := finish_step u {r with popped:=none, answer:=(a.drop i).head?.getD false} source a
  have hh := (run_add hp 1).trans hn
  have hh := (run_add hh (i+1)).trans hr
  have hh := (run_add hh 1).trans hf
  have hv : (a.drop i).head?.getD false = a.getD i false := by
    simp [List.head?_drop, List.getD_eq_getElem?_getD]
  rw [show i+1+(i+1)+1=2*i+3 by omega, hv] at hh
  exact hh

theorem cleanup_run (u : ProtocolBoundedUnary.Control) (sign : Bool)
    (q cap source a : List Bool) (i : ℕ) (hi : i<a.length) :
    run (q.length+cap.length+2*i+6)
      (cfg (some (.inr .afterUnary)) (u,⟨sign,none,false⟩)
        q cap [] (true::List.replicate i true) source a [] []) =
    ⟨none,initial,resultBank source a
      (if sign then a.getD i false else !(a.getD i false))⟩ := by
  have hs : run 1 (cfg (some (.inr .afterUnary)) (u,⟨sign,none,false⟩)
      q cap [] (true::List.replicate i true) source a [] []) =
      cfg (some (.inr .clearBinary)) (u,⟨sign,some true,false⟩)
        q cap [] (List.replicate i true) source a [] [] := by
    simpa only [run,Function.iterate_one] using
      afterUnary_step u ⟨sign,none,false⟩ q cap (List.replicate i true) source a
  have hb := clear_binary_run u ⟨sign,some true,false⟩ q cap (List.replicate i true) source a
  have hc := clear_budget_run u ⟨sign,none,false⟩ cap (List.replicate i true) source a
  have hl := lookup_complete u ⟨sign,none,false⟩ i source a hi
  have hh := (run_add hs (q.length+1)).trans hb
  have hh := (run_add hh (cap.length+1)).trans hc
  have hh := (run_add hh (2*i+3)).trans hl
  rw [show 1+(q.length+1)+(cap.length+1)+(2*i+3)=q.length+cap.length+2*i+6 by omega] at hh
  exact hh

theorem unary_run (sign : Bool) (i : ℕ) (source a : List Bool) (hi : i<a.length) :
    ∃ t u q cap, t ≤ (a.length+1)*(4*i.bits.length+5) ∧
      q.length=i.bits.length ∧ cap.length≤a.length ∧
      run t (cfg (some (.inl .zeroScan)) ((none,false),⟨sign,none,false⟩)
        i.bits a.reverse [] [] source a [] []) =
      cfg (some (.inr .afterUnary)) (u,⟨sign,none,false⟩)
        q cap [] (true::List.replicate i true) source a [] [] := by
  obtain ⟨t,c,ht,hc,hh,ho,hq,hw,hcap⟩ := ProtocolBoundedUnary.bounded_run_framed i.bits a.reverse []
  have hr : ProtocolBoundedUnary.result i.bits a.reverse [] = true::List.replicate i true := by
    simp [ProtocolBoundedUnary.result, min_eq_left (Nat.le_of_lt hi), Nat.le_of_lt hi]
  obtain ⟨n,hn,he⟩ := lift_outputs ProtocolBoundedUnary.program program (some Outer.afterUnary)
    (fun _ => rfl) (⟨sign,none,false⟩ : Register)
    (fun | .source => source | .assignment => a | .output => [] | .saved => [])
    (ProtocolBoundedUnary.cfg (some .zeroScan) (none,false) i.bits a.reverse [] []) t (by
      change (ProtocolBoundedUnary.run t _).l=none
      rw [hc]; exact hh)
  have hce : c = ProtocolBoundedUnary.cfg none c.var (c.stk 0) (c.stk 1) []
      (true::List.replicate i true) := by
    rcases c with ⟨lc,vc,sc⟩
    simp only at hh ho hw
    subst lc
    unfold ProtocolBoundedUnary.cfg
    congr 1
    funext k
    fin_cases k <;> simp [ProtocolBoundedUnary.stackContents, hw, ho, hr]
  change run n (cfg (some (.inl .zeroScan)) ((none,false),⟨sign,none,false⟩)
    i.bits a.reverse [] [] source a [] []) = liftCfg (some Outer.afterUnary)
      (⟨sign,none,false⟩ : Register) _ (ProtocolBoundedUnary.run t _) at he
  rw [hc,hce] at he
  refine ⟨n,c.var,c.stk 0,c.stk 1,?_,hq,?_,he⟩
  · simpa only [List.length_reverse] using hn.trans ht
  · simpa only [List.length_reverse] using hcap

def coefficient : ℕ := 100
def exponent : ℕ := 2

/-- One fixed finite program evaluates every valid literal, with an actual
transition bound, byte-identical preserved suffix/assignment, and empty
scratch bank. Its execution contains no callback, clock or promise oracle. -/
theorem canonical_run (l : EncodedCNF.Literal) (a rest : List Bool)
    (hi : l.variable<a.length) :
    ∃ t ≤ coefficient*((EncodedCNF.encodeLiteral l++rest).length+a.length+1)^exponent,
      run t ⟨some start,initial,ready (EncodedCNF.encodeLiteral l++rest) a⟩ =
        ⟨none,initial,resultBank rest a (l.eval a)⟩ := by
  obtain ⟨t,u,q,cap,ht,hq,hcap,hu⟩ := unary_run l.positive l.variable rest a hi
  have ha := prepared_assignment l.positive (EncodedCommunication.natField l.variable++rest) a
  have hh := header_run l.positive l.variable rest a.reverse a
  have hc := cleanup_run u l.positive q cap rest a l.variable hi
  have he := (run_add ha (3*l.variable.bits.length+2)).trans hh
  have he := (run_add he t).trans hu
  have he := (run_add he (q.length+cap.length+2*l.variable+6)).trans hc
  refine ⟨2*a.length+3+(3*l.variable.bits.length+2)+t+
    (q.length+cap.length+2*l.variable+6), ?_, ?_⟩
  · have hs : (EncodedCNF.encodeLiteral l++rest).length =
        2*l.variable.bits.length+2+rest.length := by
      simp [List.length_append, EncodedCNF.encodeLiteral_length]
    simp only [coefficient, exponent, pow_two]
    rw [hq,hs]
    nlinarith
  · simpa only [EncodedCNF.encodeLiteral, List.cons_append, EncodedCNF.Literal.eval] using he

#print axioms canonical_run

theorem ready_scratch (source a : List Bool) (k : Stack)
    (hs : k ≠ Stack.source) (ha : k ≠ Stack.assignment) : ready source a k = [] := by
  cases k with
  | inl k => fin_cases k <;> rfl
  | inr k => cases k <;> simp_all [Stack.source, Stack.assignment, ready, bank]

theorem resultBank_scratch (source a : List Bool) (b : Bool) (k : Stack)
    (hs : k ≠ Stack.source) (ha : k ≠ Stack.assignment) (ho : k ≠ Stack.output) :
    resultBank source a b k = [] := by
  rw [resultBank, Function.update_of_ne ho]
  exact ready_scratch source a k hs ha

noncomputable def machine : BitMachine.Machine :=
  ofFinite Stack.source Stack.output start initial program

end CurrentAdditive.V39CNFLiteral
