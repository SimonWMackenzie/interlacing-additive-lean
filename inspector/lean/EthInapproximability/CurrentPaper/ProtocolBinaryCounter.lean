import EthInapproximability.CurrentPaper.EncodedCommunication

/-!
# Binary counters for the encoded verifier

Source: locked v8 `03-exact-hardness.tex`, NP membership, with the fixed
bit-machine convention from `06-eth.tex`. The encoded dimensions and threshold
must not be expanded into unary. This component implements a saturating
predecessor directly on least-significant-bit-first Boolean stacks.
-/

namespace EthInapproximability.CurrentPaper.ProtocolBinaryCounter

open Turing TM2.Stmt
open BitMachine

/-- The finite control records only the last popped symbol. -/
def symbolCode : Option Bool → Fin 3
  | none => 0
  | some false => 1
  | some true => 2

/-- Borrow, copy the remaining digits, restore their order, or clear an
underflowed all-zero counter. Each instruction is a fixed finite statement. -/
def program (label : Fin 4) : TM2.Stmt (fun _ : Fin 2 => Bool) (Fin 4) (Fin 3) :=
  if label = 0 then
    pop 0 (fun _ b => symbolCode b)
      (branch (fun s => decide (s = 0)) (goto (fun _ => 3))
        (branch (fun s => decide (s = 1))
          (push 1 (fun _ => true) (goto (fun _ => 0)))
          (push 1 (fun _ => false) (goto (fun _ => 1)))))
  else if label = 1 then
    pop 0 (fun _ b => symbolCode b)
      (branch (fun s => decide (s = 0)) (goto (fun _ => 2))
        (push 1 (fun s => decide (s = 2)) (goto (fun _ => 1))))
  else if label = 2 then
    pop 1 (fun _ b => symbolCode b)
      (branch (fun s => decide (s = 0)) halt
        (push 0 (fun s => decide (s = 2)) (goto (fun _ => 2))))
  else
    pop 1 (fun _ b => symbolCode b)
      (branch (fun s => decide (s = 0)) halt (goto (fun _ => 3)))

def machine : Machine where
  stackCount := 2
  labelCount := 4
  controlCount := 3
  input := 0
  output := 0
  start := 0
  initial := 0
  program := program

def stackContents (input work : List Bool) : Fin 2 → List Bool :=
  fun k => if k = 0 then input else work

def cfg (label : Option (Fin 4)) (state : Fin 3) (input work : List Bool) :
    machine.Config := ⟨label, state, stackContents input work⟩

@[simp] theorem stacks_zero (input work : List Bool) : stackContents input work 0 = input := rfl
@[simp] theorem stacks_one (input work : List Bool) : stackContents input work 1 = work := rfl

@[simp] theorem update_zero (input work new : List Bool) :
    Function.update (stackContents input work) 0 new = stackContents new work := by
  funext k
  fin_cases k <;> simp [stackContents]

@[simp] theorem update_one (input work new : List Bool) :
    Function.update (stackContents input work) 1 new = stackContents input new := by
  funext k
  fin_cases k <;> simp [stackContents]

theorem step_borrow_nil (state : Fin 3) (work : List Bool) :
    machine.step (cfg (some 0) state [] work) = cfg (some 3) 0 [] work := by
  simp [Machine.step, machine, cfg, TM2.step, TM2.stepAux, program, symbolCode]

theorem step_borrow_false (state : Fin 3) (input work : List Bool) :
    machine.step (cfg (some 0) state (false :: input) work) =
      cfg (some 0) 1 input (true :: work) := by
  simp [Machine.step, machine, cfg, TM2.step, TM2.stepAux, program, symbolCode]
  funext k
  fin_cases k <;> simp [stackContents]

theorem step_borrow_true (state : Fin 3) (input work : List Bool) :
    machine.step (cfg (some 0) state (true :: input) work) =
      cfg (some 1) 2 input (false :: work) := by
  simp [Machine.step, machine, cfg, TM2.step, TM2.stepAux, program, symbolCode]
  funext k
  fin_cases k <;> simp [stackContents]

theorem step_copy_nil (state : Fin 3) (work : List Bool) :
    machine.step (cfg (some 1) state [] work) = cfg (some 2) 0 [] work := by
  simp [Machine.step, machine, cfg, TM2.step, TM2.stepAux, program, symbolCode]

theorem step_copy_cons (state : Fin 3) (b : Bool) (input work : List Bool) :
    machine.step (cfg (some 1) state (b :: input) work) =
      cfg (some 1) (symbolCode (some b)) input (b :: work) := by
  cases b <;>
    simp [Machine.step, machine, cfg, TM2.step, TM2.stepAux, program, symbolCode]
  all_goals
    funext k
    fin_cases k <;> simp [stackContents]

theorem step_restore_nil (state : Fin 3) (input : List Bool) :
    machine.step (cfg (some 2) state input []) = cfg none 0 input [] := by
  simp [Machine.step, machine, cfg, TM2.step, TM2.stepAux, program, symbolCode]

theorem step_restore_cons (state : Fin 3) (b : Bool) (input work : List Bool) :
    machine.step (cfg (some 2) state input (b :: work)) =
      cfg (some 2) (symbolCode (some b)) (b :: input) work := by
  cases b <;>
    simp [Machine.step, machine, cfg, TM2.step, TM2.stepAux, program, symbolCode]
  all_goals
    funext k
    fin_cases k <;> simp [stackContents]

theorem step_clear_nil (state : Fin 3) :
    machine.step (cfg (some 3) state [] []) = cfg none 0 [] [] := by
  simp [Machine.step, machine, cfg, TM2.step, TM2.stepAux, program, symbolCode]

theorem step_clear_cons (state : Fin 3) (b : Bool) (work : List Bool) :
    machine.step (cfg (some 3) state [] (b :: work)) =
      cfg (some 3) (symbolCode (some b)) [] work := by
  cases b <;>
    simp [Machine.step, machine, cfg, TM2.step, TM2.stepAux, program, symbolCode]
  all_goals
    funext k
    fin_cases k <;> simp [stackContents]

theorem run_succ_first (n : Nat) (c : machine.Config) :
    machine.run (n + 1) c = machine.run n (machine.step c) := by
  exact Function.iterate_succ_apply _ _ _

theorem restore_correct (work input : List Bool) (state : Fin 3) :
    machine.run (work.length + 1) (cfg (some 2) state input work) =
      cfg none 0 (work.reverse ++ input) [] := by
  induction work generalizing input state with
  | nil => simp [run_succ_first, step_restore_nil]
  | cons b work ih =>
      rw [List.length_cons, run_succ_first, step_restore_cons, ih]
      simp

theorem clear_correct (work : List Bool) (state : Fin 3) :
    machine.run (work.length + 1) (cfg (some 3) state [] work) = cfg none 0 [] [] := by
  induction work generalizing state with
  | nil => simp [run_succ_first, step_clear_nil]
  | cons b work ih =>
      rw [List.length_cons, run_succ_first, step_clear_cons, ih]

theorem copy_correct (input work : List Bool) (state : Fin 3) :
    machine.run (2 * input.length + work.length + 2) (cfg (some 1) state input work) =
      cfg none 0 (work.reverse ++ input) [] := by
  induction input generalizing work state with
  | nil =>
      simp only [List.length_nil, Nat.mul_zero, Nat.zero_add]
      rw [show work.length + 2 = (work.length + 1) + 1 by omega,
        run_succ_first, step_copy_nil, restore_correct]
  | cons b input ih =>
      rw [show 2 * (b :: input).length + work.length + 2 =
        (2 * input.length + (b :: work).length + 2) + 1 by simp; omega,
        run_succ_first, step_copy_cons, ih]
      simp

def predInto : List Bool → List Bool → List Bool
  | [], _ => []
  | true :: input, work => work.reverse ++ false :: input
  | false :: input, work => predInto input (true :: work)

def predBits (input : List Bool) : List Bool := predInto input []

theorem borrow_correct (input work : List Bool) (state : Fin 3) :
    machine.run (2 * input.length + work.length + 2) (cfg (some 0) state input work) =
      cfg none 0 (predInto input work) [] := by
  induction input generalizing work state with
  | nil =>
      simp only [List.length_nil, Nat.mul_zero, Nat.zero_add, predInto]
      rw [show work.length + 2 = (work.length + 1) + 1 by omega,
        run_succ_first, step_borrow_nil, clear_correct]
  | cons b input ih =>
      cases b with
      | false =>
          rw [show 2 * (false :: input).length + work.length + 2 =
            (2 * input.length + (true :: work).length + 2) + 1 by simp; omega,
            run_succ_first, step_borrow_false, ih]
          rfl
      | true =>
          rw [show 2 * (true :: input).length + work.length + 2 =
            (2 * input.length + (false :: work).length + 2) + 1 by simp; omega,
            run_succ_first, step_borrow_true, copy_correct]
          simp [predInto]

theorem run_correct (input : List Bool) :
    machine.run (2 * input.length + 2) (machine.init input) =
      cfg none 0 (predBits input) [] := by
  simpa only [List.length_nil, Nat.add_zero, predBits] using borrow_correct input [] 0

theorem outputs (input : List Bool) :
    machine.OutputsWithin input (predBits input) (2 * input.length + 2) := by
  refine ⟨2 * input.length + 2, le_rfl, ?_, ?_⟩ <;> rw [run_correct] <;> rfl

theorem polytime : BitMachine.Polytime predBits := by
  refine ⟨machine, 2, 1, ?_⟩
  intro input
  simpa [Nat.mul_add] using outputs input

/-- An independent recursive specification keeps underflow distinct from a
valid zero result. It is used only to prove the machine's numerical meaning. -/
def subOne : List Bool → Option (List Bool)
  | [] => none
  | true :: input => some (false :: input)
  | false :: input => (subOne input).map (true :: ·)

theorem predInto_eq (input work : List Bool) :
    predInto input work =
      match subOne input with
      | none => []
      | some result => work.reverse ++ result := by
  induction input generalizing work with
  | nil => rfl
  | cons b input ih =>
      cases b with
      | true => rfl
      | false =>
          simp only [predInto, subOne]
          rw [ih]
          cases h : subOne input <;> simp

theorem subOne_spec (input : List Bool) :
    match subOne input with
    | none => EncodedCommunication.bitsValue input = 0
    | some result =>
        EncodedCommunication.bitsValue result + 1 = EncodedCommunication.bitsValue input ∧
        result.length = input.length := by
  induction input with
  | nil => rfl
  | cons b input ih =>
      cases b with
      | true => simp [subOne, EncodedCommunication.bitsValue, Nat.bit_val]
      | false =>
          simp only [subOne]
          cases h : subOne input with
          | none =>
              simp only [h] at ih
              simp [EncodedCommunication.bitsValue, Nat.bit_val, ih]
          | some result =>
              simp only [h] at ih
              simp only [Option.map_some, EncodedCommunication.bitsValue, Nat.bit_val,
                Bool.toNat_true, Bool.toNat_false, Nat.add_zero, List.length_cons]
              constructor
              · omega
              · omega

/-- Correct numerical predecessor on the exact LSB-first interpretation used
by the encoded communication language, including noncanonical padded zeros. -/
theorem predBits_value (input : List Bool) :
    EncodedCommunication.bitsValue (predBits input) =
      EncodedCommunication.bitsValue input - 1 := by
  have hs := subOne_spec input
  rw [predBits, predInto_eq]
  cases h : subOne input with
  | none =>
      simp only [h] at hs
      simp [hs, EncodedCommunication.bitsValue]
  | some result =>
      simp only [h] at hs
      simpa using Nat.eq_sub_of_add_eq hs.1

theorem predBits_length_le (input : List Bool) :
    (predBits input).length ≤ input.length := by
  have hs := subOne_spec input
  rw [predBits, predInto_eq]
  cases h : subOne input with
  | none => simp
  | some result =>
      simp only [h] at hs
      simp [hs.2]

theorem counter_regressions :
    predBits [] = [] ∧ predBits [false, false] = [] ∧
      predBits [false, false, true] = [true, true, false] ∧
      predBits [true, false, true] = [false, false, true] := by decide

end EthInapproximability.CurrentPaper.ProtocolBinaryCounter
