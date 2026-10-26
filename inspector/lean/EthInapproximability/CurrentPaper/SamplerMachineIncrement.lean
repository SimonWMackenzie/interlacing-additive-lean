import EthInapproximability.CurrentPaper.BitMachineEncoding
import EthInapproximability.CurrentPaper.EncodedCommunication
import Mathlib.Tactic

/-!
# Fixed-width binary increment on actual Boolean stacks

Source: locked v8 `E-exact-details.tex`, "Explicit balanced families", monic
binary polynomial enumeration in the proof of `lem:exact-families`.
The least-significant coefficient is at the head of the list. The controller
increments modulo the fixed input width, using two Boolean stacks, two labels,
and an `Option Bool` control register. Its literal transition bound is linear
in the input width. This primitive does not establish the complete sampler
search, arithmetic, enumeration agreement, or runtime.
-/

namespace EthInapproximability.CurrentPaper.SamplerMachineIncrement

open Turing Turing.TM2.Stmt BitMachineEncoding

/-- Little-endian increment modulo the width of the supplied list. -/
def increment : List Bool → List Bool
  | [] => []
  | false :: q => true :: q
  | true :: q => false :: increment q

/-- Number of low-order one bits through which the carry propagates. -/
def carryCount : List Bool → ℕ
  | [] => 0
  | false :: _ => 0
  | true :: q => carryCount q + 1

@[simp] theorem increment_length (q : List Bool) : (increment q).length = q.length := by
  induction q with
  | nil => rfl
  | cons b q ih => cases b <;> simp [increment, ih]

theorem carryCount_le_length (q : List Bool) : carryCount q ≤ q.length := by
  induction q with
  | nil => rfl
  | cons b q ih => cases b <;> simp [carryCount, ih]

/-- Overflow occurs exactly when every bit in the fixed-width input is one. -/
def overflow (q : List Bool) : Bool := q.all id

theorem bitsValue_lt (q : List Bool) :
    EncodedCommunication.bitsValue q < 2 ^ q.length := by
  induction q with
  | nil => simp [EncodedCommunication.bitsValue]
  | cons b q ih =>
      cases b <;>
        simp only [EncodedCommunication.bitsValue, Nat.bit_val, Bool.toNat_false,
          Bool.toNat_true, List.length_cons, pow_succ] <;> omega

theorem increment_value_with_overflow (q : List Bool) :
    EncodedCommunication.bitsValue (increment q) +
        (if overflow q then 2 ^ q.length else 0) =
      EncodedCommunication.bitsValue q + 1 := by
  induction q with
  | nil => simp [increment, overflow, EncodedCommunication.bitsValue]
  | cons b q ih =>
      cases b with
      | false =>
          simp [increment, overflow, EncodedCommunication.bitsValue, Nat.bit_val]
      | true =>
          simp only [increment, overflow, List.all_cons, id_eq, Bool.true_and,
            EncodedCommunication.bitsValue, Nat.bit_val, Bool.toNat_false,
            Bool.toNat_true, List.length_cons, pow_succ] at ih ⊢
          cases hq : q.all id <;> simp_all <;> omega

/-- Numerical successor in the same LSB-first encoding as the communication
language, including all-ones wraparound and the zero-width case. -/
theorem increment_value_mod (q : List Bool) :
    EncodedCommunication.bitsValue (increment q) =
      (EncodedCommunication.bitsValue q + 1) % 2 ^ q.length := by
  have hv := increment_value_with_overflow q
  have hb : EncodedCommunication.bitsValue (increment q) < 2 ^ q.length := by
    simpa only [increment_length] using bitsValue_lt (increment q)
  rw [← hv]
  split <;> simp [Nat.mod_eq_of_lt hb]

inductive Label where
  | carry | restore
  deriving DecidableEq, Fintype

/-- Stack 0 is both input and output; stack 1 temporarily holds cleared bits. -/
def program : Label → TM2.Stmt (fun _ : Fin 2 => Bool) Label (Option Bool)
  | .carry => pop 0 (fun _ b => b)
      (branch Option.isSome
        (branch (fun b => b.getD false)
          (push 1 (fun _ => false) (goto (fun _ => .carry)))
          (push 0 (fun _ => true) (goto (fun _ => .restore))))
        (goto (fun _ => .restore)))
  | .restore => pop 1 (fun _ b => b)
      (branch Option.isSome
        (push 0 (fun b => b.getD false) (goto (fun _ => .restore)))
        (load (fun _ => none) halt))

def stackContents (source saved : List Bool) : Fin 2 → List Bool :=
  fun k => if k = 0 then source else saved

@[simp] private theorem stack_zero (q b : List Bool) : stackContents q b 0 = q := rfl
@[simp] private theorem stack_one (q b : List Bool) : stackContents q b 1 = b := rfl

def cfg (l : Option Label) (s : Option Bool) (q b : List Bool) :
    TM2.Cfg (fun _ : Fin 2 => Bool) Label (Option Bool) :=
  ⟨l, s, stackContents q b⟩

def run (n : ℕ) (c : TM2.Cfg (fun _ : Fin 2 => Bool) Label (Option Bool)) :=
  ((advance program)^[n]) c

private theorem run_succ {c d : TM2.Cfg (fun _ : Fin 2 => Bool) Label (Option Bool)}
    (h : TM2.step program c = some d) (n : ℕ) : run (n + 1) c = run n d := by
  simp only [run, Function.iterate_succ_apply, advance, h, Option.getD_some]

private theorem step_carry_true (s : Option Bool) (q b : List Bool) :
    TM2.step program (cfg (some .carry) s (true :: q) b) =
      some (cfg (some .carry) (some true) q (false :: b)) := by
  simp [TM2.step, TM2.stepAux, program, cfg]
  funext k
  fin_cases k <;> rfl

private theorem step_carry_false (s : Option Bool) (q b : List Bool) :
    TM2.step program (cfg (some .carry) s (false :: q) b) =
      some (cfg (some .restore) (some false) (true :: q) b) := by
  simp [TM2.step, TM2.stepAux, program, cfg]
  funext k
  fin_cases k <;> rfl

private theorem step_carry_nil (s : Option Bool) (b : List Bool) :
    TM2.step program (cfg (some .carry) s [] b) =
      some (cfg (some .restore) none [] b) := by
  simp [TM2.step, TM2.stepAux, program, cfg]

private theorem step_restore_cons (s : Option Bool) (x : Bool) (q b : List Bool) :
    TM2.step program (cfg (some .restore) s q (x :: b)) =
      some (cfg (some .restore) (some x) (x :: q) b) := by
  simp [TM2.step, TM2.stepAux, program, cfg]
  funext k
  fin_cases k <;> rfl

private theorem step_restore_nil (s : Option Bool) (q : List Bool) :
    TM2.step program (cfg (some .restore) s q []) =
      some (cfg none none q []) := by
  simp [TM2.step, TM2.stepAux, program, cfg]

theorem restore_correct (s : Option Bool) (q b : List Bool) :
    run (b.length + 1) (cfg (some .restore) s q b) =
      cfg none none (b.reverse ++ q) [] := by
  induction b generalizing s q with
  | nil => simpa using run_succ (step_restore_nil s q) 0
  | cons x b ih =>
      rw [List.length_cons, run_succ (step_restore_cons s x q b)]
      simpa [List.reverse_cons, List.append_assoc] using ih (some x) (x :: q)

/-- Exact complete configuration after carrying and restoring the saved prefix.
The arbitrary scratch prefix is useful when composing the controller. -/
theorem run_correct (s : Option Bool) (q b : List Bool) :
    run (2 * carryCount q + b.length + 2) (cfg (some .carry) s q b) =
      cfg none none (b.reverse ++ increment q) [] := by
  induction q generalizing s b with
  | nil =>
      simpa [carryCount, increment, Nat.add_assoc] using
        (run_succ (step_carry_nil s b) (b.length + 1)).trans
          (restore_correct none [] b)
  | cons x q ih =>
      cases x with
      | false =>
          simpa [carryCount, increment, Nat.add_assoc] using
            (run_succ (step_carry_false s q b) (b.length + 1)).trans
              (restore_correct (some false) (true :: q) b)
      | true =>
          have h := (run_succ (step_carry_true s q b)
            (2 * carryCount q + (false :: b).length + 2)).trans
              (ih (some true) (false :: b))
          have htime : 2 * carryCount (true :: q) + b.length + 2 =
              (2 * carryCount q + (false :: b).length + 2) + 1 := by
            simp only [carryCount, List.length_cons]
            omega
          rw [htime]
          simpa only [increment, List.reverse_cons, List.append_assoc,
            List.singleton_append] using h

noncomputable def bitMachine : BitMachine.Machine :=
  ofFinite (0 : Fin 2) 0 .carry (none : Option Bool) program

private theorem initial_eq (q : List Bool) :
    rawInit (0 : Fin 2) .carry (none : Option Bool) q = cfg (some .carry) none q [] := by
  unfold rawInit cfg
  congr 1

theorem bitMachine_outputs (q : List Bool) :
    bitMachine.OutputsWithin q (increment q) (2 * q.length + 2) := by
  apply outputsWithin_of_raw_run (0 : Fin 2) 0 .carry (none : Option Bool) program
    q (increment q) (2 * carryCount q + 2) (2 * q.length + 2)
      (by have := carryCount_le_length q; omega)
  · change (run (2 * carryCount q + 2) _).l = none
    rw [initial_eq]
    have h := run_correct none q []
    simp only [List.length_nil, Nat.add_zero, List.reverse_nil, List.nil_append] at h
    rw [h]
    rfl
  · change (run (2 * carryCount q + 2) _).stk 0 = increment q
    rw [initial_eq]
    have h := run_correct none q []
    simp only [List.length_nil, Nat.add_zero, List.reverse_nil, List.nil_append] at h
    rw [h]
    rfl

theorem bitMachine_computes :
    bitMachine.ComputesWithin increment (fun n => 2 * (n + 1)) := by
  intro q
  simpa only [Nat.mul_add, Nat.mul_one] using bitMachine_outputs q

theorem polytime_increment : BitMachine.Polytime increment := by
  refine ⟨bitMachine, 2, 1, ?_⟩
  simpa only [pow_one] using bitMachine_computes

end EthInapproximability.CurrentPaper.SamplerMachineIncrement
