import EthInapproximability.CurrentPaper.BitMachineEncoding
import Mathlib.Tactic

/-!
# Source-preserving Boolean-stack copy

Source: v8 `B-effectivity-details.tex`, finite-bit data access in the explicit
materializer. This primitive copies a list without losing its source. It uses
three Boolean stacks, two instruction labels, and three control states.

The first pass reverses the source onto scratch. The second pass restores
the source and writes a second, order-preserving copy onto the output. All
work is charged in literal TM2 transitions; there is no data-valued control
register. The complete matrix controller is a separate obligation.
-/

namespace EthInapproximability.CurrentPaper.BitMachineCopy

open Turing Turing.TM2.Stmt BitMachineEncoding

inductive Label where
  | scan | restore
  deriving DecidableEq, Fintype

def program : Label → TM2.Stmt (fun _ : Fin 3 => Bool) Label (Option Bool)
  | .scan => pop 0 (fun _ b => b)
      (branch Option.isSome
        (push 2 (fun b => b.getD false) (goto (fun _ => .scan)))
        (goto (fun _ => .restore)))
  | .restore => pop 2 (fun _ b => b)
      (branch Option.isSome
        (push 0 (fun b => b.getD false)
          (push 1 (fun b => b.getD false) (goto (fun _ => .restore))))
        (load (fun _ => none) halt))

def stackContents (source target saved : List Bool) : Fin 3 → List Bool :=
  fun k => if k = 0 then source else if k = 1 then target else saved

@[simp] private theorem stack_zero (q t b : List Bool) : stackContents q t b 0 = q := rfl
@[simp] private theorem stack_one (q t b : List Bool) : stackContents q t b 1 = t := rfl
@[simp] private theorem stack_two (q t b : List Bool) : stackContents q t b 2 = b := rfl

def cfg (l : Option Label) (s : Option Bool) (q t b : List Bool) :
    TM2.Cfg (fun _ : Fin 3 => Bool) Label (Option Bool) :=
  ⟨l, s, stackContents q t b⟩

def run (n : ℕ) (c : TM2.Cfg (fun _ : Fin 3 => Bool) Label (Option Bool)) :=
  ((advance program)^[n]) c

private theorem run_succ {c d : TM2.Cfg (fun _ : Fin 3 => Bool) Label (Option Bool)}
    (h : TM2.step program c = some d) (n : ℕ) : run (n + 1) c = run n d := by
  simp only [run, Function.iterate_succ_apply, advance, h, Option.getD_some]

private theorem run_add {c d : TM2.Cfg (fun _ : Fin 3 => Bool) Label (Option Bool)}
    {m : ℕ} (h : run m c = d) (n : ℕ) : run (m + n) c = run n d := by
  rw [Nat.add_comm m n]
  simp only [run, Function.iterate_add_apply] at h ⊢
  rw [h]

private theorem step_scan_cons (s : Option Bool) (x : Bool) (q t b : List Bool) :
    TM2.step program (cfg (some .scan) s (x :: q) t b) =
      some (cfg (some .scan) (some x) q t (x :: b)) := by
  simp [TM2.step, TM2.stepAux, program, cfg]
  funext k
  fin_cases k <;> rfl

private theorem step_scan_nil (s : Option Bool) (t b : List Bool) :
    TM2.step program (cfg (some .scan) s [] t b) =
      some (cfg (some .restore) none [] t b) := by
  simp [TM2.step, TM2.stepAux, program, cfg]

private theorem step_restore_cons (s : Option Bool) (x : Bool) (q t b : List Bool) :
    TM2.step program (cfg (some .restore) s q t (x :: b)) =
      some (cfg (some .restore) (some x) (x :: q) (x :: t) b) := by
  simp [TM2.step, TM2.stepAux, program, cfg]
  funext k
  fin_cases k <;> rfl

private theorem step_restore_nil (s : Option Bool) (q t : List Bool) :
    TM2.step program (cfg (some .restore) s q t []) =
      some (cfg none none q t []) := by
  simp [TM2.step, TM2.stepAux, program, cfg]

theorem scan_correct (s : Option Bool) (q t b : List Bool) :
    run (q.length + 1) (cfg (some .scan) s q t b) =
      cfg (some .restore) none [] t (q.reverse ++ b) := by
  induction q generalizing s b with
  | nil => simpa using run_succ (step_scan_nil s t b) 0
  | cons x q ih =>
      rw [List.length_cons, run_succ (step_scan_cons s x q t b)]
      simpa [List.reverse_cons, List.append_assoc] using ih (some x) (x :: b)

theorem restore_correct (s : Option Bool) (q t b : List Bool) :
    run (b.length + 1) (cfg (some .restore) s q t b) =
      cfg none none (b.reverse ++ q) (b.reverse ++ t) [] := by
  induction b generalizing s q t with
  | nil => simpa using run_succ (step_restore_nil s q t) 0
  | cons x b ih =>
      rw [List.length_cons, run_succ (step_restore_cons s x q t b)]
      simpa [List.reverse_cons, List.append_assoc] using ih (some x) (x :: q) (x :: t)

/-- Source and target may be arbitrary lists. The source is restored exactly,
the copy is prepended to the old target, and the scratch stack is cleared. -/
theorem run_correct (s : Option Bool) (source target : List Bool) :
    run (2 * source.length + 2) (cfg (some .scan) s source target []) =
      cfg none none source (source ++ target) [] := by
  have hs := scan_correct s source target []
  simp only [List.append_nil] at hs
  have hr := restore_correct none [] target source.reverse
  simp only [List.length_reverse, List.reverse_reverse, List.append_nil] at hr
  have h := (run_add hs (source.length + 1)).trans hr
  simpa only [Nat.two_mul, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h

noncomputable def bitMachine : BitMachine.Machine :=
  ofFinite (0 : Fin 3) 1 .scan (none : Option Bool) program

private theorem initial_eq (q : List Bool) :
    rawInit (0 : Fin 3) .scan (none : Option Bool) q = cfg (some .scan) none q [] [] := by
  unfold rawInit cfg
  congr 1
  funext k
  fin_cases k <;> rfl

theorem bitMachine_outputs (q : List Bool) :
    bitMachine.OutputsWithin q q (2 * q.length + 2) := by
  apply outputsWithin_of_raw_run (0 : Fin 3) 1 .scan (none : Option Bool) program
    q q (2 * q.length + 2) _ le_rfl
  · change (run (2 * q.length + 2) _).l = none
    rw [initial_eq, run_correct]
    rfl
  · change (run (2 * q.length + 2) _).stk 1 = q
    rw [initial_eq, run_correct]
    simp [cfg]

/-- The finite relabelling preserves the exact entire end configuration,
including the source copy that `OutputsWithin` alone does not mention. -/
theorem bitMachine_run (q : List Bool) :
    bitMachine.run (2 * q.length + 2) (bitMachine.init q) =
      renameCfg (Fintype.equivFin (Fin 3)) (Fintype.equivFin Label)
        (Fintype.equivFin (Option Bool)) (cfg none none q q []) := by
  have hi := ofFinite_init (0 : Fin 3) 1 .scan (none : Option Bool) program q
  have hr := ofFinite_run (0 : Fin 3) 1 .scan (none : Option Bool) program
    (rawInit (0 : Fin 3) .scan (none : Option Bool) q) (2 * q.length + 2)
  have h := (congrArg (bitMachine.run (2 * q.length + 2)) hi).trans hr
  have hraw := run_correct none q []
  simp only [run, List.append_nil] at hraw
  rw [initial_eq, hraw] at h
  exact h

theorem bitMachine_computes : bitMachine.ComputesWithin id (fun n => 2 * (n + 1)) := by
  intro q
  simpa only [id_eq, Nat.mul_add, Nat.mul_one] using bitMachine_outputs q

theorem polytime_copy : BitMachine.Polytime (id : List Bool → List Bool) := by
  refine ⟨bitMachine, 2, 1, ?_⟩
  simpa only [pow_one] using bitMachine_computes

end EthInapproximability.CurrentPaper.BitMachineCopy
