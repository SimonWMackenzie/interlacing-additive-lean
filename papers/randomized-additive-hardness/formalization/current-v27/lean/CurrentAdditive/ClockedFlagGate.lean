import EthInapproximability.CurrentPaper.FlaggedBoundedBitMachine
import EthInapproximability.CurrentPaper.BitMachineComposition

/-! A literal finite TM2 gate: a leading true bit preserves the payload;
false or missing flag clears the stack and returns the empty default. -/

namespace CurrentAdditive.ClockedFlagGate

open Turing EthInapproximability.CurrentPaper
open BitMachine BitMachineEncoding

inductive Label where
  | start | clear
  deriving DecidableEq, Fintype

def program : Label → TM2.Stmt (fun _ : Unit => Bool) Label (Option Bool)
  | .start => .pop () (fun _ b => b)
      (.branch (fun b => b.getD false) .halt (.goto (fun _ => .clear)))
  | .clear => .pop () (fun _ b => b)
      (.branch Option.isSome (.goto (fun _ => .clear)) .halt)

abbrev Config := TM2.Cfg (fun _ : Unit => Bool) Label (Option Bool)

def cfg (l : Option Label) (v : Option Bool) (w : List Bool) : Config :=
  ⟨l, v, fun _ => w⟩

def run (t : ℕ) (c : Config) : Config := ((advance program)^[t]) c

theorem run_succ (t : ℕ) (c : Config) :
    run (t+1) c = run t (advance program c) :=
  Function.iterate_succ_apply _ _ _

theorem start_true (payload : List Bool) :
    advance program (cfg (some .start) none (true :: payload)) =
      cfg none (some true) payload := by
  simp [advance, program, cfg, TM2.step, TM2.stepAux]
  funext k
  cases k
  simp

theorem start_false (payload : List Bool) :
    advance program (cfg (some .start) none (false :: payload)) =
      cfg (some .clear) (some false) payload := by
  simp [advance, program, cfg, TM2.step, TM2.stepAux]
  funext k
  cases k
  simp

theorem start_nil :
    advance program (cfg (some .start) none []) =
      cfg (some .clear) none [] := by
  simp [advance, program, cfg, TM2.step, TM2.stepAux]

theorem clear_cons (v : Option Bool) (b : Bool) (payload : List Bool) :
    advance program (cfg (some .clear) v (b :: payload)) =
      cfg (some .clear) (some b) payload := by
  simp [advance, program, cfg, TM2.step, TM2.stepAux]
  funext k
  cases k
  simp

theorem clear_nil (v : Option Bool) :
    advance program (cfg (some .clear) v []) = cfg none none [] := by
  simp [advance, program, cfg, TM2.step, TM2.stepAux]

theorem clear_run (payload : List Bool) (v : Option Bool) :
    run (payload.length+1) (cfg (some .clear) v payload) =
      cfg none none [] := by
  induction payload generalizing v with
  | nil => simpa [run] using clear_nil v
  | cons b payload ih =>
      rw [List.length_cons, run_succ, clear_cons]
      exact ih (some b)

noncomputable def machine : BitMachine.Machine :=
  ofFinite () () .start none program

theorem outputs_true (payload : List Bool) :
    machine.OutputsWithin (true :: payload) payload 1 := by
  apply outputsWithin_of_raw_run () () .start none program
    (true :: payload) payload 1 1 (Nat.le_refl _)
  · change (run 1 (cfg (some .start) none (true :: payload))).l = none
    rw [run_succ, start_true]
    rfl
  · change (run 1 (cfg (some .start) none (true :: payload))).stk () = payload
    rw [run_succ, start_true]
    rfl

theorem outputs_false (payload : List Bool) :
    machine.OutputsWithin (false :: payload) [] (payload.length+2) := by
  apply outputsWithin_of_raw_run () () .start none program
    (false :: payload) [] (payload.length+2) (payload.length+2) (Nat.le_refl _)
  · change (run (payload.length+2)
        (cfg (some .start) none (false :: payload))).l = none
    rw [show payload.length+2 = (payload.length+1)+1 by omega,
      run_succ, start_false, clear_run]
    rfl
  · change (run (payload.length+2)
        (cfg (some .start) none (false :: payload))).stk () = []
    rw [show payload.length+2 = (payload.length+1)+1 by omega,
      run_succ, start_false, clear_run]
    rfl

theorem outputs_nil : machine.OutputsWithin [] [] 2 := by
  apply outputsWithin_of_raw_run () () .start none program
    [] [] 2 2 (Nat.le_refl _)
  · change (run 2 (cfg (some .start) none [])).l = none
    rw [show (2:ℕ) = 1+1 by omega, run_succ, start_nil,
      run_succ, clear_nil]
    rfl
  · change (run 2 (cfg (some .start) none [])).stk () = []
    rw [show (2:ℕ) = 1+1 by omega, run_succ, start_nil,
      run_succ, clear_nil]
    rfl

end CurrentAdditive.ClockedFlagGate

#print axioms CurrentAdditive.ClockedFlagGate.outputs_true
#print axioms CurrentAdditive.ClockedFlagGate.outputs_false
