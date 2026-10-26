import CurrentAdditive.TrialInputPrepBridge
import CurrentAdditive.TrialCounterMachine

/-!
Physical outer controller for a trial search. The twelve Boolean stacks are:
0 candidate tail, 1 divisor tail, 2 unary shift, 3--7 reserved for the
prepared divider/test, 8 remaining divisor degrees, 9 completed degrees,
10 consumed shifts, and 11 controller scratch. Candidate and divisor tails
are low-first binary words. A test callback resumes at `afterTest` with its
nonzero-remainder result in the first finite-control bit. The controller's
`test` label is its explicit callback boundary, not an oracle instruction.
The final proof that the callback is the physical divider/zero scan requires
composition with those separately checked programs.
-/

namespace CurrentAdditive.FieldMachineHelper.TrialSearchControllerMachine

open Turing Turing.TM2.Stmt
open EthInapproximability.CurrentPaper.BitMachineEncoding

inductive Label where
  | initial | test | afterTest
  | divScan | divRestore | degreePop | degreePeek
  | shiftDecrement | extendScan | extendRestore
  | candidateScan | candidateRestore
  | resetDiv | resetDegrees | resetShift
  | success | exhausted
  deriving DecidableEq, Fintype

abbrev Control := Bool × Bool × Option Bool
abbrev Config := TM2.Cfg (fun _ : Fin 12 => Bool) Label Control

def program : Label → TM2.Stmt (fun _ : Fin 12 => Bool) Label Control
  | .initial => peek 8 (fun s b => (s.1, s.2.1, b))
      (branch (fun s => s.2.2.isSome)
        (goto (fun _ => .test)) (goto (fun _ => .success)))
  | .test => halt
  | .afterTest => load (fun s => (s.1, true, none))
      (branch (fun s => s.1)
        (goto (fun _ => .divScan)) (goto (fun _ => .candidateScan)))
  | .divScan => pop 1 (fun s b => (s.1, s.2.1, b))
      (branch (fun s => s.2.2.isSome)
        (push 11 (fun s => s.2.2.getD false ^^ s.2.1)
          (load (fun s => (s.1, s.2.1 && s.2.2.getD false, none))
            (goto (fun _ => .divScan))))
        (goto (fun _ => .divRestore)))
  | .divRestore => pop 11 (fun s b => (s.1, s.2.1, b))
      (branch (fun s => s.2.2.isSome)
        (push 1 (fun s => s.2.2.getD false)
          (goto (fun _ => .divRestore)))
        (branch (fun s => s.2.1)
          (goto (fun _ => .degreePop)) (goto (fun _ => .test))))
  | .degreePop => pop 8 (fun s b => (s.1, s.2.1, b))
      (branch (fun s => s.2.2.isSome)
        (load (fun s => (s.1, s.2.1, none)) (goto (fun _ => .degreePeek)))
        (goto (fun _ => .success)))
  | .degreePeek => peek 8 (fun s b => (s.1, s.2.1, b))
      (branch (fun s => s.2.2.isSome)
        (push 9 (fun _ => true)
          (load (fun s => (s.1, s.2.1, none))
            (goto (fun _ => .shiftDecrement))))
        (goto (fun _ => .success)))
  | .shiftDecrement => pop 2 (fun s b => (s.1, s.2.1, b))
      (push 10 (fun _ => true)
        (load (fun s => (s.1, s.2.1, none))
          (goto (fun _ => .extendScan))))
  | .extendScan => pop 1 (fun s b => (s.1, s.2.1, b))
      (branch (fun s => s.2.2.isSome)
        (push 11 (fun s => s.2.2.getD false)
          (goto (fun _ => .extendScan)))
        (push 1 (fun _ => false) (goto (fun _ => .extendRestore))))
  | .extendRestore => pop 11 (fun s b => (s.1, s.2.1, b))
      (branch (fun s => s.2.2.isSome)
        (push 1 (fun s => s.2.2.getD false)
          (goto (fun _ => .extendRestore)))
        (goto (fun _ => .test)))
  | .candidateScan => pop 0 (fun s b => (s.1, s.2.1, b))
      (branch (fun s => s.2.2.isSome)
        (push 11 (fun s => s.2.2.getD false ^^ s.2.1)
          (load (fun s => (s.1, s.2.1 && s.2.2.getD false, none))
            (goto (fun _ => .candidateScan))))
        (goto (fun _ => .candidateRestore)))
  | .candidateRestore => pop 11 (fun s b => (s.1, s.2.1, b))
      (branch (fun s => s.2.2.isSome)
        (push 0 (fun s => s.2.2.getD false)
          (goto (fun _ => .candidateRestore)))
        (branch (fun s => s.2.1)
          (goto (fun _ => .exhausted)) (goto (fun _ => .resetDiv))))
  | .resetDiv => pop 1 (fun s b => (s.1, s.2.1, b))
      (branch (fun s => s.2.2.isSome)
        (goto (fun _ => .resetDiv))
        (push 1 (fun _ => false) (goto (fun _ => .resetDegrees))))
  | .resetDegrees => pop 9 (fun s b => (s.1, s.2.1, b))
      (branch (fun s => s.2.2.isSome)
        (push 8 (fun _ => true) (goto (fun _ => .resetDegrees)))
        (goto (fun _ => .resetShift)))
  | .resetShift => pop 10 (fun s b => (s.1, s.2.1, b))
      (branch (fun s => s.2.2.isSome)
        (push 2 (fun _ => true) (goto (fun _ => .resetShift)))
        (goto (fun _ => .test)))
  | .success => halt
  | .exhausted => halt

def bank (candidate divisor shift : List Bool)
    (physical : Fin 5 → List Bool)
    (remaining used consumed scratch : List Bool) : Fin 12 → List Bool :=
  fun k => if h : k.val < 3 then
    (fun j : Fin 3 => if j = 0 then candidate else if j = 1 then divisor else shift)
      ⟨k.val, h⟩
  else if h : k.val < 8 then physical ⟨k.val - 3, by omega⟩
  else if k = 8 then remaining else if k = 9 then used else
    if k = 10 then consumed else scratch

def cfg (l : Option Label) (s : Control)
    (candidate divisor shift : List Bool)
    (physical : Fin 5 → List Bool)
    (remaining used consumed scratch : List Bool) : Config :=
  ⟨l, s, bank candidate divisor shift physical remaining used consumed scratch⟩

def run (t : Nat) (q : Config) : Config := ((advance program)^[t]) q

private theorem run_succ {c e : Config} (h : TM2.step program c = some e)
    (t : Nat) : run (t + 1) c = run t e := by
  simp only [run, Function.iterate_succ_apply, advance, h, Option.getD_some]

theorem run_add (t u : Nat) (q : Config) :
    run (t + u) q = run u (run t q) := by
  rw [Nat.add_comm t u]
  simp only [run, Function.iterate_add_apply]

theorem step_afterTest_pass (candidate divisor shift : List Bool)
    (physical : Fin 5 → List Bool) (remaining used consumed scratch : List Bool)
    (carry : Bool) (bit : Option Bool) :
    TM2.step program
      (cfg (some .afterTest) (true, carry, bit) candidate divisor shift
        physical remaining used consumed scratch) =
    some (cfg (some .divScan) (true, true, none) candidate divisor shift
      physical remaining used consumed scratch) := by
  simp [TM2.step, TM2.stepAux, program, cfg]

theorem step_afterTest_fail (candidate divisor shift : List Bool)
    (physical : Fin 5 → List Bool) (remaining used consumed scratch : List Bool)
    (carry : Bool) (bit : Option Bool) :
    TM2.step program
      (cfg (some .afterTest) (false, carry, bit) candidate divisor shift
        physical remaining used consumed scratch) =
    some (cfg (some .candidateScan) (false, true, none) candidate divisor shift
      physical remaining used consumed scratch) := by
  simp [TM2.step, TM2.stepAux, program, cfg]

private theorem step_divScan_cons (passed carry bit : Bool)
    (candidate divisor shift : List Bool)
    (physical : Fin 5 → List Bool) (remaining used consumed scratch : List Bool) :
    TM2.step program
      (cfg (some .divScan) (passed, carry, none) candidate (bit :: divisor)
        shift physical remaining used consumed scratch) =
    some (cfg (some .divScan) (passed, carry && bit, none) candidate divisor
      shift physical remaining used consumed ((bit ^^ carry) :: scratch)) := by
  simp [TM2.step, TM2.stepAux, program, cfg, bank]
  funext k
  fin_cases k <;> rfl

private theorem step_divScan_nil (passed carry : Bool)
    (candidate shift : List Bool) (physical : Fin 5 → List Bool)
    (remaining used consumed scratch : List Bool) :
    TM2.step program
      (cfg (some .divScan) (passed, carry, none) candidate [] shift
        physical remaining used consumed scratch) =
    some (cfg (some .divRestore) (passed, carry, none) candidate [] shift
      physical remaining used consumed scratch) := by
  simp [TM2.step, TM2.stepAux, program, cfg, bank]

private theorem step_divRestore_cons (passed carry bit : Bool)
    (candidate divisor shift : List Bool) (physical : Fin 5 → List Bool)
    (remaining used consumed scratch : List Bool) :
    TM2.step program
      (cfg (some .divRestore) (passed, carry, none) candidate divisor shift
        physical remaining used consumed (bit :: scratch)) =
    some (cfg (some .divRestore) (passed, carry, some bit) candidate
      (bit :: divisor) shift physical remaining used consumed scratch) := by
  simp [TM2.step, TM2.stepAux, program, cfg, bank]
  funext k
  fin_cases k <;> rfl

private theorem step_divRestore_nil (passed carry : Bool)
    (candidate divisor shift : List Bool) (physical : Fin 5 → List Bool)
    (remaining used consumed : List Bool) :
    TM2.step program
      (cfg (some .divRestore) (passed, carry, none) candidate divisor shift
        physical remaining used consumed []) =
    some (cfg (some (if carry then .degreePop else .test))
      (passed, carry, none) candidate divisor shift
        physical remaining used consumed []) := by
  cases carry <;> simp [TM2.step, TM2.stepAux, program, cfg, bank]

open CurrentAdditive.FieldMachineHelper.TrialCounterMachine
  (incrementAux counterWord counterWord_length)

private theorem divScan_run (passed carry : Bool)
    (candidate divisor shift : List Bool) (physical : Fin 5 → List Bool)
    (remaining used consumed scratch : List Bool) :
    run (divisor.length + 1)
      (cfg (some .divScan) (passed, carry, none) candidate divisor shift
        physical remaining used consumed scratch) =
    cfg (some .divRestore) (passed, (incrementAux carry divisor).1, none)
      candidate [] shift physical remaining used consumed
      ((incrementAux carry divisor).2.reverse ++ scratch) := by
  induction divisor generalizing carry scratch with
  | nil =>
    simpa [incrementAux] using
      run_succ (step_divScan_nil passed carry candidate shift physical
        remaining used consumed scratch) 0
  | cons bit rest ih =>
    rw [List.length_cons,
      run_succ (step_divScan_cons passed carry bit candidate rest shift
        physical remaining used consumed scratch)]
    simpa [incrementAux, List.reverse_cons, List.append_assoc] using
      ih (carry && bit) ((bit ^^ carry) :: scratch)

private theorem divRestore_run (passed carry : Bool)
    (candidate divisor shift : List Bool) (physical : Fin 5 → List Bool)
    (remaining used consumed scratch : List Bool) :
    run (scratch.length + 1)
      (cfg (some .divRestore) (passed, carry, none) candidate divisor shift
        physical remaining used consumed scratch) =
    cfg (some (if carry then .degreePop else .test)) (passed, carry, none)
      candidate (scratch.reverse ++ divisor) shift physical
      remaining used consumed [] := by
  induction scratch generalizing divisor with
  | nil =>
    simpa using run_succ
      (step_divRestore_nil passed carry candidate divisor shift physical
        remaining used consumed) 0
  | cons bit rest ih =>
    rw [List.length_cons,
      run_succ (step_divRestore_cons passed carry bit candidate divisor shift
        physical remaining used consumed rest)]
    simpa [List.reverse_cons, List.append_assoc] using ih (bit :: divisor)

private theorem incrementAux_length (carry : Bool) (word : List Bool) :
    (incrementAux carry word).2.length = word.length := by
  induction word generalizing carry with
  | nil => rfl
  | cons bit rest ih => simp [incrementAux, ih]

theorem run_divisor_increment (passed : Bool)
    (candidate divisor shift : List Bool) (physical : Fin 5 → List Bool)
    (remaining used consumed : List Bool) :
    run (2 * divisor.length + 2)
      (cfg (some .divScan) (passed, true, none) candidate divisor shift
        physical remaining used consumed []) =
    cfg (some (if (incrementAux true divisor).1 then .degreePop else .test))
      (passed, (incrementAux true divisor).1, none)
      candidate (incrementAux true divisor).2 shift physical
      remaining used consumed [] := by
  have hs := divScan_run passed true candidate divisor shift physical
    remaining used consumed []
  have hr := divRestore_run passed (incrementAux true divisor).1
    candidate [] shift physical remaining used consumed
    (incrementAux true divisor).2.reverse
  have hlen : (incrementAux true divisor).2.length = divisor.length :=
    incrementAux_length true divisor
  have hclock : 2 * divisor.length + 2 =
      (divisor.length + 1) + ((incrementAux true divisor).2.reverse.length + 1) := by
    simp [hlen]; omega
  rw [hclock, run_add, hs]
  simpa using hr

#print axioms run_divisor_increment

private theorem step_candidateScan_cons (passed carry bit : Bool)
    (candidate divisor shift : List Bool) (physical : Fin 5 → List Bool)
    (remaining used consumed scratch : List Bool) :
    TM2.step program
      (cfg (some .candidateScan) (passed, carry, none) (bit :: candidate)
        divisor shift physical remaining used consumed scratch) =
    some (cfg (some .candidateScan) (passed, carry && bit, none) candidate
      divisor shift physical remaining used consumed ((bit ^^ carry) :: scratch)) := by
  simp [TM2.step, TM2.stepAux, program, cfg, bank]
  funext k
  fin_cases k <;> rfl

private theorem step_candidateScan_nil (passed carry : Bool)
    (divisor shift : List Bool) (physical : Fin 5 → List Bool)
    (remaining used consumed scratch : List Bool) :
    TM2.step program
      (cfg (some .candidateScan) (passed, carry, none) [] divisor shift
        physical remaining used consumed scratch) =
    some (cfg (some .candidateRestore) (passed, carry, none) [] divisor shift
      physical remaining used consumed scratch) := by
  simp [TM2.step, TM2.stepAux, program, cfg, bank]

private theorem step_candidateRestore_cons (passed carry bit : Bool)
    (candidate divisor shift : List Bool) (physical : Fin 5 → List Bool)
    (remaining used consumed scratch : List Bool) :
    TM2.step program
      (cfg (some .candidateRestore) (passed, carry, none) candidate divisor
        shift physical remaining used consumed (bit :: scratch)) =
    some (cfg (some .candidateRestore) (passed, carry, some bit)
      (bit :: candidate) divisor shift physical remaining used consumed scratch) := by
  simp [TM2.step, TM2.stepAux, program, cfg, bank]
  funext k
  fin_cases k <;> rfl

private theorem step_candidateRestore_nil (passed carry : Bool)
    (candidate divisor shift : List Bool) (physical : Fin 5 → List Bool)
    (remaining used consumed : List Bool) :
    TM2.step program
      (cfg (some .candidateRestore) (passed, carry, none) candidate divisor
        shift physical remaining used consumed []) =
    some (cfg (some (if carry then .exhausted else .resetDiv))
      (passed, carry, none) candidate divisor shift physical
      remaining used consumed []) := by
  cases carry <;> simp [TM2.step, TM2.stepAux, program, cfg, bank]

private theorem candidateScan_run (passed carry : Bool)
    (candidate divisor shift : List Bool) (physical : Fin 5 → List Bool)
    (remaining used consumed scratch : List Bool) :
    run (candidate.length + 1)
      (cfg (some .candidateScan) (passed, carry, none) candidate divisor shift
        physical remaining used consumed scratch) =
    cfg (some .candidateRestore) (passed, (incrementAux carry candidate).1, none)
      [] divisor shift physical remaining used consumed
      ((incrementAux carry candidate).2.reverse ++ scratch) := by
  induction candidate generalizing carry scratch with
  | nil =>
    simpa [incrementAux] using
      run_succ (step_candidateScan_nil passed carry divisor shift physical
        remaining used consumed scratch) 0
  | cons bit rest ih =>
    rw [List.length_cons,
      run_succ (step_candidateScan_cons passed carry bit rest divisor shift
        physical remaining used consumed scratch)]
    simpa [incrementAux, List.reverse_cons, List.append_assoc] using
      ih (carry && bit) ((bit ^^ carry) :: scratch)

private theorem candidateRestore_run (passed carry : Bool)
    (candidate divisor shift : List Bool) (physical : Fin 5 → List Bool)
    (remaining used consumed scratch : List Bool) :
    run (scratch.length + 1)
      (cfg (some .candidateRestore) (passed, carry, none) candidate divisor shift
        physical remaining used consumed scratch) =
    cfg (some (if carry then .exhausted else .resetDiv)) (passed, carry, none)
      (scratch.reverse ++ candidate) divisor shift physical
      remaining used consumed [] := by
  induction scratch generalizing candidate with
  | nil =>
    simpa using run_succ
      (step_candidateRestore_nil passed carry candidate divisor shift physical
        remaining used consumed) 0
  | cons bit rest ih =>
    rw [List.length_cons,
      run_succ (step_candidateRestore_cons passed carry bit candidate divisor shift
        physical remaining used consumed rest)]
    simpa [List.reverse_cons, List.append_assoc] using ih (bit :: candidate)

theorem run_candidate_increment (passed : Bool)
    (candidate divisor shift : List Bool) (physical : Fin 5 → List Bool)
    (remaining used consumed : List Bool) :
    run (2 * candidate.length + 2)
      (cfg (some .candidateScan) (passed, true, none) candidate divisor shift
        physical remaining used consumed []) =
    cfg (some (if (incrementAux true candidate).1 then .exhausted else .resetDiv))
      (passed, (incrementAux true candidate).1, none)
      (incrementAux true candidate).2 divisor shift physical
      remaining used consumed [] := by
  have hs := candidateScan_run passed true candidate divisor shift physical
    remaining used consumed []
  have hr := candidateRestore_run passed (incrementAux true candidate).1
    [] divisor shift physical remaining used consumed
    (incrementAux true candidate).2.reverse
  have hlen := incrementAux_length true candidate
  have hclock : 2 * candidate.length + 2 =
      (candidate.length + 1) + ((incrementAux true candidate).2.reverse.length + 1) := by
    simp [hlen]; omega
  rw [hclock, run_add, hs]
  simpa using hr

#print axioms run_candidate_increment

private theorem step_resetDiv_cons (passed carry bit : Bool)
    (candidate divisor shift : List Bool) (physical : Fin 5 → List Bool)
    (remaining used consumed : List Bool) :
    TM2.step program
      (cfg (some .resetDiv) (passed, carry, none) candidate (bit :: divisor)
        shift physical remaining used consumed []) =
    some (cfg (some .resetDiv) (passed, carry, some bit) candidate divisor
      shift physical remaining used consumed []) := by
  simp [TM2.step, TM2.stepAux, program, cfg, bank]
  funext k
  fin_cases k <;> rfl

private theorem step_resetDiv_nil (passed carry : Bool)
    (candidate shift : List Bool) (physical : Fin 5 → List Bool)
    (remaining used consumed : List Bool) :
    TM2.step program
      (cfg (some .resetDiv) (passed, carry, none) candidate [] shift
        physical remaining used consumed []) =
    some (cfg (some .resetDegrees) (passed, carry, none) candidate [false]
      shift physical remaining used consumed []) := by
  simp [TM2.step, TM2.stepAux, program, cfg, bank]
  funext k
  fin_cases k <;> rfl

theorem resetDiv_run (passed carry : Bool)
    (candidate divisor shift : List Bool) (physical : Fin 5 → List Bool)
    (remaining used consumed : List Bool) :
    run (divisor.length + 1)
      (cfg (some .resetDiv) (passed, carry, none) candidate divisor shift
        physical remaining used consumed []) =
    cfg (some .resetDegrees) (passed, carry, none) candidate [false] shift
      physical remaining used consumed [] := by
  induction divisor with
  | nil =>
    simpa using run_succ
      (step_resetDiv_nil passed carry candidate shift physical
        remaining used consumed) 0
  | cons bit rest ih =>
    rw [List.length_cons,
      run_succ (step_resetDiv_cons passed carry bit candidate rest shift
        physical remaining used consumed)]
    exact ih

private theorem step_resetDegrees_cons (passed carry bit : Bool)
    (candidate divisor shift : List Bool) (physical : Fin 5 → List Bool)
    (remaining used consumed : List Bool) :
    TM2.step program
      (cfg (some .resetDegrees) (passed, carry, none) candidate divisor shift
        physical remaining (bit :: used) consumed []) =
    some (cfg (some .resetDegrees) (passed, carry, some bit) candidate divisor
      shift physical (true :: remaining) used consumed []) := by
  simp [TM2.step, TM2.stepAux, program, cfg, bank]
  funext k
  fin_cases k <;> rfl

private theorem step_resetDegrees_nil (passed carry : Bool)
    (candidate divisor shift : List Bool) (physical : Fin 5 → List Bool)
    (remaining consumed : List Bool) :
    TM2.step program
      (cfg (some .resetDegrees) (passed, carry, none) candidate divisor shift
        physical remaining [] consumed []) =
    some (cfg (some .resetShift) (passed, carry, none) candidate divisor shift
      physical remaining [] consumed []) := by
  simp [TM2.step, TM2.stepAux, program, cfg, bank]

theorem resetDegrees_run (passed carry : Bool)
    (candidate divisor shift : List Bool) (physical : Fin 5 → List Bool)
    (remaining used consumed : List Bool) :
    run (used.length + 1)
      (cfg (some .resetDegrees) (passed, carry, none) candidate divisor shift
        physical remaining used consumed []) =
    cfg (some .resetShift) (passed, carry, none) candidate divisor shift
      physical (List.replicate used.length true ++ remaining) [] consumed [] := by
  induction used generalizing remaining with
  | nil =>
    simpa using run_succ
      (step_resetDegrees_nil passed carry candidate divisor shift physical
        remaining consumed) 0
  | cons bit rest ih =>
    rw [List.length_cons,
      run_succ (step_resetDegrees_cons passed carry bit candidate divisor shift
        physical remaining rest consumed)]
    simpa [List.replicate_succ', List.append_assoc] using ih (true :: remaining)

private theorem step_resetShift_cons (passed carry bit : Bool)
    (candidate divisor shift : List Bool) (physical : Fin 5 → List Bool)
    (remaining used consumed : List Bool) :
    TM2.step program
      (cfg (some .resetShift) (passed, carry, none) candidate divisor shift
        physical remaining used (bit :: consumed) []) =
    some (cfg (some .resetShift) (passed, carry, some bit) candidate divisor
      (true :: shift) physical remaining used consumed []) := by
  simp [TM2.step, TM2.stepAux, program, cfg, bank]
  funext k
  fin_cases k <;> rfl

private theorem step_resetShift_nil (passed carry : Bool)
    (candidate divisor shift : List Bool) (physical : Fin 5 → List Bool)
    (remaining used : List Bool) :
    TM2.step program
      (cfg (some .resetShift) (passed, carry, none) candidate divisor shift
        physical remaining used [] []) =
    some (cfg (some .test) (passed, carry, none) candidate divisor shift
      physical remaining used [] []) := by
  simp [TM2.step, TM2.stepAux, program, cfg, bank]

theorem resetShift_run (passed carry : Bool)
    (candidate divisor shift : List Bool) (physical : Fin 5 → List Bool)
    (remaining used consumed : List Bool) :
    run (consumed.length + 1)
      (cfg (some .resetShift) (passed, carry, none) candidate divisor shift
        physical remaining used consumed []) =
    cfg (some .test) (passed, carry, none) candidate divisor
      (List.replicate consumed.length true ++ shift)
      physical remaining used [] [] := by
  induction consumed generalizing shift with
  | nil =>
    simpa using run_succ
      (step_resetShift_nil passed carry candidate divisor shift physical
        remaining used) 0
  | cons bit rest ih =>
    rw [List.length_cons,
      run_succ (step_resetShift_cons passed carry bit candidate divisor shift
        physical remaining used rest)]
    simpa [List.replicate_succ', List.append_assoc] using ih (true :: shift)

theorem run_reset_after_failed_candidate (carry : Bool)
    (candidate divisor shift : List Bool) (physical : Fin 5 → List Bool)
    (remaining used consumed : List Bool) :
    run (divisor.length + used.length + consumed.length + 3)
      (cfg (some .resetDiv) (false, carry, none) candidate divisor shift
        physical remaining used consumed []) =
    cfg (some .test) (false, carry, none) candidate [false]
      (List.replicate consumed.length true ++ shift)
      physical (List.replicate used.length true ++ remaining) [] [] [] := by
  have hd := resetDiv_run false carry candidate divisor shift physical
    remaining used consumed
  have hu := resetDegrees_run false carry candidate [false] shift physical
    remaining used consumed
  have hs := resetShift_run false carry candidate [false] shift physical
    (List.replicate used.length true ++ remaining) [] consumed
  have hclock : divisor.length + used.length + consumed.length + 3 =
      (divisor.length + 1) + (used.length + 1) + (consumed.length + 1) := by omega
  rw [hclock]
  rw [run_add ((divisor.length + 1) + (used.length + 1)) (consumed.length + 1)]
  rw [run_add (divisor.length + 1) (used.length + 1)]
  rw [hd, hu]
  exact hs

#print axioms run_reset_after_failed_candidate

private theorem step_degreePop_cons (passed carry bit : Bool)
    (candidate divisor shift : List Bool) (physical : Fin 5 → List Bool)
    (remaining used consumed : List Bool) :
    TM2.step program
      (cfg (some .degreePop) (passed, carry, none) candidate divisor shift
        physical (bit :: remaining) used consumed []) =
    some (cfg (some .degreePeek) (passed, carry, none) candidate divisor
      shift physical remaining used consumed []) := by
  simp [TM2.step, TM2.stepAux, program, cfg, bank]
  funext k
  fin_cases k <;> rfl

private theorem step_degreePeek_cons (passed carry bit : Bool)
    (candidate divisor shift : List Bool) (physical : Fin 5 → List Bool)
    (remaining used consumed : List Bool) :
    TM2.step program
      (cfg (some .degreePeek) (passed, carry, none) candidate divisor shift
        physical (bit :: remaining) used consumed []) =
    some (cfg (some .shiftDecrement) (passed, carry, none) candidate divisor
      shift physical (bit :: remaining) (true :: used) consumed []) := by
  simp [TM2.step, TM2.stepAux, program, cfg, bank]
  funext k
  fin_cases k <;> rfl

private theorem step_shiftDecrement_cons (passed carry bit : Bool)
    (candidate divisor shift : List Bool) (physical : Fin 5 → List Bool)
    (remaining used consumed : List Bool) :
    TM2.step program
      (cfg (some .shiftDecrement) (passed, carry, none) candidate divisor
        (bit :: shift) physical remaining used consumed []) =
    some (cfg (some .extendScan) (passed, carry, none) candidate divisor
      shift physical remaining used (true :: consumed) []) := by
  simp [TM2.step, TM2.stepAux, program, cfg, bank]
  funext k
  fin_cases k <;> rfl

private theorem step_extendScan_cons (passed carry bit : Bool)
    (candidate divisor shift : List Bool) (physical : Fin 5 → List Bool)
    (remaining used consumed scratch : List Bool) :
    TM2.step program
      (cfg (some .extendScan) (passed, carry, none) candidate (bit :: divisor)
        shift physical remaining used consumed scratch) =
    some (cfg (some .extendScan) (passed, carry, some bit) candidate divisor
      shift physical remaining used consumed (bit :: scratch)) := by
  simp [TM2.step, TM2.stepAux, program, cfg, bank]
  funext k
  fin_cases k <;> rfl

private theorem step_extendScan_nil (passed carry : Bool)
    (candidate shift : List Bool) (physical : Fin 5 → List Bool)
    (remaining used consumed scratch : List Bool) :
    TM2.step program
      (cfg (some .extendScan) (passed, carry, none) candidate [] shift
        physical remaining used consumed scratch) =
    some (cfg (some .extendRestore) (passed, carry, none) candidate [false]
      shift physical remaining used consumed scratch) := by
  simp [TM2.step, TM2.stepAux, program, cfg, bank]
  funext k
  fin_cases k <;> rfl

private theorem extendScan_run (passed carry : Bool)
    (candidate divisor shift : List Bool) (physical : Fin 5 → List Bool)
    (remaining used consumed scratch : List Bool) :
    run (divisor.length + 1)
      (cfg (some .extendScan) (passed, carry, none) candidate divisor shift
        physical remaining used consumed scratch) =
    cfg (some .extendRestore) (passed, carry, none) candidate [false] shift
      physical remaining used consumed (divisor.reverse ++ scratch) := by
  induction divisor generalizing scratch with
  | nil =>
    simpa using run_succ
      (step_extendScan_nil passed carry candidate shift physical
        remaining used consumed scratch) 0
  | cons bit rest ih =>
    rw [List.length_cons,
      run_succ (step_extendScan_cons passed carry bit candidate rest shift
        physical remaining used consumed scratch)]
    simpa [List.reverse_cons, List.append_assoc] using ih (bit :: scratch)

private theorem step_extendRestore_cons (passed carry bit : Bool)
    (candidate divisor shift : List Bool) (physical : Fin 5 → List Bool)
    (remaining used consumed scratch : List Bool) :
    TM2.step program
      (cfg (some .extendRestore) (passed, carry, none) candidate divisor shift
        physical remaining used consumed (bit :: scratch)) =
    some (cfg (some .extendRestore) (passed, carry, some bit) candidate
      (bit :: divisor) shift physical remaining used consumed scratch) := by
  simp [TM2.step, TM2.stepAux, program, cfg, bank]
  funext k
  fin_cases k <;> rfl

private theorem step_extendRestore_nil (passed carry : Bool)
    (candidate divisor shift : List Bool) (physical : Fin 5 → List Bool)
    (remaining used consumed : List Bool) :
    TM2.step program
      (cfg (some .extendRestore) (passed, carry, none) candidate divisor shift
        physical remaining used consumed []) =
    some (cfg (some .test) (passed, carry, none) candidate divisor shift
      physical remaining used consumed []) := by
  simp [TM2.step, TM2.stepAux, program, cfg, bank]

private theorem extendRestore_run (passed carry : Bool)
    (candidate divisor shift : List Bool) (physical : Fin 5 → List Bool)
    (remaining used consumed scratch : List Bool) :
    run (scratch.length + 1)
      (cfg (some .extendRestore) (passed, carry, none) candidate divisor shift
        physical remaining used consumed scratch) =
    cfg (some .test) (passed, carry, none) candidate
      (scratch.reverse ++ divisor) shift physical remaining used consumed [] := by
  induction scratch generalizing divisor with
  | nil =>
    simpa using run_succ
      (step_extendRestore_nil passed carry candidate divisor shift physical
        remaining used consumed) 0
  | cons bit rest ih =>
    rw [List.length_cons,
      run_succ (step_extendRestore_cons passed carry bit candidate divisor shift
        physical remaining used consumed rest)]
    simpa [List.reverse_cons, List.append_assoc] using ih (bit :: divisor)

theorem extendDivisor_run (passed carry : Bool)
    (candidate divisor shift : List Bool) (physical : Fin 5 → List Bool)
    (remaining used consumed : List Bool) :
    run (2 * divisor.length + 2)
      (cfg (some .extendScan) (passed, carry, none) candidate divisor shift
        physical remaining used consumed []) =
    cfg (some .test) (passed, carry, none) candidate
      (divisor ++ [false]) shift physical remaining used consumed [] := by
  have hs := extendScan_run passed carry candidate divisor shift physical
    remaining used consumed []
  have hr := extendRestore_run passed carry candidate [false] shift physical
    remaining used consumed divisor.reverse
  have hclock : 2 * divisor.length + 2 =
      (divisor.length + 1) + (divisor.reverse.length + 1) := by simp; omega
  rw [hclock, run_add, hs]
  simpa [List.append_assoc] using hr

theorem run_next_degree (passed carry : Bool)
    (candidate divisor shift : List Bool) (physical : Fin 5 → List Bool)
    (remaining used consumed : List Bool) :
    run (2 * divisor.length + 5)
      (cfg (some .degreePop) (passed, carry, none) candidate divisor
        (true :: shift) physical (true :: true :: remaining) used consumed []) =
    cfg (some .test) (passed, carry, none) candidate
      (divisor ++ [false]) shift physical (true :: remaining)
      (true :: used) (true :: consumed) [] := by
  have h1 := step_degreePop_cons passed carry true candidate divisor
    (true :: shift) physical (true :: remaining) used consumed
  have h2 := step_degreePeek_cons passed carry true candidate divisor
    (true :: shift) physical remaining used consumed
  have h3 := step_shiftDecrement_cons passed carry true candidate divisor
    shift physical (true :: remaining) (true :: used) consumed
  have h4 := extendDivisor_run passed carry candidate divisor shift physical
    (true :: remaining) (true :: used) (true :: consumed)
  have hclock : 2 * divisor.length + 5 = 1 + 1 + 1 + (2 * divisor.length + 2) := by omega
  rw [hclock]
  rw [run_add (1 + 1 + 1) (2 * divisor.length + 2)]
  rw [run_add (1 + 1) 1]
  rw [run_add 1 1]
  rw [run_succ h1 0]
  simp only [show ∀ q : Config, run 0 q = q from fun _ => rfl]
  rw [run_succ h2 0]
  simp only [show ∀ q : Config, run 0 q = q from fun _ => rfl]
  rw [run_succ h3 0]
  simp only [show ∀ q : Config, run 0 q = q from fun _ => rfl]
  exact h4

#print axioms run_next_degree

theorem run_after_passing_nonlast_divisor
    (candidate divisor shift : List Bool) (physical : Fin 5 → List Bool)
    (remaining used consumed : List Bool)
    (carry : Bool) (bit : Option Bool)
    (hnext : (incrementAux true divisor).1 = false) :
    run (2 * divisor.length + 3)
      (cfg (some .afterTest) (true, carry, bit) candidate divisor shift
        physical remaining used consumed []) =
    cfg (some .test) (true, false, none) candidate
      (incrementAux true divisor).2 shift physical remaining used consumed [] := by
  have h1 := step_afterTest_pass candidate divisor shift physical
    remaining used consumed [] carry bit
  have h2 := run_divisor_increment true candidate divisor shift physical
    remaining used consumed
  have hclock : 2 * divisor.length + 3 = 1 + (2 * divisor.length + 2) := by omega
  rw [hclock, run_add, run_succ h1 0]
  simpa [hnext] using h2

theorem run_after_passing_last_divisor_next_degree
    (candidate divisor shift : List Bool) (physical : Fin 5 → List Bool)
    (remaining used consumed : List Bool)
    (carry : Bool) (bit : Option Bool)
    (hlast : (incrementAux true divisor).1 = true) :
    run (4 * divisor.length + 8)
      (cfg (some .afterTest) (true, carry, bit) candidate divisor
        (true :: shift) physical (true :: true :: remaining) used consumed []) =
    cfg (some .test) (true, true, none) candidate
      ((incrementAux true divisor).2 ++ [false]) shift physical
      (true :: remaining) (true :: used) (true :: consumed) [] := by
  have h1 := step_afterTest_pass candidate divisor (true :: shift) physical
    (true :: true :: remaining) used consumed [] carry bit
  have h2 := run_divisor_increment true candidate divisor (true :: shift) physical
    (true :: true :: remaining) used consumed
  have h3 := run_next_degree true true candidate
    (incrementAux true divisor).2 shift physical remaining used consumed
  have hclock : 4 * divisor.length + 8 =
      1 + (2 * divisor.length + 2) + (2 * divisor.length + 5) := by omega
  rw [hclock]
  rw [run_add (1 + (2 * divisor.length + 2)) (2 * divisor.length + 5)]
  rw [run_add 1 (2 * divisor.length + 2), run_succ h1 0]
  simp only [show ∀ q : Config, run 0 q = q from fun _ => rfl]
  rw [h2]
  simp only [hlast, ite_true]
  simpa [incrementAux_length] using h3

private theorem step_degreePeek_nil (passed carry : Bool)
    (candidate divisor shift : List Bool) (physical : Fin 5 → List Bool)
    (used consumed : List Bool) :
    TM2.step program
      (cfg (some .degreePeek) (passed, carry, none) candidate divisor shift
        physical [] used consumed []) =
    some (cfg (some .success) (passed, carry, none) candidate divisor shift
      physical [] used consumed []) := by
  simp [TM2.step, TM2.stepAux, program, cfg, bank]

theorem run_after_passing_last_degree
    (candidate divisor shift : List Bool) (physical : Fin 5 → List Bool)
    (used consumed : List Bool) (carry : Bool) (bit : Option Bool)
    (hlast : (incrementAux true divisor).1 = true) :
    run (2 * divisor.length + 5)
      (cfg (some .afterTest) (true, carry, bit) candidate divisor shift
        physical [true] used consumed []) =
    cfg (some .success) (true, true, none) candidate
      (incrementAux true divisor).2 shift physical [] used consumed [] := by
  have h1 := step_afterTest_pass candidate divisor shift physical
    [true] used consumed [] carry bit
  have h2 := run_divisor_increment true candidate divisor shift physical
    [true] used consumed
  have h3 := step_degreePop_cons true true true candidate
    (incrementAux true divisor).2 shift physical [] used consumed
  have h4 := step_degreePeek_nil true true candidate
    (incrementAux true divisor).2 shift physical used consumed
  have hclock : 2 * divisor.length + 5 = 1 + (2 * divisor.length + 2) + 1 + 1 := by omega
  rw [hclock]
  rw [run_add (1 + (2 * divisor.length + 2) + 1) 1]
  rw [run_add (1 + (2 * divisor.length + 2)) 1]
  rw [run_add 1 (2 * divisor.length + 2)]
  rw [run_succ h1 0]
  simp only [show ∀ q : Config, run 0 q = q from fun _ => rfl]
  rw [h2]
  simp only [hlast, ite_true]
  rw [run_succ h3 0]
  simp only [show ∀ q : Config, run 0 q = q from fun _ => rfl]
  rw [run_succ h4 0]
  rfl

#print axioms run_after_passing_last_divisor_next_degree
#print axioms run_after_passing_last_degree

theorem run_after_failing_nonlast_candidate
    (candidate divisor shift : List Bool) (physical : Fin 5 → List Bool)
    (remaining used consumed : List Bool)
    (carry : Bool) (bit : Option Bool)
    (hnext : (incrementAux true candidate).1 = false) :
    run (2 * candidate.length + divisor.length + used.length + consumed.length + 6)
      (cfg (some .afterTest) (false, carry, bit) candidate divisor shift
        physical remaining used consumed []) =
    cfg (some .test) (false, false, none)
      (incrementAux true candidate).2 [false]
      (List.replicate consumed.length true ++ shift)
      physical (List.replicate used.length true ++ remaining) [] [] [] := by
  have h1 := step_afterTest_fail candidate divisor shift physical
    remaining used consumed [] carry bit
  have h2 := run_candidate_increment false candidate divisor shift physical
    remaining used consumed
  have h3 := run_reset_after_failed_candidate false
    (incrementAux true candidate).2 divisor shift physical
    remaining used consumed
  have hclock : 2 * candidate.length + divisor.length + used.length +
      consumed.length + 6 =
      1 + (2 * candidate.length + 2) +
        (divisor.length + used.length + consumed.length + 3) := by omega
  rw [hclock]
  rw [run_add (1 + (2 * candidate.length + 2))
    (divisor.length + used.length + consumed.length + 3)]
  rw [run_add 1 (2 * candidate.length + 2), run_succ h1 0]
  simp only [show ∀ q : Config, run 0 q = q from fun _ => rfl]
  rw [h2]
  simp only [hnext]
  exact h3

theorem run_after_failing_last_candidate
    (candidate divisor shift : List Bool) (physical : Fin 5 → List Bool)
    (remaining used consumed : List Bool)
    (carry : Bool) (bit : Option Bool)
    (hlast : (incrementAux true candidate).1 = true) :
    run (2 * candidate.length + 3)
      (cfg (some .afterTest) (false, carry, bit) candidate divisor shift
        physical remaining used consumed []) =
    cfg (some .exhausted) (false, true, none)
      (incrementAux true candidate).2 divisor shift physical
      remaining used consumed [] := by
  have h1 := step_afterTest_fail candidate divisor shift physical
    remaining used consumed [] carry bit
  have h2 := run_candidate_increment false candidate divisor shift physical
    remaining used consumed
  have hclock : 2 * candidate.length + 3 = 1 + (2 * candidate.length + 2) := by omega
  rw [hclock, run_add, run_succ h1 0]
  simpa [hlast] using h2

private theorem step_initial_empty_degree (passed carry : Bool)
    (candidate divisor shift : List Bool) (physical : Fin 5 → List Bool) :
    TM2.step program
      (cfg (some .initial) (passed, carry, none) candidate divisor shift
        physical [] [] [] []) =
    some (cfg (some .success) (passed, carry, none) candidate divisor shift
      physical [] [] [] []) := by
  simp [TM2.step, TM2.stepAux, program, cfg, bank]

theorem run_initial_no_divisors (passed carry : Bool)
    (candidate divisor shift : List Bool) (physical : Fin 5 → List Bool) :
    run 1 (cfg (some .initial) (passed, carry, none) candidate divisor shift
      physical [] [] [] []) =
    cfg (some .success) (passed, carry, none) candidate divisor shift
      physical [] [] [] [] := by
  simpa using run_succ
    (step_initial_empty_degree passed carry candidate divisor shift physical) 0

#print axioms run_after_failing_nonlast_candidate
#print axioms run_after_failing_last_candidate
#print axioms run_initial_no_divisors

#print axioms run_add

end CurrentAdditive.FieldMachineHelper.TrialSearchControllerMachine
