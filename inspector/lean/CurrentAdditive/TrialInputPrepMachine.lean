import CurrentAdditive.CounterBitEncoding

/-!
Literal preparation for one trial pair. Seven Boolean stacks store a
candidate counter, divisor counter, unary shift source, dividend output,
shifted-divisor output, division count, and one reusable scratch stack.
Both counters and the shift source are restored. Copying a low-first counter
by stack reversal produces high-first low coefficients; a leading `true`
makes each polynomial monic. The shift source creates the divisor's trailing
zeros and the division count (shift amount plus one).
-/

namespace CurrentAdditive.FieldMachineHelper.TrialInputPrepMachine

open Turing Turing.TM2.Stmt
open EthInapproximability.CurrentPaper.BitMachineEncoding

inductive Label where
  | shiftScan | shiftRestore | candidateScan | candidateRestore
  | divisorScan | divisorRestore
  deriving DecidableEq, Fintype

abbrev Control := Option Bool
abbrev Config := TM2.Cfg (fun _ : Fin 7 => Bool) Label Control

def program : Label → TM2.Stmt (fun _ : Fin 7 => Bool) Label Control
  | .shiftScan => pop 2 (fun _ bit => bit)
      (branch Option.isSome
        (push 6 (fun s => s.getD false)
          (push 4 (fun _ => false)
            (push 5 (fun _ => true) (goto (fun _ => .shiftScan)))))
        (goto (fun _ => .shiftRestore)))
  | .shiftRestore => pop 6 (fun _ bit => bit)
      (branch Option.isSome
        (push 2 (fun s => s.getD false) (goto (fun _ => .shiftRestore)))
        (goto (fun _ => .candidateScan)))
  | .candidateScan => pop 0 (fun _ bit => bit)
      (branch Option.isSome
        (push 6 (fun s => s.getD false)
          (push 3 (fun s => s.getD false) (goto (fun _ => .candidateScan))))
        (goto (fun _ => .candidateRestore)))
  | .candidateRestore => pop 6 (fun _ bit => bit)
      (branch Option.isSome
        (push 0 (fun s => s.getD false) (goto (fun _ => .candidateRestore)))
        (push 3 (fun _ => true) (goto (fun _ => .divisorScan))))
  | .divisorScan => pop 1 (fun _ bit => bit)
      (branch Option.isSome
        (push 6 (fun s => s.getD false)
          (push 4 (fun s => s.getD false) (goto (fun _ => .divisorScan))))
        (goto (fun _ => .divisorRestore)))
  | .divisorRestore => pop 6 (fun _ bit => bit)
      (branch Option.isSome
        (push 1 (fun s => s.getD false) (goto (fun _ => .divisorRestore)))
        (push 4 (fun _ => true)
          (push 5 (fun _ => true) halt)))

def bank (candidate divisor shift dividend shiftedDivisor count scratch : List Bool) :
    Fin 7 → List Bool :=
  fun k => if k = 0 then candidate else if k = 1 then divisor else
    if k = 2 then shift else if k = 3 then dividend else
    if k = 4 then shiftedDivisor else if k = 5 then count else scratch

def cfg (l : Option Label) (s : Control)
    (candidate divisor shift dividend shiftedDivisor count scratch : List Bool) :
    Config :=
  ⟨l, s, bank candidate divisor shift dividend shiftedDivisor count scratch⟩

def run (t : Nat) (q : Config) : Config := ((advance program)^[t]) q

private theorem run_succ {c e : Config} (h : TM2.step program c = some e)
    (t : Nat) : run (t + 1) c = run t e := by
  simp only [run, Function.iterate_succ_apply, advance, h, Option.getD_some]

theorem run_add (t u : Nat) (q : Config) :
    run (t + u) q = run u (run t q) := by
  rw [Nat.add_comm t u]
  simp only [run, Function.iterate_add_apply]

private theorem step_shiftScan_cons (bit : Bool)
    (candidate divisor shift dividend shifted count scratch : List Bool) :
    TM2.step program
      (cfg (some .shiftScan) none candidate divisor (bit :: shift)
        dividend shifted count scratch) =
      some (cfg (some .shiftScan) (some bit) candidate divisor shift
        dividend (false :: shifted) (true :: count) (bit :: scratch)) := by
  simp [TM2.step, TM2.stepAux, program, cfg, bank]
  funext k
  fin_cases k <;> rfl

private theorem step_shiftScan_nil
    (candidate divisor dividend shifted count scratch : List Bool) :
    TM2.step program
      (cfg (some .shiftScan) none candidate divisor []
        dividend shifted count scratch) =
      some (cfg (some .shiftRestore) none candidate divisor []
        dividend shifted count scratch) := by
  simp [TM2.step, TM2.stepAux, program, cfg, bank]

private theorem step_shiftRestore_cons (bit : Bool)
    (candidate divisor shift dividend shifted count scratch : List Bool) :
    TM2.step program
      (cfg (some .shiftRestore) none candidate divisor shift
        dividend shifted count (bit :: scratch)) =
      some (cfg (some .shiftRestore) (some bit) candidate divisor
        (bit :: shift) dividend shifted count scratch) := by
  simp [TM2.step, TM2.stepAux, program, cfg, bank]
  funext k
  fin_cases k <;> rfl

private theorem step_shiftRestore_nil
    (candidate divisor shift dividend shifted count : List Bool) :
    TM2.step program
      (cfg (some .shiftRestore) none candidate divisor shift
        dividend shifted count []) =
      some (cfg (some .candidateScan) none candidate divisor shift
        dividend shifted count []) := by
  simp [TM2.step, TM2.stepAux, program, cfg, bank]

theorem shiftScan_run
    (candidate divisor shift dividend shifted count scratch : List Bool) :
    run (shift.length + 1)
      (cfg (some .shiftScan) none candidate divisor shift
        dividend shifted count scratch) =
      cfg (some .shiftRestore) none candidate divisor [] dividend
        (List.replicate shift.length false ++ shifted)
        (List.replicate shift.length true ++ count)
        (shift.reverse ++ scratch) := by
  induction shift generalizing shifted count scratch with
  | nil =>
    simpa using (run_succ
      (step_shiftScan_nil candidate divisor dividend shifted count scratch) 0)
  | cons bit rest ih =>
    rw [List.length_cons,
      run_succ (step_shiftScan_cons bit candidate divisor rest
        dividend shifted count scratch)]
    simpa [List.replicate_succ', List.reverse_cons, List.append_assoc] using
      ih (false :: shifted) (true :: count) (bit :: scratch)

theorem shiftRestore_run
    (candidate divisor shift dividend shifted count scratch : List Bool) :
    run (scratch.length + 1)
      (cfg (some .shiftRestore) none candidate divisor shift
        dividend shifted count scratch) =
      cfg (some .candidateScan) none candidate divisor
        (scratch.reverse ++ shift) dividend shifted count [] := by
  induction scratch generalizing shift with
  | nil =>
    simpa using (run_succ
      (step_shiftRestore_nil candidate divisor shift dividend shifted count) 0)
  | cons bit rest ih =>
    rw [List.length_cons,
      run_succ (step_shiftRestore_cons bit candidate divisor shift
        dividend shifted count rest)]
    simpa [List.reverse_cons, List.append_assoc] using ih (bit :: shift)

theorem shiftPhase_run
    (candidate divisor shift dividend shifted count : List Bool) :
    run (2 * shift.length + 2)
      (cfg (some .shiftScan) none candidate divisor shift
        dividend shifted count []) =
      cfg (some .candidateScan) none candidate divisor shift dividend
        (List.replicate shift.length false ++ shifted)
        (List.replicate shift.length true ++ count) [] := by
  have hs := shiftScan_run candidate divisor shift dividend shifted count []
  have hr := shiftRestore_run candidate divisor [] dividend
    (List.replicate shift.length false ++ shifted)
    (List.replicate shift.length true ++ count) shift.reverse
  have hb : 2 * shift.length + 2 =
      (shift.length + 1) + (shift.reverse.length + 1) := by simp; omega
  rw [hb, run_add, hs]
  simpa using hr

private theorem step_candidateScan_cons (bit : Bool)
    (candidate divisor shift dividend shifted count scratch : List Bool) :
    TM2.step program
      (cfg (some .candidateScan) none (bit :: candidate) divisor shift
        dividend shifted count scratch) =
      some (cfg (some .candidateScan) (some bit) candidate divisor shift
        (bit :: dividend) shifted count (bit :: scratch)) := by
  simp [TM2.step, TM2.stepAux, program, cfg, bank]
  funext k
  fin_cases k <;> rfl

private theorem step_candidateScan_nil
    (divisor shift dividend shifted count scratch : List Bool) :
    TM2.step program
      (cfg (some .candidateScan) none [] divisor shift
        dividend shifted count scratch) =
      some (cfg (some .candidateRestore) none [] divisor shift
        dividend shifted count scratch) := by
  simp [TM2.step, TM2.stepAux, program, cfg, bank]

private theorem step_candidateRestore_cons (bit : Bool)
    (candidate divisor shift dividend shifted count scratch : List Bool) :
    TM2.step program
      (cfg (some .candidateRestore) none candidate divisor shift
        dividend shifted count (bit :: scratch)) =
      some (cfg (some .candidateRestore) (some bit) (bit :: candidate)
        divisor shift dividend shifted count scratch) := by
  simp [TM2.step, TM2.stepAux, program, cfg, bank]
  funext k
  fin_cases k <;> rfl

private theorem step_candidateRestore_nil
    (candidate divisor shift dividend shifted count : List Bool) :
    TM2.step program
      (cfg (some .candidateRestore) none candidate divisor shift
        dividend shifted count []) =
      some (cfg (some .divisorScan) none candidate divisor shift
        (true :: dividend) shifted count []) := by
  simp [TM2.step, TM2.stepAux, program, cfg, bank]
  funext k
  fin_cases k <;> rfl

theorem candidateScan_run
    (candidate divisor shift dividend shifted count scratch : List Bool) :
    run (candidate.length + 1)
      (cfg (some .candidateScan) none candidate divisor shift
        dividend shifted count scratch) =
      cfg (some .candidateRestore) none [] divisor shift
        (candidate.reverse ++ dividend) shifted count
        (candidate.reverse ++ scratch) := by
  induction candidate generalizing dividend scratch with
  | nil =>
    simpa using (run_succ
      (step_candidateScan_nil divisor shift dividend shifted count scratch) 0)
  | cons bit rest ih =>
    rw [List.length_cons,
      run_succ (step_candidateScan_cons bit rest divisor shift
        dividend shifted count scratch)]
    simpa [List.reverse_cons, List.append_assoc] using
      ih (bit :: dividend) (bit :: scratch)

theorem candidateRestore_run
    (candidate divisor shift dividend shifted count scratch : List Bool) :
    run (scratch.length + 1)
      (cfg (some .candidateRestore) none candidate divisor shift
        dividend shifted count scratch) =
      cfg (some .divisorScan) none (scratch.reverse ++ candidate)
        divisor shift (true :: dividend) shifted count [] := by
  induction scratch generalizing candidate with
  | nil =>
    simpa using (run_succ
      (step_candidateRestore_nil candidate divisor shift dividend shifted count) 0)
  | cons bit rest ih =>
    rw [List.length_cons,
      run_succ (step_candidateRestore_cons bit candidate divisor shift
        dividend shifted count rest)]
    simpa [List.reverse_cons, List.append_assoc] using ih (bit :: candidate)

theorem candidatePhase_run
    (candidate divisor shift dividend shifted count : List Bool) :
    run (2 * candidate.length + 2)
      (cfg (some .candidateScan) none candidate divisor shift
        dividend shifted count []) =
      cfg (some .divisorScan) none candidate divisor shift
        (true :: candidate.reverse ++ dividend) shifted count [] := by
  have hs := candidateScan_run candidate divisor shift dividend shifted count []
  have hr := candidateRestore_run [] divisor shift
    (candidate.reverse ++ dividend) shifted count candidate.reverse
  have hb : 2 * candidate.length + 2 =
      (candidate.length + 1) + (candidate.reverse.length + 1) := by simp; omega
  rw [hb, run_add, hs]
  simpa using hr

private theorem step_divisorScan_cons (bit : Bool)
    (candidate divisor shift dividend shifted count scratch : List Bool) :
    TM2.step program
      (cfg (some .divisorScan) none candidate (bit :: divisor) shift
        dividend shifted count scratch) =
      some (cfg (some .divisorScan) (some bit) candidate divisor shift
        dividend (bit :: shifted) count (bit :: scratch)) := by
  simp [TM2.step, TM2.stepAux, program, cfg, bank]
  funext k
  fin_cases k <;> rfl

private theorem step_divisorScan_nil
    (candidate shift dividend shifted count scratch : List Bool) :
    TM2.step program
      (cfg (some .divisorScan) none candidate [] shift
        dividend shifted count scratch) =
      some (cfg (some .divisorRestore) none candidate [] shift
        dividend shifted count scratch) := by
  simp [TM2.step, TM2.stepAux, program, cfg, bank]

private theorem step_divisorRestore_cons (bit : Bool)
    (candidate divisor shift dividend shifted count scratch : List Bool) :
    TM2.step program
      (cfg (some .divisorRestore) none candidate divisor shift
        dividend shifted count (bit :: scratch)) =
      some (cfg (some .divisorRestore) (some bit) candidate (bit :: divisor)
        shift dividend shifted count scratch) := by
  simp [TM2.step, TM2.stepAux, program, cfg, bank]
  funext k
  fin_cases k <;> rfl

private theorem step_divisorRestore_nil
    (candidate divisor shift dividend shifted count : List Bool) :
    TM2.step program
      (cfg (some .divisorRestore) none candidate divisor shift
        dividend shifted count []) =
      some (cfg none none candidate divisor shift
        dividend (true :: shifted) (true :: count) []) := by
  simp [TM2.step, TM2.stepAux, program, cfg, bank]
  funext k
  fin_cases k <;> rfl

theorem divisorScan_run
    (candidate divisor shift dividend shifted count scratch : List Bool) :
    run (divisor.length + 1)
      (cfg (some .divisorScan) none candidate divisor shift
        dividend shifted count scratch) =
      cfg (some .divisorRestore) none candidate [] shift dividend
        (divisor.reverse ++ shifted) count (divisor.reverse ++ scratch) := by
  induction divisor generalizing shifted scratch with
  | nil =>
    simpa using (run_succ
      (step_divisorScan_nil candidate shift dividend shifted count scratch) 0)
  | cons bit rest ih =>
    rw [List.length_cons,
      run_succ (step_divisorScan_cons bit candidate rest shift
        dividend shifted count scratch)]
    simpa [List.reverse_cons, List.append_assoc] using
      ih (bit :: shifted) (bit :: scratch)

theorem divisorRestore_run
    (candidate divisor shift dividend shifted count scratch : List Bool) :
    run (scratch.length + 1)
      (cfg (some .divisorRestore) none candidate divisor shift
        dividend shifted count scratch) =
      cfg none none candidate (scratch.reverse ++ divisor) shift
        dividend (true :: shifted) (true :: count) [] := by
  induction scratch generalizing divisor with
  | nil =>
    simpa using (run_succ
      (step_divisorRestore_nil candidate divisor shift dividend shifted count) 0)
  | cons bit rest ih =>
    rw [List.length_cons,
      run_succ (step_divisorRestore_cons bit candidate divisor shift
        dividend shifted count rest)]
    simpa [List.reverse_cons, List.append_assoc] using ih (bit :: divisor)

theorem divisorPhase_run
    (candidate divisor shift dividend shifted count : List Bool) :
    run (2 * divisor.length + 2)
      (cfg (some .divisorScan) none candidate divisor shift
        dividend shifted count []) =
      cfg none none candidate divisor shift dividend
        (true :: divisor.reverse ++ shifted) (true :: count) [] := by
  have hs := divisorScan_run candidate divisor shift dividend shifted count []
  have hr := divisorRestore_run candidate [] shift dividend
    (divisor.reverse ++ shifted) count divisor.reverse
  have hb : 2 * divisor.length + 2 =
      (divisor.length + 1) + (divisor.reverse.length + 1) := by simp; omega
  rw [hb, run_add, hs]
  simpa using hr

/-- Exact full preparation clock; all three source stacks are restored. -/
theorem run_prepare (candidate divisor shift : List Bool) :
    run (2 * (shift.length + candidate.length + divisor.length) + 6)
      (cfg (some .shiftScan) none
        candidate divisor shift [] [] [] []) =
    cfg none none candidate divisor shift
      (true :: candidate.reverse)
      (true :: divisor.reverse ++ List.replicate shift.length false)
      (true :: List.replicate shift.length true) [] := by
  have hs := shiftPhase_run candidate divisor shift [] [] []
  have hc := candidatePhase_run candidate divisor shift []
    (List.replicate shift.length false)
    (List.replicate shift.length true)
  have hd := divisorPhase_run candidate divisor shift
    (true :: candidate.reverse)
    (List.replicate shift.length false)
    (List.replicate shift.length true)
  have hb : 2 * (shift.length + candidate.length + divisor.length) + 6 =
      (2 * shift.length + 2) + (2 * candidate.length + 2) +
        (2 * divisor.length + 2) := by omega
  rw [hb]
  rw [run_add ((2 * shift.length + 2) + (2 * candidate.length + 2))
    (2 * divisor.length + 2)]
  rw [run_add (2 * shift.length + 2) (2 * candidate.length + 2)]
  rw [hs]
  simp only [List.append_nil]
  rw [hc]
  simp only [List.append_nil]
  exact hd

#print axioms run_prepare

end CurrentAdditive.FieldMachineHelper.TrialInputPrepMachine
