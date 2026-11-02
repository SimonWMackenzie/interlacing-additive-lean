import EthInapproximability.CurrentPaper.SamplerMachine

/-!
After a monic leading-bit XOR, the accumulator starts with a known zero.
The high-first shifted divisor ends with a zero whenever the shift is
positive. This literal three-stack TM2 program discards those two bits,
restores all other divisor bits, and clears scratch. Thus its output is
aligned for the next long-division iteration.
-/

namespace CurrentAdditive.FieldMachineHelper.DivisionRepackMachine

open Turing Turing.TM2.Stmt
open EthInapproximability.CurrentPaper.BitMachineEncoding

inductive Label where
  | dropAcc | scanDiv | dropTail | restoreDiv
  deriving DecidableEq, Fintype

abbrev Control := Option Bool
abbrev Config := TM2.Cfg (fun _ : Fin 3 => Bool) Label Control

def program : Label → TM2.Stmt (fun _ : Fin 3 => Bool) Label Control
  | .dropAcc => pop 0 (fun _ b => b)
      (load (fun _ => none) (goto (fun _ => .scanDiv)))
  | .scanDiv => pop 1 (fun _ b => b)
      (branch Option.isSome
        (push 2 (fun s => s.getD false)
          (load (fun _ => none) (goto (fun _ => .scanDiv))))
        (goto (fun _ => .dropTail)))
  | .dropTail => pop 2 (fun _ b => b)
      (load (fun _ => none) (goto (fun _ => .restoreDiv)))
  | .restoreDiv => pop 2 (fun _ b => b)
      (branch Option.isSome
        (push 1 (fun s => s.getD false)
          (load (fun _ => none) (goto (fun _ => .restoreDiv))))
        halt)

def bank (acc divisor scratch : List Bool) : Fin 3 → List Bool :=
  fun k => if k = 0 then acc else if k = 1 then divisor else scratch

def cfg (l : Option Label) (s : Control)
    (acc divisor scratch : List Bool) : Config :=
  ⟨l, s, bank acc divisor scratch⟩

def run (t : Nat) (q : Config) : Config := ((advance program)^[t]) q

private theorem run_succ {c e : Config} (h : TM2.step program c = some e)
    (t : Nat) : run (t + 1) c = run t e := by
  simp only [run, Function.iterate_succ_apply, advance, h, Option.getD_some]

private theorem run_add (t u : Nat) (q : Config) :
    run (t + u) q = run u (run t q) := by
  rw [Nat.add_comm t u]
  simp only [run, Function.iterate_add_apply]

private theorem step_dropAcc (b : Bool) (acc divisor scratch : List Bool) :
    TM2.step program (cfg (some .dropAcc) none (b :: acc) divisor scratch) =
      some (cfg (some .scanDiv) none acc divisor scratch) := by
  simp [TM2.step, TM2.stepAux, program, cfg, bank]
  funext k
  fin_cases k <;> rfl

private theorem step_scan_cons (b : Bool) (acc divisor scratch : List Bool) :
    TM2.step program (cfg (some .scanDiv) none acc (b :: divisor) scratch) =
      some (cfg (some .scanDiv) none acc divisor (b :: scratch)) := by
  simp [TM2.step, TM2.stepAux, program, cfg, bank]
  funext k
  fin_cases k <;> rfl

private theorem step_scan_nil (acc scratch : List Bool) :
    TM2.step program (cfg (some .scanDiv) none acc [] scratch) =
      some (cfg (some .dropTail) none acc [] scratch) := by
  simp [TM2.step, TM2.stepAux, program, cfg, bank]

private theorem step_dropTail (b : Bool) (acc scratch : List Bool) :
    TM2.step program (cfg (some .dropTail) none acc [] (b :: scratch)) =
      some (cfg (some .restoreDiv) none acc [] scratch) := by
  simp [TM2.step, TM2.stepAux, program, cfg, bank]
  funext k
  fin_cases k <;> rfl

private theorem step_restore_cons (b : Bool) (acc divisor scratch : List Bool) :
    TM2.step program (cfg (some .restoreDiv) none acc divisor (b :: scratch)) =
      some (cfg (some .restoreDiv) none acc (b :: divisor) scratch) := by
  simp [TM2.step, TM2.stepAux, program, cfg, bank]
  funext k
  fin_cases k <;> rfl

private theorem step_restore_nil (acc divisor : List Bool) :
    TM2.step program (cfg (some .restoreDiv) none acc divisor []) =
      some (cfg none none acc divisor []) := by
  simp [TM2.step, TM2.stepAux, program, cfg, bank]

theorem scan_run (acc divisor scratch : List Bool) :
    run (divisor.length + 1)
      (cfg (some .scanDiv) none acc divisor scratch) =
    cfg (some .dropTail) none acc [] (divisor.reverse ++ scratch) := by
  induction divisor generalizing scratch with
  | nil => simpa using run_succ (step_scan_nil acc scratch) 0
  | cons b rest ih =>
    rw [List.length_cons, run_succ (step_scan_cons b acc rest scratch)]
    simpa [List.reverse_cons, List.append_assoc] using ih (b :: scratch)

theorem restore_run (acc divisor scratch : List Bool) :
    run (scratch.length + 1)
      (cfg (some .restoreDiv) none acc divisor scratch) =
    cfg none none acc (scratch.reverse ++ divisor) [] := by
  induction scratch generalizing divisor with
  | nil => simpa using run_succ (step_restore_nil acc divisor) 0
  | cons b rest ih =>
    rw [List.length_cons, run_succ (step_restore_cons b acc divisor rest)]
    simpa [List.reverse_cons, List.append_assoc] using ih (b :: divisor)

/-- One full physical repack. The final divisor bit is discarded. -/
theorem run_repack_any (acc pre : List Bool) (last : Bool) :
    run (2 * (pre.length + 1) + 3)
      (cfg (some .dropAcc) none (false :: acc) (pre ++ [last]) []) =
    cfg none none acc pre [] := by
  have hdrop : run 1
      (cfg (some .dropAcc) none (false :: acc) (pre ++ [last]) []) =
      cfg (some .scanDiv) none acc (pre ++ [last]) [] := by
    simpa using run_succ (step_dropAcc false acc (pre ++ [last]) []) 0
  have hscan := scan_run acc (pre ++ [last]) []
  have htail : run 1
      (cfg (some .dropTail) none acc [] (last :: pre.reverse)) =
      cfg (some .restoreDiv) none acc [] pre.reverse := by
    simpa using run_succ (step_dropTail last acc pre.reverse) 0
  have hrestore := restore_run acc [] pre.reverse
  have hfirst : run (1 + ((pre ++ [last]).length + 1))
      (cfg (some .dropAcc) none (false :: acc) (pre ++ [last]) []) =
      cfg (some .dropTail) none acc [] (last :: pre.reverse) := by
    rw [run_add, hdrop, hscan]
    simp
  have hsecond : run (1 + ((pre ++ [last]).length + 1) + 1)
      (cfg (some .dropAcc) none (false :: acc) (pre ++ [last]) []) =
      cfg (some .restoreDiv) none acc [] pre.reverse := by
    rw [run_add, hfirst, htail]
  have hbudget : 2 * (pre.length + 1) + 3 =
      1 + ((pre ++ [last]).length + 1) +
        1 + (pre.reverse.length + 1) := by simp; omega
  rw [hbudget, run_add, hsecond, hrestore]
  simp

/-- In a nonterminal division iteration, the discarded divisor bit is zero. -/
theorem run_repack (acc pre : List Bool) :
    run (2 * (pre.length + 1) + 3)
      (cfg (some .dropAcc) none (false :: acc) (pre ++ [false]) []) =
    cfg none none acc pre [] := run_repack_any acc pre false

#print axioms run_repack

end CurrentAdditive.FieldMachineHelper.DivisionRepackMachine
