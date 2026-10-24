import EthInapproximability.CurrentPaper.BitMachineSubroutine

/-!
# Charged order-preserving table-word transfer

Frozen v8 Appendix B, `thm:paper-materialization`.  A fixed three-stack
controller consumes a literal bit word, reverses it onto a temporary stack,
and reverses it again onto the next bank.  It works for arbitrary bits and
the empty table; both empty-stack tests are charged.
-/

namespace EthInapproximability.CurrentPaper.MatrixTableInterlaceTransfer

open Turing Turing.TM2.Stmt BitMachineEncoding

inductive Label where
  | toTemp | toTarget
  deriving DecidableEq, Fintype

abbrev Stack := Fin 3
abbrev Control := Option Bool
abbrev Config := TM2.Cfg (fun _ : Stack => Bool) Label Control

def program : Label → TM2.Stmt (fun _ : Stack => Bool) Label Control
  | .toTemp => pop 0 (fun _ b => b)
      (branch Option.isSome
        (push 1 (fun b => b.getD false) (goto (fun _ => .toTemp)))
        (goto (fun _ => .toTarget)))
  | .toTarget => pop 1 (fun _ b => b)
      (branch Option.isSome
        (push 2 (fun b => b.getD false) (goto (fun _ => .toTarget)))
        halt)

def cfg (l : Option Label) (s : Control)
    (source temp target : List Bool) : Config :=
  ⟨l,s,![source,temp,target]⟩

def run (t : ℕ) (c : Config) : Config := ((advance program)^[t]) c

private theorem run_add {c d : Config} {t : ℕ}
    (h : run t c = d) (u : ℕ) : run (t+u) c = run u d := by
  rw [Nat.add_comm t u]
  simp only [run, Function.iterate_add_apply] at h ⊢
  rw [h]

private theorem step_temp_cons (s : Control) (b : Bool)
    (xs temp target : List Bool) :
    run 1 (cfg (some .toTemp) s (b::xs) temp target) =
      cfg (some .toTemp) (some b) xs (b::temp) target := by
  simp [run, advance, TM2.step, TM2.stepAux, program, cfg]
  funext k
  fin_cases k <;> rfl

private theorem step_temp_nil (s : Control) (temp target : List Bool) :
    run 1 (cfg (some .toTemp) s [] temp target) =
      cfg (some .toTarget) none [] temp target := by
  simp [run, advance, TM2.step, TM2.stepAux, program, cfg]

private theorem step_target_cons (s : Control) (b : Bool)
    (xs target : List Bool) :
    run 1 (cfg (some .toTarget) s [] (b::xs) target) =
      cfg (some .toTarget) (some b) [] xs (b::target) := by
  simp [run, advance, TM2.step, TM2.stepAux, program, cfg]
  funext k
  fin_cases k <;> rfl

private theorem step_target_nil (s : Control) (target : List Bool) :
    run 1 (cfg (some .toTarget) s [] [] target) =
      cfg none none [] [] target := by
  simp [run, advance, TM2.step, TM2.stepAux, program, cfg]

theorem temp_run (s : Control) (bits temp target : List Bool) :
    run (bits.length+1) (cfg (some .toTemp) s bits temp target) =
      cfg (some .toTarget) none [] (bits.reverse ++ temp) target := by
  induction bits generalizing s temp with
  | nil => simpa using step_temp_nil s temp target
  | cons b bits ih =>
      have h := run_add (step_temp_cons s b bits temp target) (bits.length+1)
      simpa [List.reverse_cons, List.append_assoc, Nat.add_comm, Nat.add_assoc] using
        h.trans (ih (some b) (b::temp))

theorem target_run (s : Control) (bits target : List Bool) :
    run (bits.length+1) (cfg (some .toTarget) s [] bits target) =
      cfg none none [] [] (bits.reverse ++ target) := by
  induction bits generalizing s target with
  | nil => simpa using step_target_nil s target
  | cons b bits ih =>
      have h := run_add (step_target_cons s b bits target) (bits.length+1)
      simpa [List.reverse_cons, List.append_assoc, Nat.add_comm, Nat.add_assoc] using
        h.trans (ih (some b) (b::target))

/-- Two scans and two empty-stack tests, with exact list order. -/
theorem transfer_run (bits target : List Bool) :
    run (2*bits.length+2) (cfg (some .toTemp) none bits [] target) =
      cfg none none [] [] (bits ++ target) := by
  have h := run_add (temp_run none bits [] target) (bits.length+1)
  simp only [List.append_nil] at h
  have ht := target_run none bits.reverse target
  simp only [List.length_reverse, List.reverse_reverse] at ht
  simpa only [show 2*bits.length+2 =
    (bits.length+1)+(bits.length+1) by omega] using h.trans ht

theorem transfer_bound (bits : List Bool) :
    2*bits.length+2 ≤ 2*(bits.length+1)^2 := by
  nlinarith

end EthInapproximability.CurrentPaper.MatrixTableInterlaceTransfer
