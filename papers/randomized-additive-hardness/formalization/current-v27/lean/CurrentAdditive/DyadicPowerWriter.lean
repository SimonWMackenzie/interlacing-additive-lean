import EthInapproximability.CurrentPaper.BitMachineEncoding
import Mathlib.Tactic

/-! A literal two-stack TM2 primitive used by the integer-power tests:
from a unary exponent on stack 0 it writes the little-endian bits of `2^b`
on stack 1.  This is only one component of the public compiler. -/
namespace CurrentAdditive.PublicScheduleDyadicPowerWriter

open Turing Turing.TM2.Stmt EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding

inductive Label where
  | start | scan
  deriving DecidableEq, Fintype

def program : Label → TM2.Stmt (fun _ : Fin 2 => Bool) Label (Option Bool)
  | .start => push 1 (fun _ => true) (goto (fun _ => .scan))
  | .scan => pop 0 (fun _ b => b)
      (branch Option.isSome
        (push 1 (fun _ => false) (goto (fun _ => .scan)))
        halt)

def cfg (l : Option Label) (s : Option Bool)
    (source output : List Bool) : TM2.Cfg (fun _ : Fin 2 => Bool) Label (Option Bool) :=
  ⟨l, s, ![source, output]⟩

def run (n : ℕ) (c : TM2.Cfg (fun _ : Fin 2 => Bool) Label (Option Bool)) :=
  ((advance program)^[n]) c

private theorem run_succ {c d : TM2.Cfg (fun _ : Fin 2 => Bool) Label (Option Bool)}
    (h : TM2.step program c = some d) (n : ℕ) :
    run (n + 1) c = run n d := by
  simp only [run, Function.iterate_succ_apply, advance, h, Option.getD_some]

private theorem step_start (s : Option Bool) (q out : List Bool) :
    TM2.step program (cfg (some .start) s q out) =
      some (cfg (some .scan) s q (true :: out)) := by
  simp [TM2.step, TM2.stepAux, program, cfg]
  funext k
  fin_cases k <;> rfl

private theorem step_scan_cons (s : Option Bool) (x : Bool)
    (q out : List Bool) :
    TM2.step program (cfg (some .scan) s (x :: q) out) =
      some (cfg (some .scan) (some x) q (false :: out)) := by
  simp [TM2.step, TM2.stepAux, program, cfg]
  funext k
  fin_cases k <;> rfl

private theorem step_scan_nil (s : Option Bool) (out : List Bool) :
    TM2.step program (cfg (some .scan) s [] out) =
      some (cfg none none [] out) := by
  simp [TM2.step, TM2.stepAux, program, cfg]

theorem scan_run (q out : List Bool) (s : Option Bool) :
    run (q.length + 1) (cfg (some .scan) s q out) =
      cfg none none [] (List.replicate q.length false ++ out) := by
  induction q generalizing s out with
  | nil => simpa using run_succ (step_scan_nil s out) 0
  | cons x q ih =>
      rw [List.length_cons, run_succ (step_scan_cons s x q out)]
      simpa [List.replicate_add, List.append_assoc] using ih (false :: out) (some x)

theorem run_correct (q : List Bool) :
    run (q.length + 2) (cfg (some .start) none q []) =
      cfg none none [] (List.replicate q.length false ++ [true]) := by
  rw [show q.length + 2 = (q.length + 1) + 1 by omega,
    run_succ (step_start none q [])]
  exact scan_run q [true] none

theorem unary_power_clock (b : ℕ) :
    run (b + 2) (cfg (some .start) none (List.replicate b true) []) =
      cfg none none [] (List.replicate b false ++ [true]) := by
  simpa only [List.length_replicate] using run_correct (List.replicate b true)

#print axioms unary_power_clock

end CurrentAdditive.PublicScheduleDyadicPowerWriter
