import EthInapproximability.CurrentPaper.BitMachineEncoding

/-! Literal finite-stack conjunction of the coordinate-comparison bits for a
cylinder.  The input is consumed one bit per transition; the accumulator is a
single finite-control Boolean. -/

namespace CurrentAdditive.CylinderConjunctionMachine

open Turing Turing.TM2.Stmt
open EthInapproximability.CurrentPaper.BitMachineEncoding

inductive Label where
  | scan
  deriving DecidableEq, Fintype

abbrev Control := Bool × Option Bool
abbrev Config := TM2.Cfg (fun _ : Fin 2 => Bool) Label Control

def program : Label → TM2.Stmt (fun _ : Fin 2 => Bool) Label Control
  | .scan => pop 0 (fun v b => (v.1, b))
      (branch (fun v => v.2.isSome)
        (load (fun v => (v.1 && v.2.getD true, none)) (goto (fun _ => .scan)))
        (push 1 (fun v => v.1) halt))

def cfg (l : Option Label) (v : Control) (input output : List Bool) : Config :=
  ⟨l, v, fun k => if k = 0 then input else output⟩

def run (t : Nat) (c : Config) : Config := ((advance program)^[t]) c

private theorem run_add (t u : Nat) (c : Config) :
    run (t + u) c = run u (run t c) := by
  rw [Nat.add_comm t u]
  simp [run, Function.iterate_add_apply]

def conjunction (e : Bool) (bits : List Bool) : Bool :=
  bits.foldl (fun a b => a && b) e

private theorem step_cons (e b : Bool) (bits output : List Bool) :
    advance program (cfg (some .scan) (e, none) (b::bits) output) =
      cfg (some .scan) (e && b, none) bits output := by
  simp [advance, TM2.step, TM2.stepAux, program, cfg]
  funext k; fin_cases k <;> rfl

private theorem step_nil (e : Bool) (output : List Bool) :
    advance program (cfg (some .scan) (e, none) [] output) =
      cfg none (e, none) [] (e::output) := by
  simp [advance, TM2.step, TM2.stepAux, program, cfg]
  funext k; fin_cases k <;> rfl

theorem run_conjunction (e : Bool) (bits output : List Bool) :
    run (bits.length+1) (cfg (some .scan) (e, none) bits output) =
      cfg none (conjunction e bits, none) []
        (conjunction e bits :: output) := by
  induction bits generalizing e with
  | nil => simp [run, conjunction, step_nil]
  | cons b bits ih =>
      rw [List.length_cons, show bits.length + 1 + 1 = 1 + (bits.length+1) by omega]
      rw [run_add]
      simp only [run, Function.iterate_one, step_cons]
      simpa only [conjunction, List.foldl_cons] using ih (e && b)

#print axioms run_conjunction

end CurrentAdditive.CylinderConjunctionMachine
