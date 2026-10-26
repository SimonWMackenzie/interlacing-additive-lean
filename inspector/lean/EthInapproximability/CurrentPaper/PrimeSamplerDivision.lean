import EthInapproximability.CurrentPaper.BitMachineEncoding
import Mathlib.Tactic

/-!
# Literal unary remainder testing for the prime search

Source: frozen v8 `B-effectivity-details.tex`,
`lem:paper-explicit-balanced-family`, the trial-division implementation.
The four Boolean stacks contain the remaining dividend, the unused part
of the current divisor cycle, its used part, and output. Each cycle moves
the divisor back one token at a time. No natural-number operation occurs
inside the finite controller. These raw-bank statements are a subroutine,
not yet the complete prime finder or its binary-input interface.
-/

namespace EthInapproximability.CurrentPaper.PrimeSamplerDivision

open Turing TM2.Stmt BitMachineEncoding

inductive Label where
  | scan | check | restore
  deriving DecidableEq, Fintype

abbrev Control := Bool × Option Bool
abbrev Config := TM2.Cfg (fun _ : Fin 4 => Bool) Label Control

def program : Label → TM2.Stmt (fun _ : Fin 4 => Bool) Label Control
  | .scan => pop 0 (fun v b => (v.1, b))
      (branch (fun v => v.2.isSome)
        (pop 1 (fun v b => (v.1, b))
          (push 2 (fun _ => true) (goto (fun _ => .check))))
        (push 3 Prod.fst halt))
  | .check => pop 1 (fun v b => (v.1, b))
      (branch (fun v => v.2.isSome)
        (push 1 (fun _ => true) (load (fun _ => (false, none)) (goto (fun _ => .scan))))
        (goto (fun _ => .restore)))
  | .restore => pop 2 (fun v b => (v.1, b))
      (branch (fun v => v.2.isSome)
        (push 1 (fun _ => true) (goto (fun _ => .restore)))
        (load (fun _ => (true, none)) (goto (fun _ => .scan))))

def bank (input left used output : List Bool) : Fin 4 → List Bool :=
  fun j => if j = 0 then input else if j = 1 then left else if j = 2 then used else output

def cfg (l : Option Label) (v : Control) (input left used output : List Bool) : Config :=
  ⟨l, v, bank input left used output⟩

def run (t : ℕ) (c : Config) : Config := ((advance program)^[t]) c

theorem run_add {c d : Config} {t : ℕ} (h : run t c = d) (u : ℕ) :
    run (t+u) c = run u d := by
  rw [Nat.add_comm t u]
  simp only [run, Function.iterate_add_apply] at h ⊢
  rw [h]

theorem run_step {c d : Config} (h : TM2.step program c = some d) (t : ℕ) :
    run (t+1) c = run t d := by
  simp only [run, Function.iterate_succ_apply, advance, h, Option.getD_some]

private theorem scan_cons (b : Bool) (input left used output : List Bool) :
    TM2.step program (cfg (some .scan) (b, none) (true::input) (true::left) used output) =
      some (cfg (some .check) (b, some true) input left (true::used) output) := by
  apply congrArg (fun S => some (⟨some .check, (b, some true), S⟩ : Config))
  funext j
  fin_cases j <;> rfl

private theorem check_cons (b : Bool) (input left used output : List Bool) :
    TM2.step program (cfg (some .check) (b, some true) input (true::left) used output) =
      some (cfg (some .scan) (false, none) input (true::left) used output) := by
  apply congrArg (fun S => some (⟨some .scan, (false, none), S⟩ : Config))
  funext j
  fin_cases j <;> rfl

private theorem check_nil (b : Bool) (input used output : List Bool) :
    TM2.step program (cfg (some .check) (b, some true) input [] used output) =
      some (cfg (some .restore) (b, none) input [] used output) := by
  apply congrArg (fun S => some (⟨some .restore, (b, none), S⟩ : Config))
  funext j
  fin_cases j <;> rfl

private theorem restore_cons (v : Control) (input left used output : List Bool) :
    TM2.step program (cfg (some .restore) v input left (true::used) output) =
      some (cfg (some .restore) (v.1, some true) input (true::left) used output) := by
  apply congrArg (fun S => some (⟨some .restore, (v.1, some true), S⟩ : Config))
  funext j
  fin_cases j <;> rfl

private theorem restore_nil (v : Control) (input left output : List Bool) :
    TM2.step program (cfg (some .restore) v input left [] output) =
      some (cfg (some .scan) (true, none) input left [] output) := by
  apply congrArg (fun S => some (⟨some .scan, (true, none), S⟩ : Config))
  funext j
  fin_cases j <;> rfl

private theorem scan_nil (b : Bool) (left used output : List Bool) :
    TM2.step program (cfg (some .scan) (b, none) [] left used output) =
      some (cfg none (b, none) [] left used (b::output)) := by
  apply congrArg (fun S => some (⟨none, (b, none), S⟩ : Config))
  funext j
  fin_cases j <;> rfl

theorem restore_run (a b : ℕ) (v : Control) (input output : List Bool) :
    run (b+1) (cfg (some .restore) v input (List.replicate a true)
      (List.replicate b true) output) =
      cfg (some .scan) (true, none) input (List.replicate (a+b) true) [] output := by
  induction b generalizing a v with
  | zero =>
      simp only [Nat.zero_add, Nat.add_zero, List.replicate_zero, run,
        Function.iterate_one, advance, restore_nil, Option.getD_some]
  | succ b ih =>
      rw [List.replicate_succ]
      rw [run_step (restore_cons v input (List.replicate a true) (List.replicate b true) output)]
      simpa only [← List.replicate_succ, Nat.add_right_comm, Nat.add_assoc] using
        ih (a+1) (v.1, some true)

/-- Complete remainder-test execution from any position in the divisor cycle.
The result banks also expose the final cycle position for subsequent calls. -/
theorem remainder_run (d n r : ℕ) (hr : r < d) (output : List Bool) :
    ∃ t ≤ (d+3)*n+1,
      run t (cfg (some .scan) (decide (r=0), none) (List.replicate n true)
        (List.replicate (d-r) true) (List.replicate r true) output) =
      cfg none (decide ((n+r)%d=0), none) [] (List.replicate (d-(n+r)%d) true)
        (List.replicate ((n+r)%d) true) (decide ((n+r)%d=0)::output) := by
  induction n generalizing r with
  | zero =>
      refine ⟨1, by omega, ?_⟩
      simpa only [Nat.zero_add, Nat.mod_eq_of_lt hr, List.replicate_zero, run,
        Function.iterate_one, advance, scan_nil, Option.getD_some]
  | succ n ih =>
      have hd : 0 < d := by omega
      have he : d-r = (d-r-1)+1 := by omega
      by_cases hlast : r+1=d
      · have he' : d-r=1 := by omega
        obtain ⟨t, ht, hrun⟩ := ih 0 hd
        have hmod : (n+1+r)%d = n%d := by
          have : n+1+r=n+d := by omega
          rw [this, Nat.add_mod_right]
        refine ⟨d+3+t, by nlinarith, ?_⟩
        rw [he', List.replicate_succ, List.replicate_succ]
        have hs := scan_cons (decide (r=0)) (List.replicate n true) []
          (List.replicate r true) output
        have hc := check_nil (decide (r=0)) (List.replicate n true)
          (true::List.replicate r true) output
        have hres := restore_run 0 d (decide (r=0), none) (List.replicate n true) output
        have hu : true::List.replicate r true = List.replicate d true := by
          rw [← List.replicate_succ, hlast]
        simp only [List.replicate_zero] at hres ⊢
        rw [show d+3+t = (d+1+t)+1+1 by omega, run_step hs, run_step hc, hu]
        rw [show d+1+t = (d+1)+t by omega, run_add hres]
        simpa only [Nat.zero_add, Nat.add_zero, Nat.sub_zero, List.replicate_zero,
          decide_true, hmod] using hrun
      · have hnext : r+1<d := by omega
        obtain ⟨t, ht, hrun⟩ := ih (r+1) hnext
        have hleft : d-r=(d-(r+1)-1)+2 := by omega
        have hremaining : d-(r+1)=(d-(r+1)-1)+1 := by omega
        have hflag : decide (r+1=0) = false := by simp
        refine ⟨t+2, by nlinarith, ?_⟩
        rw [hleft, List.replicate_succ, List.replicate_succ, List.replicate_succ]
        rw [show t+2=(t+1)+1 by omega,
          run_step (scan_cons (decide (r=0)) (List.replicate n true)
            (true::List.replicate (d-(r+1)-1) true) (List.replicate r true) output),
          run_step (check_cons (decide (r=0)) (List.replicate n true)
            (List.replicate (d-(r+1)-1) true) (true::List.replicate r true) output)]
        rw [hflag, hremaining, List.replicate_succ] at hrun
        simpa only [List.replicate_succ, Nat.add_assoc, Nat.add_comm 1 r] using hrun

/-- An actual division test, with all loop transfers charged. -/
theorem divisibility_run (d n : ℕ) (hd : 0 < d) :
    ∃ t ≤ (d+3)*n+1,
      let c := run t (cfg (some .scan) (true, none) (List.replicate n true)
        (List.replicate d true) [] [])
      c.l = none ∧ c.stk 3 = [decide (d ∣ n)] := by
  obtain ⟨t, ht, h⟩ := remainder_run d n 0 hd []
  refine ⟨t, ht, ?_⟩
  simp only [Nat.add_zero, Nat.sub_zero, List.replicate_zero, decide_true] at h
  dsimp only
  rw [h]
  simp [cfg, bank, Nat.dvd_iff_mod_eq_zero]

end EthInapproximability.CurrentPaper.PrimeSamplerDivision
