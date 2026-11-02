import EthInapproximability.CurrentPaper.BitMachineEncoding

/-! Literal Boolean-stack equality test for two prepared cylinder-symbol words.
The banks are consumed one bit at a time; the only work control is a Boolean
equality flag and two optional bits. -/

namespace CurrentAdditive.CylinderEqualMachine

open Turing Turing.TM2.Stmt
open EthInapproximability.CurrentPaper.BitMachineEncoding

inductive Label where
  | scan
  deriving DecidableEq, Fintype

abbrev Control := Bool × Option Bool × Option Bool
abbrev Config := TM2.Cfg (fun _ : Fin 3 => Bool) Label Control

def program : Label → TM2.Stmt (fun _ : Fin 3 => Bool) Label Control
  | .scan =>
      pop 0 (fun v a => (v.1, a, v.2.2))
        (pop 1 (fun v b => (v.1, v.2.1, b))
          (branch (fun v => v.2.1.isSome && v.2.2.isSome)
            (load (fun v => (v.1 && (v.2.1 == v.2.2), none, none))
              (goto (fun _ => .scan)))
            (push 2 (fun v => v.1 && (!v.2.1.isSome && !v.2.2.isSome)) halt)))

def bank (left right output : List Bool) : Fin 3 → List Bool :=
  fun k => if k = 0 then left else if k = 1 then right else output

def cfg (l : Option Label) (v : Control)
    (left right output : List Bool) : Config := ⟨l, v, bank left right output⟩

def run (t : Nat) (c : Config) : Config := ((advance program)^[t]) c

private theorem run_add (t u : Nat) (c : Config) :
    run (t + u) c = run u (run t c) := by
  rw [Nat.add_comm t u]
  simp [run, Function.iterate_add_apply]

private theorem step_pair (e : Bool) (a b : Bool)
    (xs ys out : List Bool) :
    advance program (cfg (some .scan) (e, none, none)
      (a :: xs) (b :: ys) out) =
    cfg (some .scan) (e && (a == b), none, none) xs ys out := by
  simp [advance, TM2.step, TM2.stepAux, program, cfg, bank]
  funext k
  fin_cases k <;> rfl

private theorem left_end (e : Bool) (ys out : List Bool) :
    (run 1 (cfg (some .scan) (e, none, none) [] ys out)).l = none ∧
    (run 1 (cfg (some .scan) (e, none, none) [] ys out)).stk 2 =
      (e && ys.isEmpty) :: out := by
  cases ys <;> simp [run, advance,
    TM2.step, TM2.stepAux, program, cfg, bank]

private theorem right_end (e : Bool) (a : Bool)
    (xs out : List Bool) :
    (run 1 (cfg (some .scan) (e, none, none) (a :: xs) [] out)).l = none ∧
    (run 1 (cfg (some .scan) (e, none, none) (a :: xs) [] out)).stk 2 =
      false :: out := by
  simp [run, advance,
    TM2.step, TM2.stepAux, program, cfg, bank]

theorem compare_run (e : Bool) (left right out : List Bool) :
    ∃ t ≤ min left.length right.length + 1,
      (run t (cfg (some .scan) (e, none, none) left right out)).l = none ∧
      (run t (cfg (some .scan) (e, none, none) left right out)).stk 2 =
        (e && decide (left = right)) :: out := by
  induction left generalizing right e with
  | nil =>
      refine ⟨1, by simp, ?_, ?_⟩
      · exact (left_end e right out).1
      · have h := (left_end e right out).2
        cases right <;> simpa using h
  | cons a xs ih =>
      cases right with
      | nil =>
          refine ⟨1, by simp, ?_, ?_⟩
          · exact (right_end e a xs out).1
          · simpa using (right_end e a xs out).2
      | cons b ys =>
          obtain ⟨t, ht, hhalt, hout⟩ := ih (e && (a == b)) ys
          refine ⟨t + 1, by simpa using Nat.add_le_add_right ht 1, ?_, ?_⟩
          · rw [show t + 1 = 1 + t by omega, run_add]
            simpa only [run, Function.iterate_one, step_pair] using hhalt
          · rw [show t + 1 = 1 + t by omega, run_add]
            simpa [run, Function.iterate_one, step_pair, Bool.and_assoc] using hout

#print axioms compare_run

end CurrentAdditive.CylinderEqualMachine
