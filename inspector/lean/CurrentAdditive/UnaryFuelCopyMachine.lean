import EthInapproximability.CurrentPaper.BitMachineEncoding

/-! A physical reusable unary-fuel copy for repeated seed runs. The source
counter is restored, and the working fuel is prepended in one scan and one
restore pass. -/

namespace CurrentAdditive.FiniteFieldMachine.UnaryFuelCopyMachine

open Turing Turing.TM2.Stmt
open EthInapproximability.CurrentPaper.BitMachineEncoding

inductive Label where
  | scan | restore
  deriving DecidableEq, Fintype

abbrev Stack := Fin 3
abbrev Control := Option Bool
abbrev Config := TM2.Cfg (fun _ : Stack => Bool) Label Control

def source : Stack := 0
def saved : Stack := 1
def fuel : Stack := 2

def program : Label → TM2.Stmt (fun _ : Stack => Bool) Label Control
  | .scan => pop source (fun _ b => b)
      (branch (fun s => s.isSome)
        (push saved (fun s => s.getD false)
          (push fuel (fun s => s.getD false) (goto (fun _ => .scan))))
        (goto (fun _ => .restore)))
  | .restore => pop saved (fun _ b => b)
      (branch (fun s => s.isSome)
        (push source (fun s => s.getD false) (goto (fun _ => .restore)))
        halt)

def cfg (l : Option Label) (s : Control)
    (src tmp out : List Bool) : Config :=
  ⟨l, s, fun k => if k = 0 then src else if k = 1 then tmp else out⟩

def run (t : ℕ) (q : Config) := ((advance program)^[t]) q

private theorem run_succ {q r : Config} (h : TM2.step program q = some r) (t : ℕ) :
    run (t + 1) q = run t r := by
  simp only [run, Function.iterate_succ_apply, advance, h, Option.getD_some]

private theorem run_add (t u : ℕ) (q : Config) :
    run (t + u) q = run u (run t q) := by
  rw [Nat.add_comm t u]
  simp only [run, Function.iterate_add_apply]

private theorem step_scan_cons (s : Control) (b : Bool)
    (src tmp out : List Bool) :
    TM2.step program (cfg (some .scan) s (b :: src) tmp out) =
      some (cfg (some .scan) (some b) src (b :: tmp) (b :: out)) := by
  dsimp only [TM2.step, TM2.stepAux, program, cfg, source, saved, fuel]
  simp only [↓reduceIte, List.head?_cons, List.tail_cons, Option.isSome_some,
    Option.getD_some, Bool.cond_true, Option.some.injEq]
  congr 1
  funext k
  fin_cases k <;> rfl

private theorem step_scan_nil (s : Control) (tmp out : List Bool) :
    TM2.step program (cfg (some .scan) s [] tmp out) =
      some (cfg (some .restore) none [] tmp out) := by
  dsimp only [TM2.step, TM2.stepAux, program, cfg, source]
  simp only [↓reduceIte, List.head?_nil, List.tail_nil, Option.isSome_none,
    Bool.cond_false, Option.some.injEq]
  congr 1
  funext k
  fin_cases k <;> rfl

private theorem step_restore_cons (s : Control) (b : Bool)
    (src tmp out : List Bool) :
    TM2.step program (cfg (some .restore) s src (b :: tmp) out) =
      some (cfg (some .restore) (some b) (b :: src) tmp out) := by
  dsimp only [TM2.step, TM2.stepAux, program, cfg, source, saved]
  simp only [show (1 : Fin 3) ≠ 0 by decide, if_neg, ↓reduceIte,
    List.head?_cons, List.tail_cons, Option.isSome_some,
    Option.getD_some, Bool.cond_true, Option.some.injEq]
  congr 1
  funext k
  fin_cases k <;> rfl

private theorem step_restore_nil (s : Control) (src out : List Bool) :
    TM2.step program (cfg (some .restore) s src [] out) =
      some (cfg none none src [] out) := by
  dsimp only [TM2.step, TM2.stepAux, program, cfg, saved]
  simp only [show (1 : Fin 3) ≠ 0 by decide, if_neg, ↓reduceIte,
    List.head?_nil, List.tail_nil, Option.isSome_none,
    Bool.cond_false, Option.some.injEq]
  congr 1
  funext k
  fin_cases k <;> rfl

theorem scan_run (s : Control) (src tmp out : List Bool) :
    run (src.length + 1) (cfg (some .scan) s src tmp out) =
      cfg (some .restore) none [] (src.reverse ++ tmp)
        (src.reverse ++ out) := by
  induction src generalizing s tmp out with
  | nil => simpa using run_succ (step_scan_nil s tmp out) 0
  | cons b src ih =>
      rw [List.length_cons, run_succ (step_scan_cons s b src tmp out)]
      simpa only [List.reverse_cons, List.append_assoc,
        List.singleton_append] using ih (some b) (b :: tmp) (b :: out)

theorem restore_run (s : Control) (src tmp out : List Bool) :
    run (tmp.length + 1) (cfg (some .restore) s src tmp out) =
      cfg none none (tmp.reverse ++ src) [] out := by
  induction tmp generalizing s src with
  | nil => simpa using run_succ (step_restore_nil s src out) 0
  | cons b tmp ih =>
      rw [List.length_cons, run_succ (step_restore_cons s b src tmp out)]
      simpa only [List.reverse_cons, List.append_assoc,
        List.singleton_append] using ih (some b) (b :: src)

/-- The already supplied unary source is restored, while the working fuel
gets one copy. This charges both the scan and restore passes. -/
theorem run_copy (src out : List Bool) :
    run (2 * src.length + 2) (cfg (some .scan) none src [] out) =
      cfg none none src [] (src.reverse ++ out) := by
  have hs := scan_run none src [] out
  simp only [List.append_nil] at hs
  have hr := restore_run none [] src.reverse (src.reverse ++ out)
  simp only [List.length_reverse, List.reverse_reverse,
    List.append_nil] at hr
  have ht : 2 * src.length + 2 = (src.length + 1) + (src.length + 1) := by omega
  rw [ht, run_add, hs, hr]

theorem run_unary_fuel (n : ℕ) :
    run (2 * n + 2)
      (cfg (some .scan) none (List.replicate n true) [] []) =
    cfg none none (List.replicate n true) [] (List.replicate n true) := by
  simpa only [List.length_replicate, List.reverse_replicate,
    List.append_nil] using run_copy (List.replicate n true) []

#print axioms run_unary_fuel

end CurrentAdditive.FiniteFieldMachine.UnaryFuelCopyMachine
