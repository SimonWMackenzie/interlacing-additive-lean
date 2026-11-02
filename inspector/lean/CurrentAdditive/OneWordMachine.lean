import EthInapproximability.CurrentPaper.BitMachineEncoding

/-! Physical setup of the coefficient word for the constant polynomial one.
The width is witnessed by an already supplied d-bit bank, which is restored.
No dimension-sized state space or free stack initialization is used. -/

namespace CurrentAdditive.FiniteFieldMachine.OneWordMachine

open Turing Turing.TM2.Stmt
open EthInapproximability.CurrentPaper.BitMachineEncoding

inductive Label where
  | scan | restore
  deriving DecidableEq, Fintype

inductive Stack where
  | width | savedWidth | tempOne | one
  deriving DecidableEq, Fintype

abbrev Control := Bool × Option Bool × Option Bool
abbrev Config := TM2.Cfg (fun _ : Stack => Bool) Label Control

def initial : Control := (true, none, none)

def program : Label → TM2.Stmt (fun _ : Stack => Bool) Label Control
  | .scan => pop .width (fun s b => (s.1, b, none))
      (branch (fun s => s.2.1.isSome)
        (push .savedWidth (fun s => s.2.1.getD false)
          (push .tempOne (fun s => s.1)
            (load (fun _ => (false, none, none)) (goto (fun _ => .scan)))))
        (goto (fun _ => .restore)))
  | .restore => pop .savedWidth (fun s b => (s.1, b, none))
      (branch (fun s => s.2.1.isSome)
        (pop .tempOne (fun s b => (s.1, s.2.1, b))
          (push .width (fun s => s.2.1.getD false)
            (push .one (fun s => s.2.2.getD false)
              (goto (fun _ => .restore)))))
        (load (fun _ => initial) halt))

def contents (width saved temp output : List Bool) : Stack → List Bool
  | .width => width | .savedWidth => saved | .tempOne => temp | .one => output

def cfg (l : Option Label) (s : Control)
    (width saved temp output : List Bool) : Config :=
  ⟨l, s, contents width saved temp output⟩

def run (t : ℕ) (q : Config) := ((advance program)^[t]) q

private theorem run_succ {q r : Config} (h : TM2.step program q = some r) (t : ℕ) :
    run (t + 1) q = run t r := by
  simp only [run, Function.iterate_succ_apply, advance, h, Option.getD_some]

private theorem run_add (t u : ℕ) (q : Config) :
    run (t + u) q = run u (run t q) := by
  rw [Nat.add_comm t u]
  simp only [run, Function.iterate_add_apply]

private theorem step_scan_cons (s : Control) (b : Bool)
    (width saved temp output : List Bool) :
    TM2.step program (cfg (some .scan) s (b :: width) saved temp output) =
      some (cfg (some .scan) (false, none, none)
        width (b :: saved) (s.1 :: temp) output) := by
  dsimp only [TM2.step, TM2.stepAux, program, cfg, contents]
  simp only [List.head?_cons, List.tail_cons, Option.isSome_some,
    Option.getD_some, Bool.cond_true, Option.some.injEq]
  congr 1
  funext k
  cases k <;> rfl

private theorem step_scan_nil (s : Control)
    (saved temp output : List Bool) :
    TM2.step program (cfg (some .scan) s [] saved temp output) =
      some (cfg (some .restore) (s.1, none, none)
        [] saved temp output) := by
  dsimp only [TM2.step, TM2.stepAux, program, cfg, contents]
  simp only [List.head?_nil, List.tail_nil, Option.isSome_none,
    Bool.cond_false, Option.some.injEq]
  congr 1
  funext k
  cases k <;> rfl

private theorem step_restore_cons (s : Control) (b z : Bool)
    (width saved temp output : List Bool) :
    TM2.step program (cfg (some .restore) s
      width (b :: saved) (z :: temp) output) =
    some (cfg (some .restore) (s.1, some b, some z)
      (b :: width) saved temp (z :: output)) := by
  dsimp only [TM2.step, TM2.stepAux, program, cfg, contents]
  simp only [List.head?_cons, List.tail_cons, Option.isSome_some,
    Option.getD_some, Bool.cond_true, Option.some.injEq]
  congr 1
  funext k
  cases k <;> rfl

private theorem step_restore_nil (s : Control)
    (width temp output : List Bool) :
    TM2.step program (cfg (some .restore) s width [] temp output) =
    some (cfg none initial width [] temp output) := by
  dsimp only [TM2.step, TM2.stepAux, program, cfg, contents]
  simp only [List.head?_nil, List.tail_nil, Option.isSome_none,
    Bool.cond_false, Option.some.injEq]
  congr 1
  funext k
  cases k <;> rfl

theorem scan_false_run (width saved temp output : List Bool) :
    run (width.length + 1)
      (cfg (some .scan) (false, none, none) width saved temp output) =
    cfg (some .restore) (false, none, none) []
      (width.reverse ++ saved)
      (List.replicate width.length false ++ temp) output := by
  induction width generalizing saved temp with
  | nil => simpa using (run_succ
      (step_scan_nil (false, none, none) saved temp output) 0)
  | cons b width ih =>
      rw [List.length_cons, run_succ
        (step_scan_cons (false, none, none) b width saved temp output)]
      simpa only [List.reverse_cons, List.replicate_succ',
        List.append_assoc, List.singleton_append] using
        ih (b :: saved) (false :: temp)

theorem scan_positive_run (b : Bool) (width output : List Bool) :
    run ((b :: width).length + 1)
      (cfg (some .scan) initial (b :: width) [] [] output) =
    cfg (some .restore) (false, none, none) []
      (b :: width).reverse
      (List.replicate width.length false ++ [true]) output := by
  rw [List.length_cons, run_succ
    (step_scan_cons initial b width [] [] output)]
  simpa [initial, List.reverse_cons] using
    scan_false_run width [b] [true] output

theorem restore_run (s : Control)
    (width saved temp output : List Bool)
    (hlen : saved.length = temp.length) :
    run (saved.length + 1)
      (cfg (some .restore) s width saved temp output) =
    cfg none initial (saved.reverse ++ width) [] []
      (temp.reverse ++ output) := by
  induction saved generalizing s width temp output with
  | nil =>
      have ht : temp = [] := List.length_eq_zero_iff.mp hlen.symm
      subst temp
      simpa using run_succ (step_restore_nil s width [] output) 0
  | cons b saved ih =>
      cases temp with
      | nil => simp at hlen
      | cons z temp =>
          have h : saved.length = temp.length := by simpa using hlen
          rw [List.length_cons, run_succ
            (step_restore_cons s b z width saved temp output)]
          simpa only [List.reverse_cons, List.append_assoc,
            List.singleton_append] using
            ih (s.1, some b, some z) (b :: width) temp (z :: output) h

/-- An already supplied nonempty width word is restored; a fresh little-endian
constant-one word is generated in two linear passes. -/
theorem run_one (b : Bool) (width : List Bool) :
    run (2 * (b :: width).length + 2)
      (cfg (some .scan) initial (b :: width) [] [] []) =
    cfg none initial (b :: width) [] []
      (true :: List.replicate width.length false) := by
  have hs := scan_positive_run b width []
  have hr := restore_run (false, none, none) []
    (b :: width).reverse
    (List.replicate width.length false ++ [true]) []
    (by simp)
  simp only [List.length_reverse, List.reverse_reverse,
    List.append_nil, List.reverse_append,
    List.reverse_replicate, List.reverse_singleton] at hr
  have ht : 2 * (b :: width).length + 2 =
      ((b :: width).length + 1) + ((b :: width).length + 1) := by omega
  rw [ht, run_add, hs, hr]
  simp only [List.singleton_append]

#print axioms run_one

end CurrentAdditive.FiniteFieldMachine.OneWordMachine
