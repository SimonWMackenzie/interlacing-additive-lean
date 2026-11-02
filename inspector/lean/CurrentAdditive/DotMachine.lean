import EthInapproximability.CurrentPaper.SamplerMachine

/-!
A physical coefficient dot-product program for the v27 small-bias printer.
Two equal-length little-endian words are restored, one Boolean is prepended
to the output stack, and every temporary stack is cleared. Each invocation
takes exactly `2*d+3` transitions. This is a private development file, not a
claim that the full field printer has been implemented.
-/

namespace CurrentAdditive.FiniteFieldMachine.DotMachine

open Turing Turing.TM2.Stmt EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding

def dotAux : Bool → List Bool → List Bool → Bool
  | acc, x :: xs, y :: ys => dotAux (acc ^^ (x && y)) xs ys
  | acc, _, _ => acc

inductive Label where
  | scan | restore | emit
  deriving DecidableEq, Fintype

abbrev Control := Bool × Option Bool × Option Bool

def initial : Control := (false, none, none)

def program : Label → TM2.Stmt (fun _ : Fin 5 => Bool) Label Control
  | .scan => pop 0 (fun s b => (s.1, b, none))
      (pop 1 (fun s b => (s.1, s.2.1, b))
        (branch (fun s => s.2.1.isSome)
          (push 2 (fun s => s.2.1.getD false)
            (push 3 (fun s => s.2.2.getD false)
              (load (fun s => (s.1 ^^ (s.2.1.getD false && s.2.2.getD false),
                none, none)) (goto (fun _ => .scan)))))
          (goto (fun _ => .restore))))
  | .restore => pop 2 (fun s b => (s.1, b, none))
      (pop 3 (fun s b => (s.1, s.2.1, b))
        (branch (fun s => s.2.1.isSome)
          (push 0 (fun s => s.2.1.getD false)
            (push 1 (fun s => s.2.2.getD false) (goto (fun _ => .restore))))
          (goto (fun _ => .emit))))
  | .emit => push 4 (fun s => s.1) halt

def bank (x y sx sy out : List Bool) : Fin 5 → List Bool :=
  fun k => if k = 0 then x else if k = 1 then y else if k = 2 then sx
    else if k = 3 then sy else out

def cfg (l : Option Label) (s : Control)
    (x y sx sy out : List Bool) : TM2.Cfg (fun _ : Fin 5 => Bool) Label Control :=
  ⟨l, s, bank x y sx sy out⟩

def run (t : ℕ) (q : TM2.Cfg (fun _ : Fin 5 => Bool) Label Control) :=
  ((advance program)^[t]) q

private theorem run_succ {c d : TM2.Cfg (fun _ : Fin 5 => Bool) Label Control}
    (h : TM2.step program c = some d) (t : ℕ) : run (t + 1) c = run t d := by
  simp only [run, Function.iterate_succ_apply, advance, h, Option.getD_some]

private theorem run_add (t u : ℕ)
    (q : TM2.Cfg (fun _ : Fin 5 => Bool) Label Control) :
    run (t + u) q = run u (run t q) := by
  rw [Nat.add_comm t u]
  simp only [run, Function.iterate_add_apply]

private theorem scan_step (s : Control) (x y : Bool)
    (xs ys sx sy out : List Bool) :
    TM2.step program (cfg (some .scan) s (x :: xs) (y :: ys) sx sy out) =
      some (cfg (some .scan) (s.1 ^^ (x && y), none, none)
        xs ys (x :: sx) (y :: sy) out) := by
  simp [TM2.step, TM2.stepAux, program, cfg, bank]
  funext k
  fin_cases k <;> rfl

private theorem scan_end (s : Control) (sx sy out : List Bool) :
    TM2.step program (cfg (some .scan) s [] [] sx sy out) =
      some (cfg (some .restore) (s.1, none, none) [] [] sx sy out) := by
  simp [TM2.step, TM2.stepAux, program, cfg, bank]
  funext k
  fin_cases k <;> rfl

private theorem restore_step (s : Control) (x y : Bool)
    (xs ys sx sy out : List Bool) :
    TM2.step program (cfg (some .restore) s xs ys (x :: sx) (y :: sy) out) =
      some (cfg (some .restore) (s.1, some x, some y)
        (x :: xs) (y :: ys) sx sy out) := by
  simp [TM2.step, TM2.stepAux, program, cfg, bank]
  funext k
  fin_cases k <;> rfl

private theorem restore_end (s : Control) (xs ys out : List Bool) :
    TM2.step program (cfg (some .restore) s xs ys [] [] out) =
      some (cfg (some .emit) (s.1, none, none) xs ys [] [] out) := by
  simp [TM2.step, TM2.stepAux, program, cfg, bank]
  funext k
  fin_cases k <;> rfl

private theorem emit_step (s : Control) (xs ys out : List Bool) :
    TM2.step program (cfg (some .emit) s xs ys [] [] out) =
      some (cfg none s xs ys [] [] (s.1 :: out)) := by
  simp [TM2.step, TM2.stepAux, program, cfg, bank]
  funext k
  fin_cases k <;> rfl

theorem scan_run (s : Control) (xs ys sx sy out : List Bool)
    (hlen : xs.length = ys.length) :
    run (xs.length + 1) (cfg (some .scan) s xs ys sx sy out) =
      cfg (some .restore) (dotAux s.1 xs ys, none, none) [] []
        (xs.reverse ++ sx) (ys.reverse ++ sy) out := by
  induction xs generalizing ys s sx sy with
  | nil =>
      have hy : ys = [] := List.length_eq_zero_iff.mp hlen.symm
      subst ys
      simpa [dotAux] using run_succ (scan_end s sx sy out) 0
  | cons x xs ih =>
      cases ys with
      | nil => simp at hlen
      | cons y ys =>
          have h : xs.length = ys.length := by simpa using hlen
          rw [List.length_cons, run_succ (scan_step s x y xs ys sx sy out)]
          simpa [dotAux, List.reverse_cons, List.append_assoc] using
            ih (s.1 ^^ (x && y), none, none) ys (x :: sx) (y :: sy) h

theorem restore_run (s : Control) (xs ys sx sy out : List Bool)
    (hlen : sx.length = sy.length) :
    run (sx.length + 1) (cfg (some .restore) s xs ys sx sy out) =
      cfg (some .emit) (s.1, none, none)
        (sx.reverse ++ xs) (sy.reverse ++ ys) [] [] out := by
  induction sx generalizing sy s xs ys with
  | nil =>
      have hy : sy = [] := List.length_eq_zero_iff.mp hlen.symm
      subst sy
      simpa using run_succ (restore_end s xs ys out) 0
  | cons x sx ih =>
      cases sy with
      | nil => simp at hlen
      | cons y sy =>
          have h : sx.length = sy.length := by simpa using hlen
          rw [List.length_cons, run_succ (restore_step s x y xs ys sx sy out)]
          simpa [List.reverse_cons, List.append_assoc] using
            ih (s.1, some x, some y) (x :: xs) (y :: ys) sy h

/-- Exact physical run of the finite program, including preserved input words. -/
theorem run_dot (x y out : List Bool) (hlen : x.length = y.length) :
    run (2 * x.length + 3) (cfg (some .scan) initial x y [] [] out) =
      cfg none (dotAux false x y, none, none)
        x y [] [] (dotAux false x y :: out) := by
  have hs := scan_run initial x y [] [] out hlen
  simp only [List.append_nil] at hs
  have hr := restore_run (dotAux false x y, none, none) [] [] x.reverse y.reverse out
    (by simp [hlen])
  simp only [List.length_reverse, List.reverse_reverse, List.append_nil] at hr
  simp only [initial] at hs ⊢
  rw [show 2 * x.length + 3 =
      (x.length + 1) + ((x.length + 1) + 1) by omega,
    run_add, hs, run_add, hr]
  simpa using run_succ (emit_step (dotAux false x y, none, none) x y out) 0

/-- The output is the exact least-significant-coefficient dot product used
by `BitPrinter.dot`, rather than a trace-pairing surrogate. -/
def natBits (d x : ℕ) : List Bool :=
  (List.range d).map (fun i => x.testBit i)

theorem dotAux_natBits (acc : Bool) (indices : List ℕ) (x z : ℕ) :
    dotAux acc (indices.map (fun i => x.testBit i))
      (indices.map (fun i => z.testBit i)) =
    indices.foldl (fun a i => a ^^ (x.testBit i && z.testBit i)) acc := by
  induction indices generalizing acc with
  | nil => rfl
  | cons i is ih =>
      simp only [List.map_cons, List.foldl_cons, dotAux]
      exact ih (acc ^^ (x.testBit i && z.testBit i))

theorem run_natBits_dot (d x z : ℕ) (out : List Bool) :
    run (2 * d + 3) (cfg (some .scan) initial (natBits d x) (natBits d z) [] [] out) =
      cfg none
        ((List.range d).foldl
          (fun acc i => acc ^^ (x.testBit i && z.testBit i)) false, none, none)
        (natBits d x) (natBits d z) [] []
        ((List.range d).foldl
          (fun acc i => acc ^^ (x.testBit i && z.testBit i)) false :: out) := by
  have h := run_dot (natBits d x) (natBits d z) out (by simp [natBits])
  simpa only [natBits, List.length_map, List.length_range,
    dotAux_natBits] using h

#print axioms run_dot
#print axioms run_natBits_dot

end CurrentAdditive.FiniteFieldMachine.DotMachine
