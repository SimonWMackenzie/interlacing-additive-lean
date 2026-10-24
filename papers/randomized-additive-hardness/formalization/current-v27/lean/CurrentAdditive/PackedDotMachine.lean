import CurrentAdditive.DotMachine

/-!
A standalone two-stack `BitMachine.Machine` for the coefficient dot product.
Its input is interleaved pairs `x₀,y₀,x₁,y₁,...`. It consumes that input and
emits one bit in `d+1` physical transitions. The bank-preserving routine in
`DotMachine` serves callers that need to retain both input words.
-/

namespace CurrentAdditive.FiniteFieldMachine.PackedDotMachine

open Turing Turing.TM2.Stmt
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper

abbrev Control := Bool × Option Bool × Option Bool
def initial : Control := (false, none, none)

def program : Unit → TM2.Stmt (fun _ : Fin 2 => Bool) Unit Control
  | () => pop 0 (fun s b => (s.1, b, none))
      (branch (fun s => s.2.1.isSome)
        (pop 0 (fun s b => (s.1, s.2.1, b))
          (load (fun s => (s.1 ^^ (s.2.1.getD false && s.2.2.getD false),
            none, none)) (goto (fun _ => ()))))
        (push 1 (fun s => s.1) halt))

def bank (input output : List Bool) : Fin 2 → List Bool :=
  fun k => if k = 0 then input else output

def cfg (l : Option Unit) (s : Control) (input output : List Bool) :
    TM2.Cfg (fun _ : Fin 2 => Bool) Unit Control :=
  ⟨l, s, bank input output⟩

def run (t : ℕ) (q : TM2.Cfg (fun _ : Fin 2 => Bool) Unit Control) :=
  ((advance program)^[t]) q

private theorem run_succ {c d : TM2.Cfg (fun _ : Fin 2 => Bool) Unit Control}
    (h : TM2.step program c = some d) (t : ℕ) : run (t + 1) c = run t d := by
  simp only [run, Function.iterate_succ_apply, advance, h, Option.getD_some]

private theorem step_pair (s : Control) (x y : Bool) (tail out : List Bool) :
    TM2.step program (cfg (some ()) s (x :: y :: tail) out) =
      some (cfg (some ()) (s.1 ^^ (x && y), none, none) tail out) := by
  simp [TM2.step, TM2.stepAux, program, cfg, bank]
  funext k
  fin_cases k <;> rfl

private theorem step_end (s : Control) (out : List Bool) :
    TM2.step program (cfg (some ()) s [] out) =
      some (cfg none (s.1, none, none) [] (s.1 :: out)) := by
  simp [TM2.step, TM2.stepAux, program, cfg, bank]
  funext k
  fin_cases k <;> rfl

def pack : List Bool → List Bool → List Bool
  | x :: xs, y :: ys => x :: y :: pack xs ys
  | _, _ => []

theorem pack_length (x y : List Bool) (h : x.length = y.length) :
    (pack x y).length = 2 * x.length := by
  induction x generalizing y with
  | nil => simp [pack]
  | cons a x ih =>
      cases y with
      | nil => simp at h
      | cons b y =>
          have h' : x.length = y.length := by simpa using h
          simp [pack, ih y h']
          omega

theorem raw_run (s : Control) (x y out : List Bool)
    (h : x.length = y.length) :
    run (x.length + 1) (cfg (some ()) s (pack x y) out) =
      cfg none (DotMachine.dotAux s.1 x y, none, none) []
        (DotMachine.dotAux s.1 x y :: out) := by
  induction x generalizing y s with
  | nil =>
      have hy : y = [] := List.length_eq_zero_iff.mp h.symm
      subst y
      simpa [pack, DotMachine.dotAux] using run_succ (step_end s out) 0
  | cons a x ih =>
      cases y with
      | nil => simp at h
      | cons b y =>
          have h' : x.length = y.length := by simpa using h
          rw [List.length_cons, pack, run_succ (step_pair s a b (pack x y) out)]
          simpa [DotMachine.dotAux] using ih (s.1 ^^ (a && b), none, none) y h'

noncomputable def machine : BitMachine.Machine :=
  ofFinite (0 : Fin 2) 1 () initial program

private theorem init_eq (input : List Bool) :
    rawInit (0 : Fin 2) () initial input = cfg (some ()) initial input [] := by
  rfl

theorem machine_outputs (x y : List Bool) (h : x.length = y.length) :
    machine.OutputsWithin (pack x y) [DotMachine.dotAux false x y] (x.length + 1) := by
  apply outputsWithin_of_raw_run (0 : Fin 2) 1 () initial program
    (pack x y) [DotMachine.dotAux false x y] (x.length + 1) _ le_rfl
  · change (run (x.length + 1) _).l = none
    rw [init_eq, raw_run initial x y [] h]
    rfl
  · change (run (x.length + 1) _).stk 1 = [DotMachine.dotAux false x y]
    rw [init_eq, raw_run initial x y [] h]
    rfl

#print axioms machine_outputs

end CurrentAdditive.FiniteFieldMachine.PackedDotMachine
