import CurrentAdditive.HornerNatBridge
import CurrentAdditive.DotMachine

/-!
A literal finite Boolean-stack controller for one seed's *streaming* dot
bits and successive powers. The program is separate from field selection
and label/table enumeration. Its multiplication branch reuses the checked
arbitrary-modulus `SamplerMachineProduct.program`.
-/

namespace CurrentAdditive.FiniteFieldMachine.StreamingBitMachine

set_option maxRecDepth 4096

open Turing Turing.TM2.Stmt
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper.BitMachineComposition
open EthInapproximability.CurrentPaper.SamplerMachine
open CurrentAdditive.FiniteFieldConstructor.BitPolynomialBridge
open CurrentAdditive.FiniteFieldConstructor.BitPrinter
open CurrentAdditive.FiniteFieldMachine.HornerNatBridge

inductive Admin where
  | check | dotScan | dotRestore | move | zero
  deriving DecidableEq, Fintype

abbrev Stack := SamplerMachineProduct.Stack ⊕ Fin 5
abbrev Label := SamplerMachineProduct.Label ⊕ Admin
abbrev Control := SamplerMachineProduct.Control × (Bool × Option Bool × Option Bool)
abbrev Config := TM2.Cfg (fun _ : Stack => Bool) Label Control

def initial : Control := (SamplerMachineProduct.initial, false, none, none)

def acc : Stack := .inl (.inl 0)
def base : Stack := .inl (.inl 1)
def work : Stack := .inl (.inl 2)
def modulusBank : Stack := .inl (.inr 0)
def multiplier : Stack := .inl (.inr 1)
def fuelBank : Stack := .inr 0
def seed : Stack := .inr 1
def savedSeed : Stack := .inr 2
def savedAcc : Stack := .inr 3
def output : Stack := .inr 4

def program : Label → TM2.Stmt (fun _ : Stack => Bool) Label Control
  | .inl l => liftStmt (some .check) (SamplerMachineProduct.program l)
  | .inr .check => pop fuelBank (fun s b => (s.1, false, b, none))
      (branch (fun s => s.2.2.1.isSome)
        (goto (fun _ => .inr .dotScan))
        (load (fun _ => initial) halt))
  | .inr .dotScan => pop seed (fun s b => (s.1, s.2.1, b, none))
      (pop acc (fun s b => (s.1, s.2.1, s.2.2.1, b))
        (branch (fun s => s.2.2.1.isSome)
          (push savedSeed (fun s => s.2.2.1.getD false)
            (push savedAcc (fun s => s.2.2.2.getD false)
              (load (fun s =>
                (s.1, s.2.1 ^^ (s.2.2.1.getD false && s.2.2.2.getD false),
                  none, none)) (goto (fun _ => .inr .dotScan)))))
          (goto (fun _ => .inr .dotRestore))))
  | .inr .dotRestore => pop savedSeed (fun s b => (s.1, s.2.1, b, none))
      (pop savedAcc (fun s b => (s.1, s.2.1, s.2.2.1, b))
        (branch (fun s => s.2.2.1.isSome)
          (push seed (fun s => s.2.2.1.getD false)
            (push acc (fun s => s.2.2.2.getD false)
              (goto (fun _ => .inr .dotRestore))))
          (push output (fun s => s.2.1)
            (load (fun _ => initial) (goto (fun _ => .inr .move))))))
  | .inr .move => pop acc (fun s b => (s.1, s.2.1, b, none))
      (branch (fun s => s.2.2.1.isSome)
        (push multiplier (fun s => s.2.2.1.getD false)
          (push work (fun _ => false) (goto (fun _ => .inr .move))))
        (goto (fun _ => .inr .zero)))
  | .inr .zero => pop work (fun s b => (s.1, s.2.1, b, none))
      (branch (fun s => s.2.2.1.isSome)
        (push acc (fun _ => false) (goto (fun _ => .inr .zero)))
        (load (fun _ => initial) (goto (fun _ => .inl (.inr (.inr ()))))))

def foreign (fuel x sx sa out : List Bool) : Fin 5 → List Bool :=
  fun i => if i = 0 then fuel else if i = 1 then x else if i = 2 then sx
    else if i = 3 then sa else out

def cfg (l : Option Label) (s : Control)
    (a y wa wo c m fuel x sx sa out : List Bool) : Config :=
  ⟨l, s, Sum.elim (SamplerMachineProduct.cfg none s.1 a y wa wo c m).stk
    (foreign fuel x sx sa out)⟩

def run (t : ℕ) (q : Config) := ((advance program)^[t]) q

theorem run_succ {c e : Config} (h : TM2.step program c = some e) (t : ℕ) :
    run (t + 1) c = run t e := by
  simp only [run, Function.iterate_succ_apply, advance, h, Option.getD_some]

theorem run_add (t u : ℕ) (q : Config) :
    run (t + u) q = run u (run t q) := by
  rw [Nat.add_comm t u]
  simp only [run, Function.iterate_add_apply]

private theorem step_check_cons (s : Control) (b : Bool)
    (a y wa wo c m fuel x sx sa out : List Bool) :
    TM2.step program (cfg (some (.inr .check)) s
      a y wa wo c m (b :: fuel) x sx sa out) =
    some (cfg (some (.inr .dotScan)) (s.1, false, some b, none)
      a y wa wo c m fuel x sx sa out) := by
  dsimp only [TM2.step, TM2.stepAux, program, cfg, foreign, fuelBank,
    Sum.elim_inl, Sum.elim_inr]
  simp only [↓reduceIte, List.head?_cons, List.tail_cons, Option.isSome_some,
    Bool.cond_true, Option.some.injEq]
  congr 1
  funext k
  rcases k with (k | k) | k <;> (try fin_cases k) <;> rfl

theorem step_check_nil (s : Control)
    (a y wa wo c m x sx sa out : List Bool) :
    TM2.step program (cfg (some (.inr .check)) s
      a y wa wo c m [] x sx sa out) =
    some (cfg none initial a y wa wo c m [] x sx sa out) := by
  dsimp only [TM2.step, TM2.stepAux, program, cfg, foreign, fuelBank,
    Sum.elim_inl, Sum.elim_inr]
  simp only [↓reduceIte, List.head?_nil, List.tail_nil, Option.isSome_none,
    Bool.cond_false, Option.some.injEq]
  congr 1
  funext k
  rcases k with (k | k) | k <;> (try fin_cases k) <;> rfl

private theorem step_dotScan_pair (s : Control) (xb ab : Bool)
    (a y wa wo c m fuel x sx sa out : List Bool) :
    TM2.step program (cfg (some (.inr .dotScan)) s
      (ab :: a) y wa wo c m fuel (xb :: x) sx sa out) =
    some (cfg (some (.inr .dotScan))
      (s.1, s.2.1 ^^ (xb && ab), none, none)
      a y wa wo c m fuel x (xb :: sx) (ab :: sa) out) := by
  dsimp only [TM2.step, TM2.stepAux, program, cfg, foreign,
    acc, seed, savedSeed, savedAcc, SamplerMachineProduct.cfg,
    SamplerMachineProduct.foreign, SamplerMachineAccumulate.stackContents,
    Sum.elim_inl, Sum.elim_inr]
  simp only [show (1 : Fin 5) ≠ 0 by decide, if_neg, ↓reduceIte,
    List.head?_cons, List.tail_cons,
    Option.isSome_some, Option.getD_some, Bool.cond_true, Option.some.injEq]
  congr 1
  funext k
  rcases k with (k | k) | k <;> (try fin_cases k) <;> rfl

private theorem step_dotScan_nil (s : Control)
    (y wa wo c m fuel sx sa out : List Bool) :
    TM2.step program (cfg (some (.inr .dotScan)) s
      [] y wa wo c m fuel [] sx sa out) =
    some (cfg (some (.inr .dotRestore)) (s.1, s.2.1, none, none)
      [] y wa wo c m fuel [] sx sa out) := by
  dsimp only [TM2.step, TM2.stepAux, program, cfg, foreign,
    acc, seed, SamplerMachineProduct.cfg, SamplerMachineProduct.foreign,
    SamplerMachineAccumulate.stackContents, Sum.elim_inl, Sum.elim_inr]
  simp only [show (1 : Fin 5) ≠ 0 by decide, if_neg, ↓reduceIte,
    List.head?_nil, List.tail_nil,
    Option.isSome_none, Bool.cond_false, Option.some.injEq]
  congr 1
  funext k
  rcases k with (k | k) | k <;> (try fin_cases k) <;> rfl

private theorem step_dotRestore_pair (s : Control) (xb ab : Bool)
    (a y wa wo c m fuel x sx sa out : List Bool) :
    TM2.step program (cfg (some (.inr .dotRestore)) s
      a y wa wo c m fuel x (xb :: sx) (ab :: sa) out) =
    some (cfg (some (.inr .dotRestore)) (s.1, s.2.1, some xb, some ab)
      (ab :: a) y wa wo c m fuel (xb :: x) sx sa out) := by
  dsimp only [TM2.step, TM2.stepAux, program, cfg, foreign,
    acc, seed, savedSeed, savedAcc, SamplerMachineProduct.cfg,
    SamplerMachineProduct.foreign, SamplerMachineAccumulate.stackContents,
    Sum.elim_inl, Sum.elim_inr]
  simp only [show (2 : Fin 5) ≠ 0 by decide,
    show (2 : Fin 5) ≠ 1 by decide,
    show (3 : Fin 5) ≠ 0 by decide,
    show (3 : Fin 5) ≠ 1 by decide,
    show (3 : Fin 5) ≠ 2 by decide,
    if_neg, ↓reduceIte, List.head?_cons, List.tail_cons,
    Option.isSome_some, Option.getD_some, Bool.cond_true, Option.some.injEq]
  congr 1
  funext k
  rcases k with (k | k) | k <;> (try fin_cases k) <;> rfl

private theorem step_dotRestore_nil (s : Control)
    (a y wa wo c m fuel x out : List Bool) :
    TM2.step program (cfg (some (.inr .dotRestore)) s
      a y wa wo c m fuel x [] [] out) =
    some (cfg (some (.inr .move)) initial
      a y wa wo c m fuel x [] [] (s.2.1 :: out)) := by
  dsimp only [TM2.step, TM2.stepAux, program, cfg, foreign,
    savedSeed, savedAcc, output, SamplerMachineProduct.cfg,
    SamplerMachineProduct.foreign, SamplerMachineAccumulate.stackContents,
    Sum.elim_inl, Sum.elim_inr]
  simp only [show (2 : Fin 5) ≠ 0 by decide,
    show (2 : Fin 5) ≠ 1 by decide,
    show (3 : Fin 5) ≠ 0 by decide,
    show (3 : Fin 5) ≠ 1 by decide,
    show (3 : Fin 5) ≠ 2 by decide,
    if_neg, ↓reduceIte, List.head?_nil, List.tail_nil,
    Option.isSome_none, Bool.cond_false, Option.some.injEq]
  congr 1
  funext k
  rcases k with (k | k) | k <;> (try fin_cases k) <;> rfl

theorem dotScan_run (s : Control)
    (a y wa wo c m fuel x sx sa out : List Bool)
    (hlen : x.length = a.length) :
    run (x.length + 1) (cfg (some (.inr .dotScan)) s
      a y wa wo c m fuel x sx sa out) =
    cfg (some (.inr .dotRestore))
      (s.1, DotMachine.dotAux s.2.1 x a, none, none)
      [] y wa wo c m fuel [] (x.reverse ++ sx) (a.reverse ++ sa) out := by
  induction x generalizing a s sx sa with
  | nil =>
      have ha : a = [] := List.length_eq_zero_iff.mp hlen.symm
      subst a
      simpa [DotMachine.dotAux] using
        run_succ (step_dotScan_nil s y wa wo c m fuel sx sa out) 0
  | cons xb x ih =>
      cases a with
      | nil => simp at hlen
      | cons ab a =>
          have h : x.length = a.length := by simpa using hlen
          rw [List.length_cons, run_succ
            (step_dotScan_pair s xb ab a y wa wo c m fuel x sx sa out)]
          simpa [DotMachine.dotAux, List.reverse_cons, List.append_assoc] using
            ih (s.1, s.2.1 ^^ (xb && ab), none, none) a (xb :: sx) (ab :: sa) h

theorem dotRestore_run (s : Control)
    (a y wa wo c m fuel x sx sa out : List Bool)
    (hlen : sx.length = sa.length) :
    run (sx.length + 1) (cfg (some (.inr .dotRestore)) s
      a y wa wo c m fuel x sx sa out) =
    cfg (some (.inr .move)) initial
      (sa.reverse ++ a) y wa wo c m fuel (sx.reverse ++ x) [] []
      (s.2.1 :: out) := by
  induction sx generalizing sa s a x with
  | nil =>
      have ha : sa = [] := List.length_eq_zero_iff.mp hlen.symm
      subst sa
      simpa using run_succ (step_dotRestore_nil s a y wa wo c m fuel x out) 0
  | cons xb sx ih =>
      cases sa with
      | nil => simp at hlen
      | cons ab sa =>
          have h : sx.length = sa.length := by simpa using hlen
          rw [List.length_cons, run_succ
            (step_dotRestore_pair s xb ab a y wa wo c m fuel x sx sa out)]
          simpa [List.reverse_cons, List.append_assoc] using
            ih (s.1, s.2.1, some xb, some ab) (ab :: a) (xb :: x) sa h

private theorem step_move_cons (s : Control) (b : Bool)
    (a y wa wo c m fuel x sx sa out : List Bool) :
    TM2.step program (cfg (some (.inr .move)) s
      (b :: a) y wa wo c m fuel x sx sa out) =
    some (cfg (some (.inr .move)) (s.1, s.2.1, some b, none)
      a y (false :: wa) wo c (b :: m) fuel x sx sa out) := by
  dsimp only [TM2.step, TM2.stepAux, program, cfg, foreign,
    acc, multiplier, work, SamplerMachineProduct.cfg,
    SamplerMachineProduct.foreign, SamplerMachineAccumulate.stackContents,
    Sum.elim_inl, Sum.elim_inr]
  simp only [↓reduceIte, List.head?_cons, List.tail_cons, Option.isSome_some,
    Option.getD_some, Bool.cond_true, Option.some.injEq]
  congr 1
  funext k
  rcases k with (k | k) | k <;> (try fin_cases k) <;> rfl

private theorem step_move_nil (s : Control)
    (y wa wo c m fuel x sx sa out : List Bool) :
    TM2.step program (cfg (some (.inr .move)) s
      [] y wa wo c m fuel x sx sa out) =
    some (cfg (some (.inr .zero)) (s.1, s.2.1, none, none)
      [] y wa wo c m fuel x sx sa out) := by
  dsimp only [TM2.step, TM2.stepAux, program, cfg, foreign,
    acc, SamplerMachineProduct.cfg, SamplerMachineProduct.foreign,
    SamplerMachineAccumulate.stackContents, Sum.elim_inl, Sum.elim_inr]
  simp only [↓reduceIte, List.head?_nil, List.tail_nil, Option.isSome_none,
    Bool.cond_false, Option.some.injEq]
  congr 1
  funext k
  rcases k with (k | k) | k <;> (try fin_cases k) <;> rfl

private theorem step_zero_cons (s : Control) (b : Bool)
    (a y wa wo c m fuel x sx sa out : List Bool) :
    TM2.step program (cfg (some (.inr .zero)) s
      a y (b :: wa) wo c m fuel x sx sa out) =
    some (cfg (some (.inr .zero)) (s.1, s.2.1, some b, none)
      (false :: a) y wa wo c m fuel x sx sa out) := by
  dsimp only [TM2.step, TM2.stepAux, program, cfg, foreign,
    acc, work, SamplerMachineProduct.cfg,
    SamplerMachineProduct.foreign, SamplerMachineAccumulate.stackContents,
    Sum.elim_inl, Sum.elim_inr]
  simp only [show (2 : Fin 4) ≠ 0 by decide, show (2 : Fin 4) ≠ 1 by decide,
    if_neg, ↓reduceIte, List.head?_cons, List.tail_cons, Option.isSome_some,
    Option.getD_some, Bool.cond_true, Option.some.injEq]
  congr 1
  funext k
  rcases k with (k | k) | k <;> (try fin_cases k) <;> rfl

private theorem step_zero_nil (s : Control)
    (a y wo c m fuel x sx sa out : List Bool) :
    TM2.step program (cfg (some (.inr .zero)) s
      a y [] wo c m fuel x sx sa out) =
    some (cfg (some (.inl (.inr (.inr ())))) initial
      a y [] wo c m fuel x sx sa out) := by
  dsimp only [TM2.step, TM2.stepAux, program, cfg, foreign,
    work, SamplerMachineProduct.cfg, SamplerMachineProduct.foreign,
    SamplerMachineAccumulate.stackContents, Sum.elim_inl, Sum.elim_inr]
  simp only [show (2 : Fin 4) ≠ 0 by decide, show (2 : Fin 4) ≠ 1 by decide,
    if_neg, ↓reduceIte, List.head?_nil, List.tail_nil, Option.isSome_none,
    Bool.cond_false, Option.some.injEq]
  congr 1
  funext k
  rcases k with (k | k) | k <;> (try fin_cases k) <;> rfl

theorem move_run (s : Control)
    (a y wa wo c m fuel x sx sa out : List Bool) :
    run (a.length + 1) (cfg (some (.inr .move)) s
      a y wa wo c m fuel x sx sa out) =
    cfg (some (.inr .zero)) (s.1, s.2.1, none, none)
      [] y (List.replicate a.length false ++ wa) wo c
      (a.reverse ++ m) fuel x sx sa out := by
  induction a generalizing s wa m with
  | nil => simpa using step_move_nil s y wa wo c m fuel x sx sa out |> fun h => run_succ h 0
  | cons b a ih =>
      rw [List.length_cons, run_succ (step_move_cons s b a y wa wo c m fuel x sx sa out)]
      simpa only [List.length_cons, List.replicate_succ', List.reverse_cons,
        List.append_assoc, List.singleton_append] using
          ih (s.1, s.2.1, some b, none) (false :: wa) (b :: m)

theorem zero_run (s : Control)
    (a y wa wo c m fuel x sx sa out : List Bool) :
    run (wa.length + 1) (cfg (some (.inr .zero)) s
      a y wa wo c m fuel x sx sa out) =
    cfg (some (.inl (.inr (.inr ())))) initial
      (List.replicate wa.length false ++ a) y [] wo c m fuel x sx sa out := by
  induction wa generalizing s a with
  | nil => simpa using run_succ (step_zero_nil s a y wo c m fuel x sx sa out) 0
  | cons b wa ih =>
      rw [List.length_cons, run_succ (step_zero_cons s b a y wa wo c m fuel x sx sa out)]
      simpa only [List.length_cons, List.replicate_succ', List.append_assoc,
        List.singleton_append] using
          ih (s.1, s.2.1, some b, none) (false :: a)

theorem prepare_run (s : Control)
    (a y c fuel x out : List Bool) :
    run (2 * a.length + 2) (cfg (some (.inr .move)) s
      a y [] [] c [] fuel x [] [] out) =
    cfg (some (.inl (.inr (.inr ())))) initial
      (List.replicate a.length false) y [] [] c a.reverse fuel x [] [] out := by
  have hm := move_run s a y [] [] c [] fuel x [] [] out
  simp only [List.append_nil] at hm
  have hz := zero_run (s.1, s.2.1, none, none) [] y
    (List.replicate a.length false) [] c a.reverse fuel x [] [] out
  simp only [List.length_replicate, List.append_nil] at hz
  have ht : 2 * a.length + 2 = (a.length + 1) + (a.length + 1) := by omega
  rw [ht, run_add, hm, hz]

theorem product_call (d tail : ℕ) (htail : tail < 2 ^ d)
    (hd : 0 < d) (y a : Fin (2 ^ d))
    (fuel x out : List Bool) :
    let modulus := CurrentAdditive.FiniteFieldConstructor.TrialSearch.monicBits d tail
    let c := lowerWord d modulus
    ∃ t ≤ d * (4 * d + 5) + 1,
      run t (cfg (some (.inl (.inr (.inr ())))) initial
        (encodeWord (fun _ : Fin d => (0 : ZMod 2)))
        (encodeWord (xBits d y)) [] [] (encodeWord c)
        (encodeWord (xBits d a)).reverse fuel x [] [] out) =
      cfg (some (.inr .check)) initial
        (encodeWord (lowerWord d (mul d modulus y.val a.val)))
        (encodeWord (xBits d y)) [] [] (encodeWord c) [] fuel x [] [] out := by
  intro modulus c
  obtain ⟨t, ht, hr⟩ := run_bitPrinter_mul d tail htail hd y a
  have hh : (SamplerMachineProduct.run t
      (SamplerMachineProduct.cfg (some (.inr (.inr ()))) SamplerMachineProduct.initial
        (encodeWord (fun _ : Fin d => (0 : ZMod 2)))
        (encodeWord (xBits d y)) [] [] (encodeWord c)
        (encodeWord (xBits d a)).reverse)).l = none := by
    rw [hr]; rfl
  obtain ⟨t', ht', hrun⟩ := BitMachineSubroutine.lift_outputs
    SamplerMachineProduct.program program (some .check) (fun _ => rfl)
    (false, none, none) (foreign fuel x [] [] out)
    (SamplerMachineProduct.cfg (some (.inr (.inr ()))) SamplerMachineProduct.initial
      (encodeWord (fun _ : Fin d => (0 : ZMod 2)))
      (encodeWord (xBits d y)) [] [] (encodeWord c)
      (encodeWord (xBits d a)).reverse) t hh
  change ∃ t' ≤ _, run t' _ = _
  refine ⟨t', ht'.trans ht, ?_⟩
  change ((advance program)^[t']) _ = _
  change ((advance program)^[t']) _ =
    liftCfg (some .check) (false, none, none) (foreign fuel x [] [] out)
      (SamplerMachineProduct.run t _) at hrun
  rw [hr] at hrun
  exact hrun

theorem encodeWord_xBits (d : ℕ) (a : Fin (2 ^ d)) :
    encodeWord (xBits d a) = DotMachine.natBits d a.val := by
  have hb (b : Bool) :
      decide ((if b then (1 : ZMod 2) else 0) = 1) = b := by
    cases b <;> decide
  apply List.ext_getElem
  · simp [DotMachine.natBits]
  · intro i hi hj
    simp only [encodeWord, List.getElem_ofFn] at hi ⊢
    simp only [DotMachine.natBits, List.getElem_map, List.getElem_range]
    simp only [xBits, boolCoeff, encodeBit]
    exact hb (a.val.testBit i)

theorem encodeWord_zero (d : ℕ) :
    encodeWord (fun _ : Fin d => (0 : ZMod 2)) = List.replicate d false := by
  simp [encodeWord, encodeBit]

private theorem run_check_cons (s : Control) (b : Bool)
    (a y wa wo c m fuel x sx sa out : List Bool) :
    run 1 (cfg (some (.inr .check)) s
      a y wa wo c m (b :: fuel) x sx sa out) =
    cfg (some (.inr .dotScan)) (s.1, false, some b, none)
      a y wa wo c m fuel x sx sa out := by
  simpa using run_succ (step_check_cons s b a y wa wo c m fuel x sx sa out) 0

/-- One streaming bit from the present power, followed by one physical
polynomial-basis multiplication by the seed's fixed base. -/
theorem round_run (d tail : ℕ) (htail : tail < 2 ^ d)
    (hd : 0 < d) (x y a : Fin (2 ^ d)) (b : Bool)
    (fuel out : List Bool) :
    let modulus := CurrentAdditive.FiniteFieldConstructor.TrialSearch.monicBits d tail
    let c := lowerWord d modulus
    ∃ t ≤ d * (4 * d + 5) + 4 * d + 6,
      run t (cfg (some (.inr .check)) initial
        (encodeWord (xBits d a)) (encodeWord (xBits d y)) [] []
        (encodeWord c) [] (b :: fuel) (encodeWord (xBits d x)) [] [] out) =
      cfg (some (.inr .check)) initial
        (encodeWord (lowerWord d (mul d modulus y.val a.val)))
        (encodeWord (xBits d y)) [] [] (encodeWord c) [] fuel
        (encodeWord (xBits d x)) [] [] (dot d x.val a.val :: out) := by
  intro modulus c
  obtain ⟨tp, htp, hp⟩ := product_call d tail htail hd y a fuel
    (encodeWord (xBits d x)) (dot d x.val a.val :: out)
  refine ⟨tp + (4 * d + 5), by omega, ?_⟩
  have hscan := dotScan_run
    (SamplerMachineProduct.initial, false, some b, none)
    (encodeWord (xBits d a)) (encodeWord (xBits d y)) [] []
    (encodeWord c) [] fuel (encodeWord (xBits d x)) [] [] out
    (by simp)
  have hdot : DotMachine.dotAux false
      (encodeWord (xBits d x)) (encodeWord (xBits d a)) =
      dot d x.val a.val := by
    rw [encodeWord_xBits, encodeWord_xBits]
    exact DotMachine.dotAux_natBits false (List.range d) x.val a.val
  simp only [encodeWord_length] at hscan
  rw [hdot] at hscan
  have hrestore := dotRestore_run
    (SamplerMachineProduct.initial, dot d x.val a.val, none, none)
    [] (encodeWord (xBits d y)) [] [] (encodeWord c) [] fuel []
    (encodeWord (xBits d x)).reverse
    (encodeWord (xBits d a)).reverse out (by simp)
  simp only [List.length_reverse, encodeWord_length, List.reverse_reverse,
    List.append_nil, List.nil_append] at hrestore
  have hprep := prepare_run initial (encodeWord (xBits d a))
    (encodeWord (xBits d y)) (encodeWord c) fuel
    (encodeWord (xBits d x)) (dot d x.val a.val :: out)
  simp only [encodeWord_length, ← encodeWord_zero] at hprep
  have htime : tp + (4 * d + 5) =
      1 + ((d + 1) + ((d + 1) + ((2 * d + 2) + tp))) := by omega
  rw [htime]
  rw [run_add 1, run_add (d + 1), run_add (d + 1), run_add (2 * d + 2)]
  simp only [List.append_nil] at hscan
  simp only [initial] at *
  rw [run_check_cons, hscan, hrestore, hprep, hp]

end CurrentAdditive.FiniteFieldMachine.StreamingBitMachine
