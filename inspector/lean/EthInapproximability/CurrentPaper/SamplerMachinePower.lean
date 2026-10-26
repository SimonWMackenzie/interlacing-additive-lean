import EthInapproximability.CurrentPaper.SamplerMachineProduct

/-!
# Repeated field multiplication on Boolean stacks

Source: locked v8 `E-exact-details.tex`, polynomial-basis powers in the
proof of `lem:exact-families`. A unary fuel stack controls repeated
multiplication. The controller explicitly reverses the current product,
writes its zero accumulator, invokes the finite multiplication program,
and repeats. All data stay on Boolean stacks; no exponent-valued control
register or unit-cost arithmetic instruction is used.
-/

namespace EthInapproximability.CurrentPaper.SamplerMachinePower

open Turing Turing.TM2.Stmt BitMachineEncoding BitMachineComposition
open ExecutableSmallBiasSampler SamplerMachine

inductive Admin where
  | loop | move | zero
  deriving DecidableEq, Fintype

abbrev Stack := SamplerMachineProduct.Stack ⊕ Unit
abbrev Label := SamplerMachineProduct.Label ⊕ Admin
abbrev Control := SamplerMachineProduct.Control × Option Bool
abbrev Config := TM2.Cfg (fun _ : Stack => Bool) Label Control

def initial : Control := (SamplerMachineProduct.initial, none)

def program : Label → TM2.Stmt (fun _ : Stack => Bool) Label Control
  | .inl l => liftStmt (some .loop) (SamplerMachineProduct.program l)
  | .inr .loop => pop (.inr ()) (fun s b => (s.1, b))
      (branch (fun s => s.2.isSome)
        (load (fun _ => initial) (goto (fun _ => .inr .move)))
        (load (fun _ => initial) halt))
  | .inr .move => pop (.inl (.inl 0)) (fun s b => (s.1, b))
      (branch (fun s => s.2.isSome)
        (push (.inl (.inr 1)) (fun s => s.2.getD false)
          (push (.inl (.inl 2)) (fun _ => false) (goto (fun _ => .inr .move))))
        (goto (fun _ => .inr .zero)))
  | .inr .zero => pop (.inl (.inl 2)) (fun s b => (s.1, b))
      (branch (fun s => s.2.isSome)
        (push (.inl (.inl 0)) (fun _ => false) (goto (fun _ => .inr .zero)))
        (load (fun _ => initial) (goto (fun _ => .inl (.inr (.inr ()))))))

def cfg (l : Option Label) (s : Control)
    (a u work other c multiplier fuel : List Bool) : Config :=
  ⟨l, s, Sum.elim
    (SamplerMachineProduct.cfg none s.1 a u work other c multiplier).stk
    (fun _ => fuel)⟩

def run (t : ℕ) (q : Config) := ((advance program)^[t]) q

private theorem run_succ {c d : Config} (h : TM2.step program c = some d) (n : ℕ) :
    run (n + 1) c = run n d := by
  simp only [run, Function.iterate_succ_apply, advance, h, Option.getD_some]

private theorem step_move_cons (s : Control) (b : Bool)
    (a u work other c multiplier fuel : List Bool) :
    TM2.step program (cfg (some (.inr .move)) s (b :: a) u work other c multiplier fuel) =
      some (cfg (some (.inr .move)) (s.1, some b) a u (false :: work) other c
        (b :: multiplier) fuel) := by
  dsimp only [TM2.step, TM2.stepAux, program, cfg, SamplerMachineProduct.cfg,
    SamplerMachineAccumulate.stackContents, SamplerMachineProduct.foreign,
    Sum.elim_inl, Sum.elim_inr]
  simp only [↓reduceIte, List.head?_cons, List.tail_cons, Option.isSome_some,
    Option.getD_some, Bool.cond_true, Option.some.injEq]
  congr 1
  funext k
  rcases k with (k | k) | k <;> (try fin_cases k) <;> rfl

private theorem step_move_nil (s : Control)
    (u work other c multiplier fuel : List Bool) :
    TM2.step program (cfg (some (.inr .move)) s [] u work other c multiplier fuel) =
      some (cfg (some (.inr .zero)) (s.1, none) [] u work other c multiplier fuel) := by
  dsimp only [TM2.step, TM2.stepAux, program, cfg, SamplerMachineProduct.cfg,
    SamplerMachineAccumulate.stackContents, SamplerMachineProduct.foreign,
    Sum.elim_inl, Sum.elim_inr]
  simp only [↓reduceIte, List.head?_nil, List.tail_nil, Option.isSome_none,
    Bool.cond_false, Option.some.injEq]
  congr 1
  funext k
  rcases k with (k | k) | k <;> (try fin_cases k) <;> rfl

private theorem step_zero_cons (s : Control) (b : Bool)
    (a u work other c multiplier fuel : List Bool) :
    TM2.step program (cfg (some (.inr .zero)) s a u (b :: work) other c multiplier fuel) =
      some (cfg (some (.inr .zero)) (s.1, some b) (false :: a) u work other c
        multiplier fuel) := by
  dsimp only [TM2.step, TM2.stepAux, program, cfg, SamplerMachineProduct.cfg,
    SamplerMachineAccumulate.stackContents, SamplerMachineProduct.foreign,
    Sum.elim_inl, Sum.elim_inr]
  simp only [show (2 : Fin 4) ≠ 0 by decide, show (2 : Fin 4) ≠ 1 by decide,
    ↓reduceIte, List.head?_cons, List.tail_cons, Option.isSome_some,
    Option.getD_some, Bool.cond_true, Option.some.injEq]
  congr 1
  funext k
  rcases k with (k | k) | k <;> (try fin_cases k) <;> rfl

private theorem step_zero_nil (s : Control)
    (a u other c multiplier fuel : List Bool) :
    TM2.step program (cfg (some (.inr .zero)) s a u [] other c multiplier fuel) =
      some (cfg (some (.inl (.inr (.inr ())))) initial a u [] other c multiplier fuel) := by
  dsimp only [TM2.step, TM2.stepAux, program, cfg, SamplerMachineProduct.cfg,
    SamplerMachineAccumulate.stackContents, SamplerMachineProduct.foreign,
    Sum.elim_inl, Sum.elim_inr]
  simp only [show (2 : Fin 4) ≠ 0 by decide, show (2 : Fin 4) ≠ 1 by decide,
    ↓reduceIte, List.head?_nil, List.tail_nil, Option.isSome_none,
    Bool.cond_false, Option.some.injEq]
  congr 1
  funext k
  rcases k with (k | k) | k <;> (try fin_cases k) <;> rfl

theorem move_run (s : Control) (a u work other c multiplier fuel : List Bool) :
    run (a.length + 1) (cfg (some (.inr .move)) s a u work other c multiplier fuel) =
      cfg (some (.inr .zero)) (s.1, none) [] u
        (List.replicate a.length false ++ work) other c (a.reverse ++ multiplier) fuel := by
  induction a generalizing s work multiplier with
  | nil => simpa using run_succ (step_move_nil s u work other c multiplier fuel) 0
  | cons b a ih =>
      rw [List.length_cons, run_succ (step_move_cons s b a u work other c multiplier fuel)]
      simpa only [List.length_cons, List.replicate_succ', List.reverse_cons,
        List.append_assoc, List.singleton_append] using
          ih (s.1, some b) (false :: work) (b :: multiplier)

theorem zero_run (s : Control) (a u work other c multiplier fuel : List Bool) :
    run (work.length + 1) (cfg (some (.inr .zero)) s a u work other c multiplier fuel) =
      cfg (some (.inl (.inr (.inr ())))) initial
        (List.replicate work.length false ++ a) u [] other c multiplier fuel := by
  induction work generalizing s a with
  | nil => simpa using run_succ (step_zero_nil s a u other c multiplier fuel) 0
  | cons b work ih =>
      rw [List.length_cons, run_succ (step_zero_cons s b a u work other c multiplier fuel)]
      simpa only [List.length_cons, List.replicate_succ', List.append_assoc,
        List.singleton_append] using
        ih (s.1, some b) (false :: a)

theorem prepare_run (s : Control) (a u c fuel : List Bool) :
    run (2 * a.length + 2) (cfg (some (.inr .move)) s a u [] [] c [] fuel) =
      cfg (some (.inl (.inr (.inr ())))) initial
        (List.replicate a.length false) u [] [] c a.reverse fuel := by
  have hm := move_run s a u [] [] c [] fuel
  simp only [List.append_nil] at hm
  have hz := zero_run (s.1, none) [] u (List.replicate a.length false) [] c a.reverse fuel
  simp only [List.length_replicate, List.append_nil] at hz
  have ht : 2 * a.length + 2 = (a.length + 1) + (a.length + 1) := by omega
  rw [ht]
  simp only [run, Function.iterate_add_apply] at hm hz ⊢
  rw [hm, hz]

theorem product_call {n : ℕ} (u a : BinaryWord n) (fuel : List Bool) :
    ∃ t ≤ n * (4 * n + 5) + 1,
      run t (cfg (some (.inl (.inr (.inr ())))) initial
        (encodeWord (fun _ : Fin n => (0 : ZMod 2))) (encodeWord u) [] []
        (encodeWord (chosenWord n)) (encodeWord a).reverse fuel) =
      cfg (some (.inr .loop)) initial (encodeWord (wordMul n u a)) (encodeWord u)
        [] [] (encodeWord (chosenWord n)) [] fuel := by
  obtain ⟨t, ht, hr⟩ := SamplerMachineProduct.run_wordMul u a
  have hh : (SamplerMachineProduct.run t
      (SamplerMachineProduct.cfg (some (.inr (.inr ()))) SamplerMachineProduct.initial
        (encodeWord (fun _ : Fin n => (0 : ZMod 2))) (encodeWord u) [] []
        (encodeWord (chosenWord n)) (encodeWord a).reverse)).l = none := by rw [hr]; rfl
  obtain ⟨t', ht', hrun⟩ := BitMachineSubroutine.lift_outputs
    SamplerMachineProduct.program program (some .loop) (fun _ => rfl)
    (none : Option Bool) (fun _ : Unit => fuel)
    (SamplerMachineProduct.cfg (some (.inr (.inr ()))) SamplerMachineProduct.initial
      (encodeWord (fun _ : Fin n => (0 : ZMod 2))) (encodeWord u) [] []
      (encodeWord (chosenWord n)) (encodeWord a).reverse) t hh
  change ∃ t' ≤ _, run t' _ = _
  refine ⟨t', ht'.trans ht, ?_⟩
  change ((advance program)^[t']) _ = _
  change ((advance program)^[t']) _ =
    liftCfg (some .loop) none (fun _ : Unit => fuel)
      (SamplerMachineProduct.run t _) at hrun
  rw [hr] at hrun
  exact hrun

private theorem step_loop_cons (s : Control) (b : Bool)
    (a u c fuel : List Bool) :
    TM2.step program (cfg (some (.inr .loop)) s a u [] [] c [] (b :: fuel)) =
      some (cfg (some (.inr .move)) initial a u [] [] c [] fuel) := by
  dsimp only [TM2.step, TM2.stepAux, program, cfg, initial, Sum.elim_inr]
  simp only [List.head?_cons, List.tail_cons, Option.isSome_some,
    Bool.cond_true, Option.some.injEq]
  congr 1
  funext k
  rcases k with k | k <;> rfl

private theorem step_loop_nil (s : Control) (a u c : List Bool) :
    TM2.step program (cfg (some (.inr .loop)) s a u [] [] c [] []) =
      some (cfg none initial a u [] [] c [] []) := by
  dsimp only [TM2.step, TM2.stepAux, program, cfg, initial, Sum.elim_inr]
  simp only [List.head?_nil, List.tail_nil, Option.isSome_none,
    Bool.cond_false, Option.some.injEq]
  congr 1
  funext k
  rcases k with k | k <;> rfl

theorem encodeWord_zero (n : ℕ) :
    encodeWord (fun _ : Fin n => (0 : ZMod 2)) = List.replicate n false := by
  simp [encodeWord, encodeBit]

/-- One literal round, including the fuel test and product preparation. -/
theorem round_run {n : ℕ} (s : Control) (u a : BinaryWord n) (b : Bool) (fuel : List Bool) :
    ∃ t ≤ n * (4 * n + 5) + 2 * n + 4,
      run t (cfg (some (.inr .loop)) s (encodeWord a) (encodeWord u) [] []
        (encodeWord (chosenWord n)) [] (b :: fuel)) =
      cfg (some (.inr .loop)) initial (encodeWord (wordMul n u a)) (encodeWord u)
        [] [] (encodeWord (chosenWord n)) [] fuel := by
  obtain ⟨t, ht, hr⟩ := product_call u a fuel
  refine ⟨t + (2 * n + 2) + 1, by omega, ?_⟩
  rw [run_succ (step_loop_cons s b (encodeWord a) (encodeWord u)
    (encodeWord (chosenWord n)) fuel)]
  simp only [run, Function.iterate_add_apply]
  have hp := prepare_run initial (encodeWord a) (encodeWord u)
    (encodeWord (chosenWord n)) fuel
  simp only [encodeWord_length, ← encodeWord_zero] at hp
  change run t (run (2 * n + 2) _) = _
  rw [hp, hr]

/-- The same fixed finite program executes any number of field products.
The unary fuel is consumed; modulus and multiplicand are unchanged, and
all three work stacks are cleared. The bound includes the final halt test. -/
theorem run_multiply_iterate {n : ℕ} (s : Control) (u a : BinaryWord n)
    (fuel : List Bool) :
    ∃ t ≤ fuel.length * (n * (4 * n + 5) + 2 * n + 4) + 1,
      run t (cfg (some (.inr .loop)) s (encodeWord a) (encodeWord u) [] []
        (encodeWord (chosenWord n)) [] fuel) =
      cfg none initial (encodeWord (((wordMul n u)^[fuel.length]) a)) (encodeWord u)
        [] [] (encodeWord (chosenWord n)) [] [] := by
  induction fuel generalizing s a with
  | nil =>
      refine ⟨1, by simp, ?_⟩
      exact run_succ (step_loop_nil s (encodeWord a) (encodeWord u)
        (encodeWord (chosenWord n))) 0
  | cons b fuel ih =>
      obtain ⟨ts, hts, hs⟩ := round_run s u a b fuel
      obtain ⟨tr, htr, hr⟩ := ih initial (wordMul n u a)
      refine ⟨tr + ts, ?_, ?_⟩
      · simp only [List.length_cons]
        nlinarith
      · simp only [run, Function.iterate_add_apply]
        change run tr (run ts _) = _
        rw [hs, hr]
        simp only [List.length_cons, Function.iterate_succ_apply]

theorem wordMul_comm (n : ℕ) (u v : BinaryWord n) : wordMul n u v = wordMul n v u := by
  apply (wordEval_bijective n).injective
  simp only [wordEval_mul, mul_comm]

theorem iterate_eq_wordPow (n : ℕ) (u : BinaryWord n) (k : ℕ) :
    ((wordMul n u)^[k]) (constantWord n 1) = wordPow n u k := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [Function.iterate_succ_apply', ih, wordPow, wordMul_comm]

/-- Actual finite-control execution of the exact executable `wordPow`.
This raw-bank interface requires the constant-one word, base, selected
modulus, and unary exponent to be supplied; their preparation is not free. -/
theorem run_wordPow (n : ℕ) (u : BinaryWord n) (k : ℕ) :
    ∃ t ≤ k * (n * (4 * n + 5) + 2 * n + 4) + 1,
      run t (cfg (some (.inr .loop)) initial
        (encodeWord (constantWord n 1)) (encodeWord u) [] []
        (encodeWord (chosenWord n)) [] (List.replicate k true)) =
      cfg none initial (encodeWord (wordPow n u k)) (encodeWord u)
        [] [] (encodeWord (chosenWord n)) [] [] := by
  simpa only [List.length_replicate, iterate_eq_wordPow] using
    run_multiply_iterate initial u (constantWord n 1) (List.replicate k true)

end EthInapproximability.CurrentPaper.SamplerMachinePower
