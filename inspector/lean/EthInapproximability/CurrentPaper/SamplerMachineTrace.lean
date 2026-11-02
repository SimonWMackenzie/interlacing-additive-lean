import EthInapproximability.CurrentPaper.SamplerMachinePower

/-!
# A finite-stack controller for the binary field trace

Source: locked v8 `E-exact-details.tex`, the traces of field pairs in
`lem:exact-families`. Each round adds the current Frobenius power to the
sum, then squares it using the literal coefficient multiplication program.
The machine has eight Boolean stacks and finite control. Its raw interface
receives the selected modulus, the initial word, a zero sum, and unary fuel.
-/

namespace EthInapproximability.CurrentPaper.SamplerMachineTrace

open Turing Turing.TM2.Stmt BitMachineEncoding BitMachineComposition
open ExecutableSmallBiasSampler SamplerMachine

inductive Admin where
  | loop | sumScan | sumRestore | move | zero | clear
  deriving DecidableEq, Fintype

abbrev Stack := SamplerMachineProduct.Stack ⊕ Fin 2
abbrev Label := SamplerMachineProduct.Label ⊕ Admin
abbrev Control := SamplerMachineProduct.Control × (Option Bool × Option Bool)
abbrev Config := TM2.Cfg (fun _ : Stack => Bool) Label Control

def initial : Control := (SamplerMachineProduct.initial, none, none)

def program : Label → TM2.Stmt (fun _ : Stack => Bool) Label Control
  | .inl l => liftStmt (some .clear) (SamplerMachineProduct.program l)
  | .inr .loop => pop (.inr 1) (fun s b => (s.1, b, none))
      (branch (fun s => s.2.1.isSome)
        (load (fun _ => initial) (goto (fun _ => .inr .sumScan)))
        (load (fun _ => initial) halt))
  | .inr .sumScan => pop (.inr 0) (fun s b => (s.1, b, none))
      (pop (.inl (.inl 0)) (fun s b => (s.1, s.2.1, b))
        (branch (fun s => s.2.1.isSome)
          (push (.inl (.inl 2)) (fun s => Bool.xor (s.2.1.getD false) (s.2.2.getD false))
            (push (.inl (.inl 3)) (fun s => s.2.2.getD false)
              (goto (fun _ => .inr .sumScan))))
          (goto (fun _ => .inr .sumRestore))))
  | .inr .sumRestore => pop (.inl (.inl 2)) (fun s b => (s.1, b, none))
      (pop (.inl (.inl 3)) (fun s b => (s.1, s.2.1, b))
        (branch (fun s => s.2.1.isSome)
          (push (.inr 0) (fun s => s.2.1.getD false)
            (push (.inl (.inl 0)) (fun s => s.2.2.getD false)
              (goto (fun _ => .inr .sumRestore))))
          (load (fun _ => initial) (goto (fun _ => .inr .move)))))
  | .inr .move => pop (.inl (.inl 0)) (fun s b => (s.1, b, none))
      (branch (fun s => s.2.1.isSome)
        (push (.inl (.inr 1)) (fun s => s.2.1.getD false)
          (push (.inl (.inl 2)) (fun _ => false)
            (push (.inl (.inl 3)) (fun s => s.2.1.getD false)
              (goto (fun _ => .inr .move)))))
        (goto (fun _ => .inr .zero)))
  | .inr .zero => pop (.inl (.inl 2)) (fun s b => (s.1, b, none))
      (pop (.inl (.inl 3)) (fun s b => (s.1, s.2.1, b))
        (branch (fun s => s.2.1.isSome)
          (push (.inl (.inl 0)) (fun _ => false)
            (push (.inl (.inl 1)) (fun s => s.2.2.getD false)
              (goto (fun _ => .inr .zero))))
          (load (fun _ => initial) (goto (fun _ => .inl (.inr (.inr ())))))))
  | .inr .clear => pop (.inl (.inl 1)) (fun s b => (s.1, b, none))
      (branch (fun s => s.2.1.isSome)
        (goto (fun _ => .inr .clear))
        (load (fun _ => initial) (goto (fun _ => .inr .loop))))

def cfg (l : Option Label) (s : Control)
    (a u work other c multiplier sum fuel : List Bool) : Config :=
  ⟨l, s, Sum.elim
    (SamplerMachineProduct.cfg none s.1 a u work other c multiplier).stk
    (fun i => if i = 0 then sum else fuel)⟩

def run (t : ℕ) (q : Config) := ((advance program)^[t]) q

private theorem run_succ {c d : Config} (h : TM2.step program c = some d) (n : ℕ) :
    run (n + 1) c = run n d := by
  simp only [run, Function.iterate_succ_apply, advance, h, Option.getD_some]

private theorem step_sumScan_cons (s : Control) (x y : Bool)
    (a u work other c multiplier sum fuel : List Bool) :
    TM2.step program (cfg (some (.inr .sumScan)) s (y :: a) u work other c multiplier
      (x :: sum) fuel) =
      some (cfg (some (.inr .sumScan)) (s.1, some x, some y) a u
        (Bool.xor x y :: work) (y :: other) c multiplier sum fuel) := by
  dsimp only [TM2.step, TM2.stepAux, program, cfg, SamplerMachineProduct.cfg,
    SamplerMachineAccumulate.stackContents, SamplerMachineProduct.foreign,
    Sum.elim_inl, Sum.elim_inr]
  simp only [↓reduceIte, List.head?_cons, List.tail_cons, Option.isSome_some,
    Option.getD_some, Bool.cond_true, Option.some.injEq, Function.update_apply,
    Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq]
  congr 1
  funext k
  rcases k with (k | k) | k <;> fin_cases k <;> rfl

private theorem step_sumScan_nil (s : Control)
    (u work other c multiplier fuel : List Bool) :
    TM2.step program (cfg (some (.inr .sumScan)) s [] u work other c multiplier [] fuel) =
      some (cfg (some (.inr .sumRestore)) (s.1, none, none)
        [] u work other c multiplier [] fuel) := by
  dsimp only [TM2.step, TM2.stepAux, program, cfg, SamplerMachineProduct.cfg,
    SamplerMachineAccumulate.stackContents, SamplerMachineProduct.foreign,
    Sum.elim_inl, Sum.elim_inr]
  simp only [↓reduceIte, List.head?_nil, List.tail_nil, Option.isSome_none,
    Bool.cond_false, Option.some.injEq, Function.update_apply,
    Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq]
  congr 1
  funext k
  rcases k with (k | k) | k <;> fin_cases k <;> rfl

private theorem step_sumRestore_cons (s : Control) (x y : Bool)
    (a u work other c multiplier sum fuel : List Bool) :
    TM2.step program (cfg (some (.inr .sumRestore)) s a u (x :: work) (y :: other)
      c multiplier sum fuel) =
      some (cfg (some (.inr .sumRestore)) (s.1, some x, some y) (y :: a) u
        work other c multiplier (x :: sum) fuel) := by
  dsimp only [TM2.step, TM2.stepAux, program, cfg, SamplerMachineProduct.cfg,
    SamplerMachineAccumulate.stackContents, SamplerMachineProduct.foreign,
    Sum.elim_inl, Sum.elim_inr]
  simp only [show (2 : Fin 4) ≠ 0 by decide, show (2 : Fin 4) ≠ 1 by decide,
    show (3 : Fin 4) ≠ 0 by decide, show (3 : Fin 4) ≠ 1 by decide,
    show (3 : Fin 4) ≠ 2 by decide, ↓reduceIte,
    List.head?_cons, List.tail_cons, Option.isSome_some, Option.getD_some,
    Bool.cond_true, Option.some.injEq, Function.update_apply,
    Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq]
  congr 1
  funext k
  rcases k with (k | k) | k <;> fin_cases k <;> rfl

private theorem step_sumRestore_nil (s : Control) (a u c multiplier sum fuel : List Bool) :
    TM2.step program (cfg (some (.inr .sumRestore)) s a u [] [] c multiplier sum fuel) =
      some (cfg (some (.inr .move)) initial a u [] [] c multiplier sum fuel) := by
  dsimp only [TM2.step, TM2.stepAux, program, cfg, SamplerMachineProduct.cfg,
    SamplerMachineAccumulate.stackContents, SamplerMachineProduct.foreign,
    Sum.elim_inl, Sum.elim_inr]
  simp only [show (2 : Fin 4) ≠ 0 by decide, show (2 : Fin 4) ≠ 1 by decide,
    show (3 : Fin 4) ≠ 0 by decide, show (3 : Fin 4) ≠ 1 by decide,
    show (3 : Fin 4) ≠ 2 by decide, ↓reduceIte,
    List.head?_nil, List.tail_nil, Option.isSome_none, Bool.cond_false,
    Option.some.injEq, Function.update_apply, Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq]
  congr 1
  funext k
  rcases k with (k | k) | k <;> fin_cases k <;> rfl

theorem sumScan_run (s : Control) (a u work other c multiplier sum fuel : List Bool)
    (h : sum.length = a.length) :
    run (sum.length + 1)
      (cfg (some (.inr .sumScan)) s a u work other c multiplier sum fuel) =
      cfg (some (.inr .sumRestore)) (s.1, none, none) [] u
        ((sum.zipWith Bool.xor a).reverse ++ work) (a.reverse ++ other) c multiplier [] fuel := by
  induction sum generalizing s a work other with
  | nil =>
      have ha : a = [] := List.length_eq_zero_iff.mp h.symm
      subst a
      simpa using run_succ (step_sumScan_nil s u work other c multiplier fuel) 0
  | cons x sum ih =>
      cases a with
      | nil => simp at h
      | cons y a =>
          rw [List.length_cons, run_succ
            (step_sumScan_cons s x y a u work other c multiplier sum fuel)]
          simpa only [List.zipWith_cons_cons, List.reverse_cons, List.append_assoc,
            List.singleton_append] using
            ih (s.1, some x, some y) a (Bool.xor x y :: work) (y :: other)
              (by simpa using h)

theorem sumRestore_run (s : Control) (a u work other c multiplier sum fuel : List Bool)
    (h : work.length = other.length) :
    run (work.length + 1)
      (cfg (some (.inr .sumRestore)) s a u work other c multiplier sum fuel) =
      cfg (some (.inr .move)) initial (other.reverse ++ a) u [] [] c multiplier
        (work.reverse ++ sum) fuel := by
  induction work generalizing s a other sum with
  | nil =>
      have ho : other = [] := List.length_eq_zero_iff.mp h.symm
      subst other
      simpa using run_succ (step_sumRestore_nil s a u c multiplier sum fuel) 0
  | cons x work ih =>
      cases other with
      | nil => simp at h
      | cons y other =>
          rw [List.length_cons, run_succ
            (step_sumRestore_cons s x y a u work other c multiplier sum fuel)]
          simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using
            ih (s.1, some x, some y) (y :: a) other (x :: sum) (by simpa using h)

theorem sum_run (s : Control) (a u c multiplier sum fuel : List Bool)
    (h : sum.length = a.length) :
    run (2 * a.length + 2)
      (cfg (some (.inr .sumScan)) s a u [] [] c multiplier sum fuel) =
      cfg (some (.inr .move)) initial a u [] [] c multiplier (sum.zipWith Bool.xor a) fuel := by
  have hs := sumScan_run s a u [] [] c multiplier sum fuel h
  have hl : (sum.zipWith Bool.xor a).length = a.length := by simp [h]
  simp only [List.append_nil, h] at hs
  have hr := sumRestore_run (s.1, none, none) [] u (sum.zipWith Bool.xor a).reverse
    a.reverse c multiplier [] fuel (by simpa only [List.length_reverse, hl])
  simp only [List.length_reverse, hl, List.reverse_reverse, List.append_nil] at hr
  have ht : 2 * a.length + 2 = (a.length + 1) + (a.length + 1) := by omega
  rw [ht]
  simp only [run, Function.iterate_add_apply] at hs hr ⊢
  rw [hs, hr]

private theorem step_move_cons (s : Control) (b : Bool)
    (a u work other c multiplier sum fuel : List Bool) :
    TM2.step program (cfg (some (.inr .move)) s (b :: a) u work other c multiplier sum fuel) =
      some (cfg (some (.inr .move)) (s.1, some b, none) a u (false :: work)
        (b :: other) c (b :: multiplier) sum fuel) := by
  dsimp only [TM2.step, TM2.stepAux, program, cfg, SamplerMachineProduct.cfg,
    SamplerMachineAccumulate.stackContents, SamplerMachineProduct.foreign,
    Sum.elim_inl, Sum.elim_inr]
  simp only [↓reduceIte, List.head?_cons, List.tail_cons, Option.isSome_some,
    Option.getD_some, Bool.cond_true, Option.some.injEq, Function.update_apply,
    Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq]
  congr 1
  funext k
  rcases k with (k | k) | k <;> fin_cases k <;> rfl

private theorem step_move_nil (s : Control)
    (u work other c multiplier sum fuel : List Bool) :
    TM2.step program (cfg (some (.inr .move)) s [] u work other c multiplier sum fuel) =
      some (cfg (some (.inr .zero)) (s.1, none, none) [] u work other c multiplier sum fuel) := by
  dsimp only [TM2.step, TM2.stepAux, program, cfg, SamplerMachineProduct.cfg,
    SamplerMachineAccumulate.stackContents, SamplerMachineProduct.foreign,
    Sum.elim_inl, Sum.elim_inr]
  simp only [↓reduceIte, List.head?_nil, List.tail_nil, Option.isSome_none,
    Bool.cond_false, Option.some.injEq]
  congr 1
  funext k
  rcases k with (k | k) | k <;> fin_cases k <;> rfl

private theorem step_zero_cons (s : Control) (x y : Bool)
    (a u work other c multiplier sum fuel : List Bool) :
    TM2.step program (cfg (some (.inr .zero)) s a u (x :: work) (y :: other)
      c multiplier sum fuel) =
      some (cfg (some (.inr .zero)) (s.1, some x, some y) (false :: a) (y :: u)
        work other c multiplier sum fuel) := by
  dsimp only [TM2.step, TM2.stepAux, program, cfg, SamplerMachineProduct.cfg,
    SamplerMachineAccumulate.stackContents, SamplerMachineProduct.foreign,
    Sum.elim_inl, Sum.elim_inr]
  simp only [show (2 : Fin 4) ≠ 0 by decide, show (2 : Fin 4) ≠ 1 by decide,
    show (3 : Fin 4) ≠ 0 by decide, show (3 : Fin 4) ≠ 1 by decide,
    show (3 : Fin 4) ≠ 2 by decide, ↓reduceIte,
    List.head?_cons, List.tail_cons, Option.isSome_some, Option.getD_some,
    Bool.cond_true, Option.some.injEq, Function.update_apply,
    Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq]
  congr 1
  funext k
  rcases k with (k | k) | k <;> fin_cases k <;> rfl

private theorem step_zero_nil (s : Control) (a u c multiplier sum fuel : List Bool) :
    TM2.step program (cfg (some (.inr .zero)) s a u [] [] c multiplier sum fuel) =
      some (cfg (some (.inl (.inr (.inr ())))) initial a u [] [] c multiplier sum fuel) := by
  dsimp only [TM2.step, TM2.stepAux, program, cfg, SamplerMachineProduct.cfg,
    SamplerMachineAccumulate.stackContents, SamplerMachineProduct.foreign,
    Sum.elim_inl, Sum.elim_inr]
  simp only [show (2 : Fin 4) ≠ 0 by decide, show (2 : Fin 4) ≠ 1 by decide,
    show (3 : Fin 4) ≠ 0 by decide, show (3 : Fin 4) ≠ 1 by decide,
    show (3 : Fin 4) ≠ 2 by decide, ↓reduceIte,
    List.head?_nil, List.tail_nil, Option.isSome_none, Bool.cond_false,
    Option.some.injEq, Function.update_apply, Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq]
  congr 1
  funext k
  rcases k with (k | k) | k <;> fin_cases k <;> rfl

theorem move_run (s : Control) (a u work other c multiplier sum fuel : List Bool) :
    run (a.length + 1) (cfg (some (.inr .move)) s a u work other c multiplier sum fuel) =
      cfg (some (.inr .zero)) (s.1, none, none) [] u
        (List.replicate a.length false ++ work) (a.reverse ++ other) c
        (a.reverse ++ multiplier) sum fuel := by
  induction a generalizing s work other multiplier with
  | nil => simpa using run_succ (step_move_nil s u work other c multiplier sum fuel) 0
  | cons b a ih =>
      rw [List.length_cons,
        run_succ (step_move_cons s b a u work other c multiplier sum fuel)]
      simpa only [List.length_cons, List.replicate_succ', List.reverse_cons,
        List.append_assoc, List.singleton_append] using
          ih (s.1, some b, none) (false :: work) (b :: other) (b :: multiplier)

theorem zero_run (s : Control) (a u work other c multiplier sum fuel : List Bool)
    (h : work.length = other.length) :
    run (work.length + 1) (cfg (some (.inr .zero)) s a u work other c multiplier sum fuel) =
      cfg (some (.inl (.inr (.inr ())))) initial
        (List.replicate work.length false ++ a) (other.reverse ++ u) [] [] c multiplier sum fuel := by
  induction work generalizing s a u other with
  | nil =>
      have ho : other = [] := List.length_eq_zero_iff.mp h.symm
      subst other
      simpa using run_succ (step_zero_nil s a u c multiplier sum fuel) 0
  | cons x work ih =>
      cases other with
      | nil => simp at h
      | cons y other =>
          rw [List.length_cons, run_succ
            (step_zero_cons s x y a u work other c multiplier sum fuel)]
          simpa only [List.length_cons, List.replicate_succ', List.reverse_cons,
            List.append_assoc, List.singleton_append] using
            ih (s.1, some x, some y) (false :: a) (y :: u) other (by simpa using h)

theorem prepare_run (s : Control) (a c sum fuel : List Bool) :
    run (2 * a.length + 2) (cfg (some (.inr .move)) s a [] [] [] c [] sum fuel) =
      cfg (some (.inl (.inr (.inr ())))) initial
        (List.replicate a.length false) a [] [] c a.reverse sum fuel := by
  have hm := move_run s a [] [] [] c [] sum fuel
  simp only [List.append_nil] at hm
  have hz := zero_run (s.1, none, none) [] [] (List.replicate a.length false)
    a.reverse c a.reverse sum fuel (by simp)
  simp only [List.length_replicate, List.reverse_reverse, List.append_nil] at hz
  have ht : 2 * a.length + 2 = (a.length + 1) + (a.length + 1) := by omega
  rw [ht]
  simp only [run, Function.iterate_add_apply] at hm hz ⊢
  rw [hm, hz]

private theorem step_clear_cons (s : Control) (b : Bool)
    (a u c sum fuel : List Bool) :
    TM2.step program (cfg (some (.inr .clear)) s a (b :: u) [] [] c [] sum fuel) =
      some (cfg (some (.inr .clear)) (s.1, some b, none) a u [] [] c [] sum fuel) := by
  dsimp only [TM2.step, TM2.stepAux, program, cfg, SamplerMachineProduct.cfg,
    SamplerMachineAccumulate.stackContents, SamplerMachineProduct.foreign,
    Sum.elim_inl, Sum.elim_inr]
  simp only [show (1 : Fin 4) ≠ 0 by decide, ↓reduceIte,
    List.head?_cons, List.tail_cons, Option.isSome_some,
    Bool.cond_true, Option.some.injEq]
  congr 1
  funext k
  rcases k with (k | k) | k <;> fin_cases k <;> rfl

private theorem step_clear_nil (s : Control) (a c sum fuel : List Bool) :
    TM2.step program (cfg (some (.inr .clear)) s a [] [] [] c [] sum fuel) =
      some (cfg (some (.inr .loop)) initial a [] [] [] c [] sum fuel) := by
  dsimp only [TM2.step, TM2.stepAux, program, cfg, SamplerMachineProduct.cfg,
    SamplerMachineAccumulate.stackContents, SamplerMachineProduct.foreign,
    Sum.elim_inl, Sum.elim_inr]
  simp only [show (1 : Fin 4) ≠ 0 by decide, ↓reduceIte,
    List.head?_nil, List.tail_nil, Option.isSome_none,
    Bool.cond_false, Option.some.injEq]
  congr 1
  funext k
  rcases k with (k | k) | k <;> fin_cases k <;> rfl

theorem clear_run (s : Control) (a u c sum fuel : List Bool) :
    run (u.length + 1) (cfg (some (.inr .clear)) s a u [] [] c [] sum fuel) =
      cfg (some (.inr .loop)) initial a [] [] [] c [] sum fuel := by
  induction u generalizing s with
  | nil => exact run_succ (step_clear_nil s a c sum fuel) 0
  | cons b u ih =>
      rw [List.length_cons, run_succ (step_clear_cons s b a u c sum fuel)]
      exact ih (s.1, some b, none)

theorem square_call {n : ℕ} (a : BinaryWord n) (sum fuel : List Bool) :
    ∃ t ≤ n * (4 * n + 5) + n + 2,
      run t (cfg (some (.inl (.inr (.inr ())))) initial
        (encodeWord (fun _ : Fin n => (0 : ZMod 2))) (encodeWord a) [] []
        (encodeWord (chosenWord n)) (encodeWord a).reverse sum fuel) =
      cfg (some (.inr .loop)) initial (encodeWord (wordMul n a a)) [] [] []
        (encodeWord (chosenWord n)) [] sum fuel := by
  obtain ⟨t, ht, hr⟩ := SamplerMachineProduct.run_wordMul a a
  have hh : (SamplerMachineProduct.run t
      (SamplerMachineProduct.cfg (some (.inr (.inr ()))) SamplerMachineProduct.initial
        (encodeWord (fun _ : Fin n => (0 : ZMod 2))) (encodeWord a) [] []
        (encodeWord (chosenWord n)) (encodeWord a).reverse)).l = none := by rw [hr]; rfl
  obtain ⟨t', ht', hrun⟩ := BitMachineSubroutine.lift_outputs
    SamplerMachineProduct.program program (some .clear) (fun _ => rfl)
    ((none, none) : Option Bool × Option Bool)
    (fun i : Fin 2 => if i = 0 then sum else fuel)
    (SamplerMachineProduct.cfg (some (.inr (.inr ()))) SamplerMachineProduct.initial
      (encodeWord (fun _ : Fin n => (0 : ZMod 2))) (encodeWord a) [] []
      (encodeWord (chosenWord n)) (encodeWord a).reverse) t hh
  change ((advance program)^[t']) _ =
    liftCfg (some .clear) (none, none) (fun i : Fin 2 => if i = 0 then sum else fuel)
      (SamplerMachineProduct.run t _) at hrun
  rw [hr] at hrun
  change run t' (cfg (some (.inl (.inr (.inr ())))) initial
    (encodeWord (fun _ : Fin n => (0 : ZMod 2))) (encodeWord a) [] []
    (encodeWord (chosenWord n)) (encodeWord a).reverse sum fuel) =
      cfg (some (.inr .clear)) initial
    (encodeWord (wordMul n a a)) (encodeWord a) [] [] (encodeWord (chosenWord n)) [] sum fuel at hrun
  refine ⟨(n + 1) + t', by omega, ?_⟩
  simp only [run, Function.iterate_add_apply]
  change run (n + 1) (run t' _) = _
  rw [hrun]
  simpa only [encodeWord_length] using
    clear_run initial (encodeWord (wordMul n a a)) (encodeWord a)
      (encodeWord (chosenWord n)) sum fuel

private theorem step_loop_cons (s : Control) (b : Bool) (a c sum fuel : List Bool) :
    TM2.step program (cfg (some (.inr .loop)) s a [] [] [] c [] sum (b :: fuel)) =
      some (cfg (some (.inr .sumScan)) initial a [] [] [] c [] sum fuel) := by
  dsimp only [TM2.step, TM2.stepAux, program, cfg, initial, Sum.elim_inr]
  simp only [show (1 : Fin 2) ≠ 0 by decide, ↓reduceIte,
    List.head?_cons, List.tail_cons, Option.isSome_some, Bool.cond_true, Option.some.injEq]
  congr 1
  funext k
  rcases k with k | k
  · rfl
  · fin_cases k <;> rfl

private theorem step_loop_nil (s : Control) (a c sum : List Bool) :
    TM2.step program (cfg (some (.inr .loop)) s a [] [] [] c [] sum []) =
      some (cfg none initial a [] [] [] c [] sum []) := by
  dsimp only [TM2.step, TM2.stepAux, program, cfg, initial, Sum.elim_inr]
  simp only [show (1 : Fin 2) ≠ 0 by decide, ↓reduceIte,
    List.head?_nil, List.tail_nil, Option.isSome_none, Bool.cond_false, Option.some.injEq]
  congr 1
  funext k
  rcases k with k | k
  · rfl
  · fin_cases k <;> rfl

theorem zipWith_xor_encodeWord {n : ℕ} (u v : BinaryWord n) :
    (encodeWord u).zipWith Bool.xor (encodeWord v) = encodeWord (wordAdd u v) := by
  have h := SamplerMachineAccumulate.addScaled_encodeWord (1 : ZMod 2) u v
  have hv : wordScale (1 : ZMod 2) v = v := by funext i; simp [wordScale]
  rw [hv] at h
  simpa [SamplerMachineAccumulate.addScaled, encodeBit] using h

theorem round_run {n : ℕ} (s : Control) (a sum : BinaryWord n) (b : Bool) (fuel : List Bool) :
    ∃ t ≤ n * (4 * n + 5) + 5 * n + 7,
      run t (cfg (some (.inr .loop)) s (encodeWord a) [] [] []
        (encodeWord (chosenWord n)) [] (encodeWord sum) (b :: fuel)) =
      cfg (some (.inr .loop)) initial (encodeWord (wordMul n a a)) [] [] []
        (encodeWord (chosenWord n)) [] (encodeWord (wordAdd sum a)) fuel := by
  obtain ⟨t, ht, hr⟩ := square_call a (encodeWord (wordAdd sum a)) fuel
  have ha := sum_run initial (encodeWord a) [] (encodeWord (chosenWord n)) []
    (encodeWord sum) fuel (by simp only [encodeWord_length])
  simp only [encodeWord_length, zipWith_xor_encodeWord] at ha
  have hp := prepare_run initial (encodeWord a) (encodeWord (chosenWord n))
    (encodeWord (wordAdd sum a)) fuel
  simp only [encodeWord_length, ← SamplerMachinePower.encodeWord_zero] at hp
  refine ⟨t + (2 * n + 2) + (2 * n + 2) + 1, by omega, ?_⟩
  rw [run_succ (step_loop_cons s b (encodeWord a) (encodeWord (chosenWord n))
    (encodeWord sum) fuel)]
  simp only [run, Function.iterate_add_apply]
  change run t (run (2 * n + 2) (run (2 * n + 2) _)) = _
  rw [ha, hp, hr]

def frobeniusStep (n : ℕ) (state : BinaryWord n × BinaryWord n) :
    BinaryWord n × BinaryWord n := (wordMul n state.1 state.1, wordAdd state.2 state.1)

/-- Complete finite execution of any requested number of trace rounds. -/
theorem run_rounds {n : ℕ} (s : Control) (state : BinaryWord n × BinaryWord n)
    (fuel : List Bool) :
    ∃ t ≤ fuel.length * (n * (4 * n + 5) + 5 * n + 7) + 1,
      run t (cfg (some (.inr .loop)) s (encodeWord state.1) [] [] []
        (encodeWord (chosenWord n)) [] (encodeWord state.2) fuel) =
      cfg none initial (encodeWord (((frobeniusStep n)^[fuel.length]) state).1) [] [] []
        (encodeWord (chosenWord n)) []
        (encodeWord (((frobeniusStep n)^[fuel.length]) state).2) [] := by
  induction fuel generalizing s state with
  | nil =>
      refine ⟨1, by simp, ?_⟩
      exact run_succ (step_loop_nil s (encodeWord state.1) (encodeWord (chosenWord n))
        (encodeWord state.2)) 0
  | cons b fuel ih =>
      obtain ⟨ts, hts, hs⟩ := round_run s state.1 state.2 b fuel
      obtain ⟨tr, htr, hr⟩ := ih initial (frobeniusStep n state)
      refine ⟨tr + ts, ?_, ?_⟩
      · simp only [List.length_cons]
        nlinarith
      · simp only [run, Function.iterate_add_apply]
        change run tr (run ts _) = _
        rw [hs]
        change run tr (cfg (some (.inr .loop)) initial
          (encodeWord (frobeniusStep n state).1) [] [] []
          (encodeWord (chosenWord n)) [] (encodeWord (frobeniusStep n state).2) fuel) = _
        rw [hr]
        simp only [List.length_cons, Function.iterate_succ_apply]

open scoped BigOperators

theorem wordEval_frobenius_iterate (n k : ℕ) (state : BinaryWord n × BinaryWord n) :
    wordEval n (((frobeniusStep n)^[k]) state).1 = wordEval n state.1 ^ (2 ^ k) ∧
      wordEval n (((frobeniusStep n)^[k]) state).2 =
        wordEval n state.2 + ∑ j ∈ Finset.range k, wordEval n state.1 ^ (2 ^ j) := by
  induction k with
  | zero => simp
  | succ k ih =>
      have hadd (u v : BinaryWord n) :
          wordEval n (wordAdd u v) = wordEval n u + wordEval n v :=
        (wordEval n).map_add u v
      rw [Function.iterate_succ_apply']
      simp only [frobeniusStep, wordEval_mul, hadd]
      rw [ih.1, ih.2]
      constructor
      · rw [pow_succ, pow_mul, pow_two]
      · rw [Finset.sum_range_succ]
        ring

theorem frobenius_iterate_sum {n : ℕ} (hn : 0 < n) (u : BinaryWord n) :
    (((frobeniusStep n)^[n]) (u, 0)).2 = wordFrobeniusSum n u := by
  apply (wordEval_bijective n).injective
  rw [(wordEval_frobenius_iterate n n (u, 0)).2, wordEval_frobeniusSum hn]
  simp only [map_zero, zero_add]
  exact (Fin.sum_univ_eq_sum_range (fun j => wordEval n u ^ (2 ^ j)) n).symm

/-- The raw eight-stack program computes every coefficient of the exact
Frobenius trace sum in cubic time in the field's binary dimension. The
selected modulus is preserved and all multiplication work stacks are empty.
Supplying the input bank and extracting its constant coefficient are separate
small calling operations, not hidden here as unit-cost instructions. -/
theorem run_frobeniusSum {n : ℕ} (hn : 0 < n) (u : BinaryWord n) :
    ∃ t ≤ n * (n * (4 * n + 5) + 5 * n + 7) + 1,
      run t (cfg (some (.inr .loop)) initial (encodeWord u) [] [] []
        (encodeWord (chosenWord n)) [] (encodeWord (0 : BinaryWord n))
        (List.replicate n true)) =
      cfg none initial (encodeWord (((frobeniusStep n)^[n]) (u, 0)).1) [] [] []
        (encodeWord (chosenWord n)) [] (encodeWord (wordFrobeniusSum n u)) [] := by
  simpa only [List.length_replicate, frobenius_iterate_sum hn] using
    run_rounds initial (u, 0) (List.replicate n true)

theorem trace_runtime_polynomial (n : ℕ) :
    n * (n * (4 * n + 5) + 5 * n + 7) + 1 ≤ 10 * (n + 1) ^ 3 := by
  nlinarith [Nat.zero_le (n ^ 3)]

/-- The constant coefficient is the trace bit, in the actual stored order. -/
theorem head_trace_word (n : ℕ) (u : BinaryWord n) :
    (encodeWord (wordFrobeniusSum n u)).head?.getD false = encodeBit (traceBit n u) := by
  cases n with
  | zero => simp [encodeWord, traceBit, encodeBit]
  | succ n => simp [encodeWord, traceBit, List.ofFn_succ]

end EthInapproximability.CurrentPaper.SamplerMachineTrace
