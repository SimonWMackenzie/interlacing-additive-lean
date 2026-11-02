import EthInapproximability.CurrentPaper.SamplerMachineProduct
import EthInapproximability.CurrentPaper.SamplerEnumeration

/-!
# An actual factor-product comparison subroutine

Source: locked v8 Appendix E, `lem:exact-families`, finite irreducibility
testing. A fixed seven-stack controller runs the literal multiplication
program and compares its result with a saved candidate. The comparison
consumes the product, restores the candidate, and returns one Boolean flag.
Initial zero accumulator, padded factors, modulus, and candidate are supplied
by the raw-bank caller; preparing them is a separate computational step.
-/

namespace EthInapproximability.CurrentPaper.SamplerMachineFactorTest

open Turing Turing.TM2.Stmt BitMachineEncoding BitMachineComposition
open ExecutableSmallBiasSampler SamplerMachine SamplerEnumeration

inductive Admin where
  | compare | restore
  deriving DecidableEq, Fintype

abbrev Stack := SamplerMachineProduct.Stack ⊕ Unit
abbrev Label := SamplerMachineProduct.Label ⊕ Admin
abbrev Flags := Bool × Option Bool × Option Bool
abbrev Control := SamplerMachineProduct.Control × Flags
abbrev Config := TM2.Cfg (fun _ : Stack => Bool) Label Control

def initial (flag : Bool) : Control := (SamplerMachineProduct.initial, flag, none, none)

def program : Label → TM2.Stmt (fun _ : Stack => Bool) Label Control
  | .inl l => liftStmt (some .compare) (SamplerMachineProduct.program l)
  | .inr .compare => pop (.inl (.inl 0)) (fun s b => (s.1, s.2.1, b, none))
      (branch (fun s => s.2.2.1.isSome)
        (pop (.inr ()) (fun s b => (s.1, s.2.1, s.2.2.1, b))
          (push (.inl (.inl 2)) (fun s => s.2.2.2.getD false)
            (load (fun s => (s.1,
              s.2.1 && (s.2.2.1.getD false == s.2.2.2.getD false), none, none))
              (goto (fun _ => .inr .compare)))))
        (goto (fun _ => .inr .restore)))
  | .inr .restore => pop (.inl (.inl 2)) (fun s b => (s.1, s.2.1, b, none))
      (branch (fun s => s.2.2.1.isSome)
        (push (.inr ()) (fun s => s.2.2.1.getD false) (goto (fun _ => .inr .restore)))
        (load (fun s => initial s.2.1) halt))

def cfg (l : Option Label) (s : Control)
    (a u work other c multiplier target : List Bool) : Config :=
  ⟨l, s, Sum.elim (SamplerMachineProduct.cfg none s.1 a u work other c multiplier).stk
    (fun _ => target)⟩

def run (t : ℕ) (q : Config) := ((advance program)^[t]) q

private theorem run_add (t s : ℕ) (q : Config) : run (t + s) q = run t (run s q) :=
  Function.iterate_add_apply _ _ _ _

private theorem run_succ {c d : Config} (h : TM2.step program c = some d) (n : ℕ) :
    run (n + 1) c = run n d := by
  simp only [run, Function.iterate_succ_apply, advance, h, Option.getD_some]

private theorem step_compare_cons (s : Control) (a b : Bool)
    (as bs u work other c multiplier : List Bool) :
    TM2.step program (cfg (some (.inr .compare)) s (a :: as) u work other c multiplier
      (b :: bs)) =
      some (cfg (some (.inr .compare)) (s.1, s.2.1 && (a == b), none, none)
        as u (b :: work) other c multiplier bs) := by
  dsimp only [TM2.step, TM2.stepAux, program, cfg, SamplerMachineProduct.cfg,
    SamplerMachineAccumulate.stackContents, SamplerMachineProduct.foreign,
    Sum.elim_inl, Sum.elim_inr]
  simp only [↓reduceIte, List.head?_cons, List.tail_cons, Option.isSome_some,
    Option.getD_some, Bool.cond_true, Option.some.injEq]
  congr 1
  funext k
  rcases k with (k | k) | k <;> (try fin_cases k) <;> rfl

private theorem step_compare_nil (s : Control)
    (u work other c multiplier target : List Bool) :
    TM2.step program (cfg (some (.inr .compare)) s [] u work other c multiplier target) =
      some (cfg (some (.inr .restore)) (s.1, s.2.1, none, none)
        [] u work other c multiplier target) := by
  dsimp only [TM2.step, TM2.stepAux, program, cfg, SamplerMachineProduct.cfg,
    SamplerMachineAccumulate.stackContents, SamplerMachineProduct.foreign,
    Sum.elim_inl, Sum.elim_inr]
  simp only [↓reduceIte, List.head?_nil, List.tail_nil, Option.isSome_none,
    Bool.cond_false, Option.some.injEq]
  congr 1
  funext k
  rcases k with (k | k) | k <;> (try fin_cases k) <;> rfl

private theorem step_restore_cons (s : Control) (b : Bool)
    (a u work other c multiplier target : List Bool) :
    TM2.step program (cfg (some (.inr .restore)) s a u (b :: work) other c multiplier target) =
      some (cfg (some (.inr .restore)) (s.1, s.2.1, some b, none)
        a u work other c multiplier (b :: target)) := by
  dsimp only [TM2.step, TM2.stepAux, program, cfg, SamplerMachineProduct.cfg,
    SamplerMachineAccumulate.stackContents, SamplerMachineProduct.foreign,
    Sum.elim_inl, Sum.elim_inr]
  simp only [show (2 : Fin 4) ≠ 0 by decide, show (2 : Fin 4) ≠ 1 by decide,
    ↓reduceIte, List.head?_cons, List.tail_cons, Option.isSome_some,
    Option.getD_some, Bool.cond_true, Option.some.injEq]
  congr 1
  funext k
  rcases k with (k | k) | k <;> (try fin_cases k) <;> rfl

private theorem step_restore_nil (s : Control)
    (a u other c multiplier target : List Bool) :
    TM2.step program (cfg (some (.inr .restore)) s a u [] other c multiplier target) =
      some (cfg none (initial s.2.1) a u [] other c multiplier target) := by
  dsimp only [TM2.step, TM2.stepAux, program, cfg, SamplerMachineProduct.cfg,
    SamplerMachineAccumulate.stackContents, SamplerMachineProduct.foreign,
    Sum.elim_inl, Sum.elim_inr]
  simp only [show (2 : Fin 4) ≠ 0 by decide, show (2 : Fin 4) ≠ 1 by decide,
    ↓reduceIte, List.head?_nil, List.tail_nil, Option.isSome_none,
    Bool.cond_false, Option.some.injEq]
  congr 1
  funext k
  rcases k with (k | k) | k <;> (try fin_cases k) <;> rfl

theorem compare_scan (s : Control) (a target u work other c multiplier : List Bool)
    (hlen : a.length = target.length) :
    run (a.length + 1) (cfg (some (.inr .compare)) s a u work other c multiplier target) =
      cfg (some (.inr .restore)) (s.1, s.2.1 && decide (a = target), none, none)
        [] u (target.reverse ++ work) other c multiplier [] := by
  induction a generalizing s target work with
  | nil =>
      have ht : target = [] := List.length_eq_zero_iff.mp hlen.symm
      subst target
      simpa using run_succ (step_compare_nil s u work other c multiplier []) 0
  | cons a as ih =>
      cases target with
      | nil => simp at hlen
      | cons b bs =>
          have hl : as.length = bs.length := by simpa using hlen
          rw [List.length_cons, run_succ (step_compare_cons s a b as bs u work other c multiplier)]
          simpa only [List.reverse_cons, List.append_assoc, List.singleton_append,
            List.cons.injEq, Bool.decide_and, Bool.decide_eq_true,
            Bool.and_assoc, beq_iff_eq] using
              ih (s.1, s.2.1 && (a == b), none, none) bs (b :: work) hl

theorem restore_run (s : Control) (a u work other c multiplier target : List Bool) :
    run (work.length + 1) (cfg (some (.inr .restore)) s a u work other c multiplier target) =
      cfg none (initial s.2.1) a u [] other c multiplier (work.reverse ++ target) := by
  induction work generalizing s target with
  | nil => simpa using run_succ (step_restore_nil s a u other c multiplier target) 0
  | cons b work ih =>
      rw [List.length_cons, run_succ (step_restore_cons s b a u work other c multiplier target)]
      simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using
        ih (s.1, s.2.1, some b, none) (b :: target)

/-- The target word is restored exactly; product and comparison scratch
are consumed. The equal-width premise is supplied by typed coefficient words. -/
theorem compare_run (a target u c : List Bool) (hlen : a.length = target.length) :
    run (2 * a.length + 2)
      (cfg (some (.inr .compare)) (initial true) a u [] [] c [] target) =
        cfg none (initial (decide (a = target))) [] u [] [] c [] target := by
  have hs := compare_scan (initial true) a target u [] [] c [] hlen
  simp only [initial, Bool.true_and, List.append_nil] at hs
  have hr := restore_run (SamplerMachineProduct.initial, decide (a = target), none, none)
    [] u target.reverse [] c [] []
  simp only [List.length_reverse, List.reverse_reverse, List.append_nil, ← hlen] at hr
  rw [show 2 * a.length + 2 = (a.length + 1) + (a.length + 1) by omega]
  simp only [initial] at ⊢
  rw [run_add, hs, hr]
  rfl

theorem product_call {w : ℕ} (modulus a u : BinaryWord w) (v target : List Bool) :
    ∃ t ≤ v.length * (4 * w + 5) + 1,
      run t (cfg (some (.inl (.inr (.inr ())))) (initial true)
        (encodeWord a) (encodeWord u) [] [] (encodeWord modulus) v target) =
      cfg (some (.inr .compare)) (initial true)
        (encodeWord (v.foldl (SamplerMachineProduct.hornerStep modulus u) a)) (encodeWord u)
        [] [] (encodeWord modulus) [] target := by
  obtain ⟨t, ht, hr⟩ := SamplerMachineProduct.run_horner modulus
    SamplerMachineProduct.initial a u v
  have hh : (SamplerMachineProduct.run t
      (SamplerMachineProduct.cfg (some (.inr (.inr ()))) SamplerMachineProduct.initial
        (encodeWord a) (encodeWord u) [] [] (encodeWord modulus) v)).l = none := by
    rw [hr]
    rfl
  obtain ⟨t', ht', hrun⟩ := BitMachineSubroutine.lift_outputs
    SamplerMachineProduct.program program (some .compare) (fun _ => rfl)
    (true, none, none) (fun _ : Unit => target)
    (SamplerMachineProduct.cfg (some (.inr (.inr ()))) SamplerMachineProduct.initial
      (encodeWord a) (encodeWord u) [] [] (encodeWord modulus) v) t hh
  refine ⟨t', ht'.trans ht, ?_⟩
  change ((advance program)^[t']) _ = _
  change ((advance program)^[t']) _ = liftCfg (some .compare) (true, none, none)
    (fun _ : Unit => target) (SamplerMachineProduct.run t _) at hrun
  rw [hr] at hrun
  exact hrun

/-- Exact fixed-width Horner result comparison, including every transfer
and final halt. This uses arbitrary modulus coefficients. -/
theorem run_hornerCompare {w : ℕ} (modulus a u target : BinaryWord w) (v : List Bool) :
    ∃ t ≤ v.length * (4 * w + 5) + 2 * w + 3,
      run t (cfg (some (.inl (.inr (.inr ())))) (initial true)
        (encodeWord a) (encodeWord u) [] [] (encodeWord modulus) v (encodeWord target)) =
      cfg none (initial (decide (v.foldl (SamplerMachineProduct.hornerStep modulus u) a = target)))
        [] (encodeWord u) [] [] (encodeWord modulus) [] (encodeWord target) := by
  obtain ⟨t, ht, hr⟩ := product_call modulus a u v (encodeWord target)
  have hc := compare_run
    (encodeWord (v.foldl (SamplerMachineProduct.hornerStep modulus u) a))
    (encodeWord target) (encodeWord u) (encodeWord modulus) (by simp)
  simp only [encodeWord_length, encodeWord_injective.eq_iff] at hc
  refine ⟨(2 * w + 2) + t, by omega, ?_⟩
  rw [run_add, hr, hc]

/-- The actual finite controller decides whether two arbitrary `n`-bit
factors multiply to the monic degree-`n` candidate. Width `2*n` prevents
truncation. No irreducible modulus has been chosen or assumed. -/
theorem run_fixedFactorProduct {n : ℕ} (hn : 0 < n) (c u v : BinaryWord n) :
    ∃ t ≤ (2 * n) * (4 * (2 * n) + 5) + 4 * n + 3,
      run t (cfg (some (.inl (.inr (.inr ())))) (initial true)
        (encodeWord (fun _ : Fin (2 * n) => (0 : ZMod 2)))
        (encodeWord (fun i : Fin (2 * n) => rawCoeff u i.val)) [] []
        (encodeWord (fun _ : Fin (2 * n) => (0 : ZMod 2)))
        (encodeWord (fun i : Fin (2 * n) => rawCoeff v i.val)).reverse
        (encodeWord (fun i : Fin (2 * n) => monicCoeff n c i.val))) =
      cfg none (initial (decide (∀ j : Fin (2 * n),
        monicCoeff n c j.val = rawProductCoeff u v j.val)))
        [] (encodeWord (fun i : Fin (2 * n) => rawCoeff u i.val)) [] []
        (encodeWord (fun _ : Fin (2 * n) => (0 : ZMod 2))) []
        (encodeWord (fun i : Fin (2 * n) => monicCoeff n c i.val)) := by
  have heq :
      (encodeWord (fun i : Fin (2 * n) => rawCoeff v i.val)).reverse.foldl
        (SamplerMachineProduct.hornerStep (fun _ : Fin (2 * n) => 0)
          (fun i => rawCoeff u i.val)) (fun _ => 0) =
        fun j : Fin (2 * n) => rawProductCoeff u v j.val := by
    exact hornerWith_rawProduct hn u v
  simpa only [List.length_reverse, encodeWord_length, heq, funext_iff, eq_comm,
    show 2 * (2 * n) = 4 * n by omega] using
    run_hornerCompare (fun _ : Fin (2 * n) => 0) (fun _ => 0)
      (fun i => rawCoeff u i.val) (fun i => monicCoeff n c i.val)
      (encodeWord (fun i : Fin (2 * n) => rawCoeff v i.val)).reverse

end EthInapproximability.CurrentPaper.SamplerMachineFactorTest
