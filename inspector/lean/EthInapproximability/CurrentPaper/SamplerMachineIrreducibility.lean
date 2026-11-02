import EthInapproximability.CurrentPaper.SamplerMachineFactorPredicate
import EthInapproximability.CurrentPaper.SamplerMachineSearch

/-!
# Actual exhaustive irreducibility testing

Source: locked v8 Appendix E, `lem:exact-families`. The candidate is kept
on one Boolean stack. This controller constructs the zero factor counter,
runs the implemented factor-pair search, clears the final factor counter,
and returns the negation of factor acceptance in finite control. Every work
stack is restored, providing the actual predicate needed by modulus search.
-/

namespace EthInapproximability.CurrentPaper.SamplerMachineIrreducibility

open Turing Turing.TM2.Stmt BitMachineEncoding BitMachineComposition
open ExecutableSmallBiasSampler SamplerMachine SamplerEnumeration SamplerFactorEnumeration

abbrev InnerStack := SamplerMachineSearch.Stack SamplerMachineFactorPredicate.Stack
abbrev InnerLabel := SamplerMachineSearch.Label SamplerMachineFactorPredicate.Label
abbrev InnerControl := SamplerMachineSearch.Control SamplerMachineFactorPredicate.Control
abbrev InnerConfig := SamplerMachineSearch.Config SamplerMachineFactorPredicate.Stack
  SamplerMachineFactorPredicate.Label SamplerMachineFactorPredicate.Control

def innerProgram : InnerLabel → TM2.Stmt (fun _ : InnerStack => Bool) InnerLabel InnerControl :=
  SamplerMachineSearch.program SamplerMachineFactorPredicate.program (.inr ())
    (.inr .scanU) SamplerMachineFactorPredicate.initial SamplerMachineFactorPredicate.accepts

def innerInitial : InnerControl := (SamplerMachineFactorPredicate.initial, false, none)

def innerCfg (l : Option InnerLabel) (s : InnerControl) (c pair work : List Bool) : InnerConfig :=
  SamplerMachineSearch.cfg (.inr ()) (SamplerMachineFactorPredicate.inputBank c) l s pair work

def innerBound (n : ℕ) : ℕ := 2 ^ (2 * n) * (16 * n ^ 2 + 44 * n + 36)

/-- The generic search is instantiated with the already implemented, bank-
preserving factor predicate. Both success and exhaustion branches are covered. -/
theorem inner_run {n : ℕ} (hn : 0 < n) (c : BinaryWord n) :
    ∃ (t : ℕ) (s : InnerControl) (pair : List Bool),
      t ≤ innerBound n ∧ pair.length = 2 * n ∧
      ((advance innerProgram)^[t])
        (innerCfg (some (.inl (.inr .scanU))) innerInitial (encodeWord c)
          (List.replicate (2 * n) false) []) =
        innerCfg none s (encodeWord c) pair [] ∧
      (!SamplerMachineFactorPredicate.accepts s.1) = irreducibleTest n c := by
  let P := SamplerMachineFactorPredicate.program
  let S := SamplerMachineFactorPredicate.inputBank (encodeWord c)
  let T := 16 * n ^ 2 + 36 * n + 30
  have hT : T + 4 * (2 * n) + 6 = 16 * n ^ 2 + 44 * n + 36 := by dsimp [T]; omega
  have hP := SamplerMachineFactorPredicate.predicate_contract hn c
  have heq := factorSearch_exhaustion_bit hn c
  cases hf : factorSearch n c with
  | some found =>
      have hfind : (counterWords (2 * n)).find? (factorPredicate n c) = some found := hf
      obtain ⟨t, s, ht, ha, hr⟩ := SamplerMachineSearch.search_allWords P (.inr ())
        (.inr .scanU) SamplerMachineFactorPredicate.initial SamplerMachineFactorPredicate.accepts
        S (2 * n) T (factorPredicate n c) hP found hfind
      refine ⟨t, (s, false, none), found, ?_, ?_, hr, ?_⟩
      · simpa only [innerBound, hT] using ht
      · exact counter_member_length (List.mem_of_find?_eq_some hfind)
      · simp only [hf, reduceCtorEq, decide_false] at heq
        simpa only [ha, Bool.not_true] using heq
  | none =>
      have hpos : 0 < 2 ^ (2 * n) := by positivity
      have hc : 2 ^ (2 * n) - 1 + 1 = 2 ^ (2 * n) := by omega
      have hz (m : ℕ) : EncodedCommunication.bitsValue (List.replicate m false) = 0 := by
        induction m with
        | zero => rfl
        | succ m ih => simp [List.replicate_succ, EncodedCommunication.bitsValue, Nat.bit_val, ih]
      have hfind : (List.iterate SamplerMachineIncrement.increment (List.replicate (2 * n) false)
          (2 ^ (2 * n) - 1 + 1)).find? (factorPredicate n c) = none := by
        simpa only [hc] using hf
      obtain ⟨t, s, ht, ha, hr⟩ := SamplerMachineSearch.search_none P (.inr ())
        (.inr .scanU) SamplerMachineFactorPredicate.initial SamplerMachineFactorPredicate.accepts
        S (2 * n) T (factorPredicate n c) hP (2 ^ (2 * n) - 1)
        (List.replicate (2 * n) false) (by simp) (by rw [hz]; omega) hfind
      refine ⟨t, (s, true, none), _, ?_, ?_, hr, ?_⟩
      · simpa only [innerBound, hc, hT] using ht
      · exact increment_iterate_length (2 * n) (2 ^ (2 * n) - 1)
      · simp only [hf, decide_true] at heq
        simpa only [ha, Bool.not_false] using heq

inductive Admin where
  | fill | restore | clear
  deriving DecidableEq, Fintype

abbrev Stack := InnerStack ⊕ Unit
abbrev Label := InnerLabel ⊕ Admin
abbrev Control := InnerControl × Option Bool
abbrev Config := TM2.Cfg (fun _ : Stack => Bool) Label Control

def initial : Control := (innerInitial, none)

def source : Stack := .inl (.inl (.inl .candidate))
def factorCounter : Stack := .inl (.inl (.inr ()))

def program : Label → TM2.Stmt (fun _ : Stack => Bool) Label Control
  | .inl l => liftStmt (some .clear) (innerProgram l)
  | .inr .fill => pop source (fun s b => (s.1, b))
      (branch (fun s => s.2.isSome)
        (push (.inr ()) (fun s => s.2.getD false)
          (push factorCounter (fun _ => false) (push factorCounter (fun _ => false)
            (goto (fun _ => .inr .fill)))))
        (goto (fun _ => .inr .restore)))
  | .inr .restore => pop (.inr ()) (fun s b => (s.1, b))
      (branch (fun s => s.2.isSome)
        (push source (fun s => s.2.getD false) (goto (fun _ => .inr .restore)))
        (load (fun _ => initial) (goto (fun _ => .inl (.inl (.inr .scanU))))))
  | .inr .clear => pop factorCounter (fun s b => (s.1, b))
      (branch (fun s => s.2.isSome)
        (goto (fun _ => .inr .clear))
        (load (fun s => (s.1, none)) halt))

def cfg (l : Option Label) (s : Control) (c pair work saved : List Bool) : Config :=
  ⟨l, s, Sum.elim (innerCfg none s.1 c pair work).stk (fun _ => saved)⟩

def run (t : ℕ) (q : Config) := ((advance program)^[t]) q

def accepts (s : Control) : Bool := !SamplerMachineFactorPredicate.accepts s.1.1

private theorem run_add (t s : ℕ) (q : Config) : run (t + s) q = run t (run s q) :=
  Function.iterate_add_apply _ _ _ _

private theorem run_succ {c d : Config} (h : TM2.step program c = some d) (t : ℕ) :
    run (t + 1) c = run t d := by
  simp only [run, Function.iterate_succ_apply, advance, h, Option.getD_some]

private theorem step_fill_cons (s : Control) (b : Bool) (c pair work saved : List Bool) :
    TM2.step program (cfg (some (.inr .fill)) s (b :: c) pair work saved) =
      some (cfg (some (.inr .fill)) (s.1, some b) c (false :: false :: pair) work (b :: saved)) := by
  dsimp only [TM2.step, TM2.stepAux, program, cfg, innerCfg, SamplerMachineSearch.cfg,
    source, factorCounter, Sum.elim_inl, Sum.elim_inr]
  rw [SamplerMachineFactorPredicate.inputBank_update]
  dsimp only [SamplerMachineFactorPredicate.cfg, SamplerMachineFactorBody.cfg,
    SamplerMachineFactorPrepare.stackContents, Sum.elim_inl, Sum.elim_inr]
  simp only [List.head?_cons, List.tail_cons, Option.isSome_some, Option.getD_some,
    Bool.cond_true, Option.some.injEq]
  congr 1
  funext k
  rcases k with ((k | k) | k) | k <;> cases k <;> rfl

private theorem step_fill_nil (s : Control) (pair work saved : List Bool) :
    TM2.step program (cfg (some (.inr .fill)) s [] pair work saved) =
      some (cfg (some (.inr .restore)) (s.1, none) [] pair work saved) := by
  dsimp only [TM2.step, TM2.stepAux, program, cfg, innerCfg, SamplerMachineSearch.cfg,
    source, factorCounter, Sum.elim_inl, Sum.elim_inr]
  rw [SamplerMachineFactorPredicate.inputBank_update]
  dsimp only [SamplerMachineFactorPredicate.cfg, SamplerMachineFactorBody.cfg,
    SamplerMachineFactorPrepare.stackContents, Sum.elim_inl, Sum.elim_inr]
  simp only [List.head?_nil, List.tail_nil, Option.isSome_none, Bool.cond_false, Option.some.injEq]
  congr 1
  funext k
  rcases k with ((k | k) | k) | k <;> cases k <;> rfl

private theorem step_restore_cons (s : Control) (b : Bool) (c pair work saved : List Bool) :
    TM2.step program (cfg (some (.inr .restore)) s c pair work (b :: saved)) =
      some (cfg (some (.inr .restore)) (s.1, some b) (b :: c) pair work saved) := by
  dsimp only [TM2.step, TM2.stepAux, program, cfg, innerCfg, SamplerMachineSearch.cfg,
    source, factorCounter, Sum.elim_inl, Sum.elim_inr]
  rw [SamplerMachineFactorPredicate.inputBank_update]
  dsimp only [SamplerMachineFactorPredicate.cfg, SamplerMachineFactorBody.cfg,
    SamplerMachineFactorPrepare.stackContents, Sum.elim_inl, Sum.elim_inr]
  simp only [List.head?_cons, List.tail_cons, Option.isSome_some, Option.getD_some,
    Bool.cond_true, Option.some.injEq]
  congr 1
  funext k
  rcases k with ((k | k) | k) | k <;> cases k <;> rfl

private theorem step_restore_nil (s : Control) (c pair work : List Bool) :
    TM2.step program (cfg (some (.inr .restore)) s c pair work []) =
      some (cfg (some (.inl (.inl (.inr .scanU)))) initial c pair work []) := by
  dsimp only [TM2.step, TM2.stepAux, program, cfg, innerCfg, SamplerMachineSearch.cfg,
    source, factorCounter, Sum.elim_inl, Sum.elim_inr]
  simp only [List.head?_nil, List.tail_nil, Option.isSome_none, Bool.cond_false, Option.some.injEq]
  congr 1
  funext k
  rcases k with ((k | k) | k) | k <;> cases k <;> rfl

private theorem step_clear_cons (s : Control) (b : Bool) (c pair work saved : List Bool) :
    TM2.step program (cfg (some (.inr .clear)) s c (b :: pair) work saved) =
      some (cfg (some (.inr .clear)) (s.1, some b) c pair work saved) := by
  dsimp only [TM2.step, TM2.stepAux, program, cfg, innerCfg, SamplerMachineSearch.cfg,
    source, factorCounter, Sum.elim_inl, Sum.elim_inr]
  simp only [Function.update_self, List.head?_cons, List.tail_cons, Option.isSome_some,
    Bool.cond_true, Option.some.injEq]
  congr 1
  funext k
  rcases k with ((k | k) | k) | k <;> cases k <;> rfl

private theorem step_clear_nil (s : Control) (c work saved : List Bool) :
    TM2.step program (cfg (some (.inr .clear)) s c [] work saved) =
      some (cfg none (s.1, none) c [] work saved) := by
  dsimp only [TM2.step, TM2.stepAux, program, cfg, innerCfg, SamplerMachineSearch.cfg,
    source, factorCounter, Sum.elim_inl, Sum.elim_inr]
  simp only [Function.update_self, List.head?_nil, List.tail_nil, Option.isSome_none,
    Bool.cond_false, Option.some.injEq]
  congr 1
  funext k
  rcases k with ((k | k) | k) | k <;> cases k <;> rfl

theorem fill_run (s : Control) (c pair work saved : List Bool) :
    run (c.length + 1) (cfg (some (.inr .fill)) s c pair work saved) =
      cfg (some (.inr .restore)) (s.1, none) []
        (List.replicate (2 * c.length) false ++ pair) work (c.reverse ++ saved) := by
  induction c generalizing s pair saved with
  | nil => simpa using run_succ (step_fill_nil s pair work saved) 0
  | cons b c ih =>
      rw [List.length_cons, run_succ (step_fill_cons s b c pair work saved)]
      have heq : List.replicate (2 * c.length) false ++ false :: false :: pair =
          List.replicate (2 * (c.length + 1)) false ++ pair := by
        rw [show 2 * (c.length + 1) = 2 * c.length + 2 by omega, List.replicate_add]
        simp
      simpa only [List.length_cons, List.reverse_cons, List.append_assoc,
        List.singleton_append, heq] using ih (s.1, some b) (false :: false :: pair) (b :: saved)

theorem restore_run (s : Control) (c pair work saved : List Bool) :
    run (saved.length + 1) (cfg (some (.inr .restore)) s c pair work saved) =
      cfg (some (.inl (.inl (.inr .scanU)))) initial (saved.reverse ++ c) pair work [] := by
  induction saved generalizing s c with
  | nil => simpa using run_succ (step_restore_nil s c pair work) 0
  | cons b saved ih =>
      rw [List.length_cons, run_succ (step_restore_cons s b c pair work saved)]
      simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using
        ih (s.1, some b) (b :: c)

theorem prepare_run (c : List Bool) :
    run (2 * c.length + 2) (cfg (some (.inr .fill)) initial c [] [] []) =
      cfg (some (.inl (.inl (.inr .scanU)))) initial c (List.replicate (2 * c.length) false) [] [] := by
  have hf := fill_run initial c [] [] []
  simp only [List.append_nil] at hf
  have hr := restore_run (initial.1, none) [] (List.replicate (2 * c.length) false) [] c.reverse
  simp only [List.length_reverse, List.reverse_reverse, List.append_nil] at hr
  rw [show 2 * c.length + 2 = (c.length + 1) + (c.length + 1) by omega, run_add, hf, hr]

theorem clear_run (s : Control) (c pair work saved : List Bool) :
    run (pair.length + 1) (cfg (some (.inr .clear)) s c pair work saved) =
      cfg none (s.1, none) c [] work saved := by
  induction pair generalizing s with
  | nil => simpa using run_succ (step_clear_nil s c work saved) 0
  | cons b pair ih =>
      rw [List.length_cons, run_succ (step_clear_cons s b c pair work saved)]
      exact ih (s.1, some b)

theorem inner_cfg (l : Option InnerLabel) (s : InnerControl) (c pair work saved : List Bool) :
    liftCfg (some .clear) (none : Option Bool) (fun _ : Unit => saved) (innerCfg l s c pair work) =
      cfg (match l with | none => some (.inr .clear) | some l => some (.inl l))
        (s, none) c pair work saved := by
  cases l <;> rfl

theorem search_call {n : ℕ} (hn : 0 < n) (c : BinaryWord n) :
    ∃ (t : ℕ) (s : Control) (pair : List Bool),
      t ≤ innerBound n ∧ pair.length = 2 * n ∧
      run t (cfg (some (.inl (.inl (.inr .scanU)))) initial (encodeWord c)
        (List.replicate (2 * n) false) [] []) =
        cfg (some (.inr .clear)) s (encodeWord c) pair [] [] ∧
      accepts s = irreducibleTest n c := by
  obtain ⟨t, s, pair, ht, hp, hr, ha⟩ := inner_run hn c
  have hh : (((advance innerProgram)^[t])
      (innerCfg (some (.inl (.inr .scanU))) innerInitial (encodeWord c)
        (List.replicate (2 * n) false) [])).l = none := by rw [hr]; rfl
  obtain ⟨t', ht', hrun⟩ := BitMachineSubroutine.lift_outputs innerProgram program
    (some .clear) (fun _ => rfl) (none : Option Bool) (fun _ : Unit => [])
    (innerCfg (some (.inl (.inr .scanU))) innerInitial (encodeWord c)
      (List.replicate (2 * n) false) []) t hh
  rw [hr, inner_cfg, inner_cfg] at hrun
  exact ⟨t', (s, none), pair, ht'.trans ht, hp, hrun, ha⟩

def timeBound (n : ℕ) : ℕ := innerBound n + 4 * n + 3

/-- Complete actual irreducibility computation on the stored candidate.
No factor-predicate, cleanup, counter-preparation, or runtime assumptions
remain. The candidate is restored and every work stack finishes empty. -/
theorem run_irreducibility {n : ℕ} (hn : 0 < n) (c : BinaryWord n) :
    ∃ (t : ℕ) (s : Control), t ≤ timeBound n ∧
      run t (cfg (some (.inr .fill)) initial (encodeWord c) [] [] []) =
        cfg none s (encodeWord c) [] [] [] ∧ accepts s = irreducibleTest n c := by
  have hp := prepare_run (encodeWord c)
  simp only [encodeWord_length] at hp
  obtain ⟨ts, s, pair, hts, hpair, hs, ha⟩ := search_call hn c
  have hc := clear_run s (encodeWord c) pair [] []
  rw [hpair] at hc
  refine ⟨(2 * n + 1) + (ts + (2 * n + 2)), (s.1, none), ?_, ?_, ha⟩
  · unfold timeBound
    omega
  · rw [run_add (2 * n + 1) (ts + (2 * n + 2)), run_add ts (2 * n + 2), hp, hs, hc]

def inputBank : Stack → List Bool := fun _ => []

theorem inputBank_update (c : List Bool) :
    Function.update inputBank source c = (cfg none initial c [] [] []).stk := by
  funext k
  rcases k with ((k | k) | k) | k <;> cases k <;> rfl

/-- Exact all-width-input contract for the outer monic-modulus search.
Only the candidate stack is populated on entry and exit. The same concrete
finite program works at every positive width and returns the original test. -/
theorem predicate_contract {n : ℕ} (hn : 0 < n) (q : List Bool) (hq : q.length = n) :
    ∃ (t : ℕ) (s : Control), t ≤ timeBound n ∧
      ((advance program)^[t])
        ⟨some (.inr .fill), initial, Function.update inputBank source q⟩ =
        ⟨none, s, Function.update inputBank source q⟩ ∧
      accepts s = irreducibleTest n (decodeWord n q) := by
  obtain ⟨t, s, ht, hr, ha⟩ := run_irreducibility hn (decodeWord n q)
  refine ⟨t, s, ht, ?_, ha⟩
  rw [inputBank_update]
  simpa only [encodeWord_decodeWord n q hq] using hr

end EthInapproximability.CurrentPaper.SamplerMachineIrreducibility
