import EthInapproximability.CurrentPaper.BitMachineSubroutine

/-!
# A literal bounded simulation of a Boolean-stack machine

Source: frozen v8 `05-iteration.tex`, slow diagonal, and `06-eth.tex`, the
bounded cutoff simulations. A fresh Boolean stack contains one cell per
permitted transition. Each original label first pops that stack. Exhaustion
halts with a finite timeout flag; an original halt has no timeout flag.

The runtime below starts from an explicitly preloaded configuration. It does
not silently count creation of unary fuel, input preparation, output decoding,
or the outer prefix scan as free operations.
-/

namespace EthInapproximability.CurrentPaper.BoundedBitMachine

open Turing Turing.TM2.Stmt
open BitMachine BitMachineEncoding BitMachineComposition BitMachineSubroutine

variable (M : Machine)

abbrev Stack := Fin M.stackCount ⊕ Unit
abbrev Label := Fin M.labelCount ⊕ Unit
abbrev Control := Fin M.controlCount × Option Bool
abbrev Config := TM2.Cfg (fun _ : Stack M => Bool) (Label M) (Control M)

def program : Label M → TM2.Stmt (fun _ : Stack M => Bool) (Label M) (Control M)
  | .inl l => pop (.inr ()) (fun v b => (v.1, b))
      (branch (fun v => v.2.isSome)
        (load (fun v => (v.1, none)) (liftStmt none (M.program l)))
        (load (fun v => (v.1, some false)) halt))
  | .inr () => pop (.inl M.input) (fun v b => (v.1, b))
      (branch (fun v => v.2.isSome)
        (branch (fun v => v.2.getD false)
          (load (fun v => (v.1, none)) (goto (fun _ => .inl M.start)))
          (push (.inr ()) (fun _ => false)
            (load (fun v => (v.1, none)) (goto (fun _ => .inr ())))))
        (load (fun v => (v.1, some false)) halt))

def embed (fuel : ℕ) (c : M.Config) : Config M :=
  liftCfg none none (fun _ => List.replicate fuel false) c

def terminal (flag : Option Bool) (fuel : ℕ) (c : M.Config) : Config M :=
  ⟨none, (c.var, flag), Sum.elim c.stk (fun _ => List.replicate fuel false)⟩

def run (t : ℕ) (c : Config M) : Config M := ((advance (program M))^[t]) c

theorem run_succ (n : ℕ) (c : Config M) :
    run M (n + 1) c = advance (program M) (run M n c) :=
  Function.iterate_succ_apply' _ _ _

private theorem fuel_update (S : Fin M.stackCount → List Bool) (xs ys : List Bool) :
    Function.update (Sum.elim S (fun _ : Unit => xs)) (.inr ()) ys =
      Sum.elim S (fun _ : Unit => ys) := by
  funext k
  rcases k with k | k
  · simp
  · cases k; simp

theorem step_positive (n : ℕ) (c : M.Config) (hc : c.l ≠ none) :
    advance (program M) (embed M (n + 1) c) = embed M n (M.step c) := by
  rcases c with ⟨l, v, S⟩
  cases l with
  | none => exact (hc rfl).elim
  | some l =>
      simp only [advance, program, embed, liftCfg, TM2.step, Option.getD_some,
        TM2.stepAux, Sum.elim_inr, List.replicate_succ, List.head?_cons,
        List.tail_cons, Option.isSome_some, cond_true, fuel_update]
      exact lift_stepAux none (M.program l) v none S (fun _ => List.replicate n false)

theorem step_empty (c : M.Config) (hc : c.l ≠ none) :
    advance (program M) (embed M 0 c) = terminal M (some false) 0 c := by
  rcases c with ⟨l, v, S⟩
  cases l with
  | none => exact (hc rfl).elim
  | some l => simp [advance, program, embed, liftCfg, terminal, TM2.step,
      TM2.stepAux]

theorem run_until (t extra : ℕ) (c : M.Config)
    (h : ∀ i < t, (M.run i c).l ≠ none) :
    run M t (embed M (t + extra) c) = embed M extra (M.run t c) := by
  induction t generalizing extra with
  | zero => simp [run]
  | succ t ih =>
      have heq : t + 1 + extra = t + (extra + 1) := by omega
      rw [heq]
      rw [run_succ]
      rw [ih (extra + 1) (fun i hi => h i (by omega)),
        step_positive M extra _ (h t (by omega)), BitMachine.run_succ]

theorem nonhalt_prefix (c : M.Config) (n : ℕ) (h : (M.run n c).l ≠ none) :
    ∀ i ≤ n, (M.run i c).l ≠ none := by
  intro i hi hh
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hi
  rw [BitMachine.run_add, BitMachine.run_halted M _ hh] at h
  exact h hh

theorem run_timeout (c : M.Config) (n : ℕ) (h : (M.run n c).l ≠ none) :
    run M (n + 1) (embed M n c) = terminal M (some false) 0 (M.run n c) := by
  have hr := run_until M n 0 c (fun i hi => nonhalt_prefix M c n h i (by omega))
  simp only [Nat.add_zero] at hr
  rw [run_succ]
  rw [hr, step_empty M _ h]

theorem embed_halted (c : M.Config) (n : ℕ) (h : c.l = none) :
    embed M n c = terminal M none n c := by
  simp [embed, liftCfg, terminal, h]

theorem run_success (c : M.Config) (n : ℕ) (h : (M.run n c).l = none) :
    ∃ remaining ≤ n, run M (n + 1) (embed M n c) =
      terminal M none remaining (M.run n c) := by
  obtain ⟨t, ht, hh, heq, hfirst⟩ := first_halt_cfg M.program c n h
  change (M.run t c).l = none at hh
  change M.run t c = M.run n c at heq
  change ∀ k < t, (M.run k c).l ≠ none at hfirst
  have hr := run_until M t (n - t) c hfirst
  rw [Nat.add_sub_of_le ht, heq, embed_halted M _ _ h] at hr
  refine ⟨n - t, by omega, ?_⟩
  have hn : n + 1 = (n + 1 - t) + t := by omega
  rw [hn]
  change ((advance (program M))^[(n + 1 - t) + t]) (embed M n c) = _
  rw [Function.iterate_add_apply]
  change ((advance (program M))^[n + 1 - t]) (run M t (embed M n c)) = _
  rw [hr, BitMachineSubroutine.run_halted _ _ rfl]

/-- Both branches return the exact source state at the requested time.
The finite flag, not a predicate oracle, distinguishes timeout from success. -/
theorem bounded_simulation (c : M.Config) (n : ℕ) :
    ∃ remaining ≤ n,
      run M (n + 1) (embed M n c) =
        terminal M (if (M.run n c).l = none then none else some false)
          remaining (M.run n c) := by
  by_cases h : (M.run n c).l = none
  · simpa only [h, if_true] using run_success M c n h
  · exact ⟨0, Nat.zero_le _, by simpa only [h, if_false] using run_timeout M c n h⟩

noncomputable def machine : Machine :=
  ofFinite (.inl M.input) (.inl M.output) (.inr ())
    (M.initial, none) (program M)

noncomputable def encode (c : Config M) : (machine M).Config :=
  renameCfg (Fintype.equivFin (Stack M)) (Fintype.equivFin (Label M))
    (Fintype.equivFin (Control M)) c

theorem machine_run (c : Config M) (n : ℕ) :
    (machine M).run n (encode M c) = encode M (run M n c) :=
  ofFinite_run _ _ _ _ _ c n

/-- A fixed finite Boolean-stack machine implements the simulation with
exactly the stated transition allowance, from the displayed loaded state. -/
theorem machine_bounded_simulation (c : M.Config) (n : ℕ) :
    ∃ remaining ≤ n,
      (machine M).run (n + 1) (encode M (embed M n c)) =
        encode M (terminal M (if (M.run n c).l = none then none else some false)
          remaining (M.run n c)) := by
  obtain ⟨r, hr, heq⟩ := bounded_simulation M c n
  exact ⟨r, hr, by rw [machine_run, heq]⟩

/-- The input prefix represents a unary budget and is physically consumed.
The separator is followed by the exact original machine input. -/
def packed (n : ℕ) (bits : List Bool) : List Bool :=
  List.replicate n false ++ true :: bits

def preparing (fuel : ℕ) (bits : List Bool) : Config M :=
  ⟨some (.inr ()), (M.initial, none),
    Sum.elim (M.init bits).stk (fun _ => List.replicate fuel false)⟩

private theorem init_tail (b : Bool) (bits : List Bool) :
    Function.update (M.init (b :: bits)).stk M.input bits = (M.init bits).stk := by
  funext k
  by_cases h : k = M.input
  · subst k; simp [Machine.init]
  · simp [Machine.init, h]

theorem prepare_step_false (fuel : ℕ) (bits : List Bool) :
    advance (program M) (preparing M fuel (false :: bits)) =
      preparing M (fuel + 1) bits := by
  simp only [advance, program, preparing, TM2.step, Option.getD_some,
    TM2.stepAux, Sum.elim_inl, Machine.init, if_true, List.head?_cons,
    List.tail_cons, Option.isSome_some, cond_true, Option.getD_some,
    cond_false]
  rw [sum_update]
  have ht := init_tail M false bits
  change Function.update (fun k => if k = M.input then false :: bits else [])
    M.input bits = (fun k => if k = M.input then bits else []) at ht
  rw [ht]
  simp only [Sum.elim_inr]
  rw [fuel_update, List.replicate_succ]

theorem prepare_step_true (fuel : ℕ) (bits : List Bool) :
    advance (program M) (preparing M fuel (true :: bits)) =
      embed M fuel (M.init bits) := by
  simp only [advance, program, preparing, TM2.step, Option.getD_some,
    TM2.stepAux, Sum.elim_inl, Machine.init, if_true, List.head?_cons,
    List.tail_cons, Option.isSome_some, cond_true, Option.getD_some]
  rw [sum_update]
  have ht := init_tail M true bits
  change Function.update (fun k => if k = M.input then true :: bits else [])
    M.input bits = (fun k => if k = M.input then bits else []) at ht
  rw [ht]
  rfl

theorem prepare_run (n fuel : ℕ) (bits : List Bool) :
    run M (n + 1) (preparing M fuel (packed n bits)) =
      embed M (n + fuel) (M.init bits) := by
  induction n generalizing fuel with
  | zero => simpa [run, packed] using prepare_step_true M fuel bits
  | succ n ih =>
      have hs : advance (program M) (preparing M fuel (packed (n + 1) bits)) =
          preparing M (fuel + 1) (packed n bits) := by
        simpa [packed, List.replicate_succ] using
          prepare_step_false M fuel (packed n bits)
      change ((advance (program M))^[(n + 1) + 1])
        (preparing M fuel (packed (n + 1) bits)) = _
      rw [Function.iterate_succ_apply, hs]
      change run M (n + 1) (preparing M (fuel + 1) (packed n bits)) = _
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih (fuel + 1)

theorem machine_init_packed (n : ℕ) (bits : List Bool) :
    (machine M).init (packed n bits) = encode M (preparing M 0 (packed n bits)) := by
  have hi := ofFinite_init (.inl M.input : Stack M) (.inl M.output)
    (.inr () : Label M) (M.initial, none) (program M) (packed n bits)
  change (machine M).init (packed n bits) = _ at hi
  rw [hi]
  unfold encode
  congr 1
  unfold rawInit preparing
  congr 1
  funext k
  rcases k with k | k
  · simp [rawInit, preparing, Machine.init]
  · simp [rawInit, preparing]

/-- Reading the unary budget costs n+1 steps and bounded simulation costs
another n+1. This theorem starts at ordinary machine input, not a free
multi-stack initialization. -/
theorem packed_simulation (n : ℕ) (bits : List Bool) :
    ∃ remaining ≤ n,
      (machine M).run (2 * (n + 1)) ((machine M).init (packed n bits)) =
        encode M (terminal M
          (if (M.run n (M.init bits)).l = none then none else some false)
          remaining (M.run n (M.init bits))) := by
  obtain ⟨r, hr, heq⟩ := machine_bounded_simulation M (M.init bits) n
  refine ⟨r, hr, ?_⟩
  rw [show 2 * (n + 1) = (n + 1) + (n + 1) by omega, BitMachine.run_add,
    machine_init_packed, machine_run, prepare_run]
  simpa using heq

theorem packed_outputs (n : ℕ) (bits : List Bool) :
    (machine M).OutputsWithin (packed n bits)
      ((M.run n (M.init bits)).stk M.output) (2 * (n + 1)) := by
  obtain ⟨r, hr, h⟩ := packed_simulation M n bits
  refine ⟨2 * (n + 1), le_rfl, ?_, ?_⟩ <;> rw [h]
  · rfl
  · simp only [encode, renameCfg, terminal, machine, ofFinite]
    exact congrArg (Sum.elim (M.run n (M.init bits)).stk
      (fun _ : Unit => List.replicate r false))
      ((Fintype.equivFin (Stack M)).symm_apply_apply (.inl M.output))

/-- Parsing only specifies the semantics; `prepare_run` charges the actual
prefix read. An absent separator is rejected after consuming the whole word. -/
def parseBudget : List Bool → ℕ × Option (List Bool)
  | [] => (0, none)
  | true :: bits => (0, some bits)
  | false :: bits => let p := parseBudget bits; (p.1 + 1, p.2)

theorem parseBudget_spec (input : List Bool) :
    match (parseBudget input).2 with
    | none => input = List.replicate (parseBudget input).1 false
    | some bits => input = packed (parseBudget input).1 bits := by
  induction input with
  | nil => rfl
  | cons b bits ih =>
      cases b with
      | true => rfl
      | false =>
          simp only [parseBudget]
          cases h : (parseBudget bits).2 with
          | none =>
              simp only [h] at ih ⊢
              rw [List.replicate_succ, ← ih]
          | some rest =>
              simp only [h] at ih ⊢
              simpa only [packed, List.replicate_succ, List.cons_append] using
                congrArg (List.cons false) ih

theorem parseBudget_length (input : List Bool) : (parseBudget input).1 ≤ input.length := by
  induction input with
  | nil => rfl
  | cons b bits ih => cases b <;> simp only [parseBudget, List.length_cons] <;> omega

theorem parseBudget_packed (n : ℕ) (bits : List Bool) :
    parseBudget (packed n bits) = (n, some bits) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change ((parseBudget (packed n bits)).1 + 1, (parseBudget (packed n bits)).2) = _
      rw [ih]

theorem prepare_step_empty (fuel : ℕ) :
    advance (program M) (preparing M fuel []) =
      terminal M (some false) fuel (M.init []) := by
  simp only [advance, program, preparing, terminal, Machine.init, ite_self,
    TM2.step, Option.getD_some, TM2.stepAux, Sum.elim_inl, List.head?_nil,
    List.tail_nil, Option.isSome_none, cond_false]
  rw [sum_update]
  congr 1
  funext k
  cases k with
  | inl k => simp
  | inr k => rfl

theorem prepare_without_separator (n fuel : ℕ) :
    run M (n + 1) (preparing M fuel (List.replicate n false)) =
      terminal M (some false) (n + fuel) (M.init []) := by
  induction n generalizing fuel with
  | zero => simpa only [run, Function.iterate_one, List.replicate_zero, Nat.zero_add]
      using prepare_step_empty M fuel
  | succ n ih =>
      change ((advance (program M))^[(n + 1) + 1]) _ = _
      rw [Function.iterate_succ_apply, List.replicate_succ, prepare_step_false]
      simpa only [run, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih (fuel + 1)

theorem machine_init_preparing (input : List Bool) :
    (machine M).init input = encode M (preparing M 0 input) := by
  have hi := ofFinite_init (.inl M.input : Stack M) (.inl M.output)
    (.inr () : Label M) (M.initial, none) (program M) input
  change (machine M).init input = _ at hi
  rw [hi]
  unfold encode
  congr 1
  unfold rawInit preparing
  congr 1
  funext k
  rcases k with k | k
  · simp [Machine.init]
  · simp

def result (input : List Bool) : List Bool :=
  match (parseBudget input).2 with
  | none => []
  | some bits => (M.run (parseBudget input).1 (M.init bits)).stk M.output

theorem outputs_all (input : List Bool) :
    (machine M).OutputsWithin input (result M input) (2 * (input.length + 1)) := by
  have hs := parseBudget_spec input
  cases h : (parseBudget input).2 with
  | none =>
      simp only [h] at hs
      have hr : (machine M).run ((parseBudget input).1 + 1) ((machine M).init input) =
          encode M (terminal M (some false) (parseBudget input).1 (M.init [])) := by
        rw [machine_init_preparing, machine_run]
        calc
          _ = encode M (run M ((parseBudget input).1 + 1)
              (preparing M 0 (List.replicate (parseBudget input).1 false))) :=
            congrArg (fun z => encode M (run M ((parseBudget input).1 + 1) (preparing M 0 z))) hs
          _ = _ := by rw [prepare_without_separator, Nat.add_zero]
      refine ⟨(parseBudget input).1 + 1, by have := parseBudget_length input; omega, ?_, ?_⟩
      · rw [hr]; rfl
      · rw [hr]
        simp only [encode, renameCfg, terminal, machine, ofFinite]
        have heq := congrArg (Sum.elim (M.init []).stk
          (fun _ : Unit => List.replicate (parseBudget input).1 false))
          ((Fintype.equivFin (Stack M)).symm_apply_apply (.inl M.output))
        exact heq.trans (by simp [result, h, Machine.init])
  | some bits =>
      simp only [h] at hs
      have ho := packed_outputs M (parseBudget input).1 bits
      rw [← hs] at ho
      exact outputsWithin_mono _ (by simpa only [result, h] using ho)
        (by have := parseBudget_length input; omega)

/-- Bounded simulation is a total linear-time encoded operation for every
fixed source program, including malformed unary prefixes. The potentially
nonhalting source program need not satisfy any correctness hypothesis. -/
theorem result_polytime : Polytime (result M) :=
  ⟨machine M, 2, 1, by simpa only [pow_one] using outputs_all M⟩

end EthInapproximability.CurrentPaper.BoundedBitMachine
