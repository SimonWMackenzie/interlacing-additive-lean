import EthInapproximability.CurrentPaper.SamplerMachineIrreducibility

/-!
# The complete finite-machine irreducible-polynomial search

Source: locked v8 Appendix E, `lem:exact-families`. The input length is the
field degree. An actual scan initializes its candidate counter; nested
implemented searches then return the very first irreducible polynomial in
the executable sampler's enumeration. No prepared work bank, irreducibility
oracle, or runtime hypothesis is used by the final machine theorem.
-/

namespace EthInapproximability.CurrentPaper.SamplerMachineChosenWord

set_option maxHeartbeats 1000000

open Turing Turing.TM2.Stmt BitMachineEncoding BitMachineComposition
open ExecutableSmallBiasSampler SamplerMachine SamplerEnumeration

abbrev InnerStack := SamplerMachineSearch.Stack SamplerMachineIrreducibility.Stack
abbrev InnerLabel := SamplerMachineSearch.Label SamplerMachineIrreducibility.Label
abbrev InnerControl := SamplerMachineSearch.Control SamplerMachineIrreducibility.Control
abbrev InnerConfig := TM2.Cfg (fun _ : InnerStack => Bool) InnerLabel InnerControl

def innerProgram : InnerLabel → TM2.Stmt (fun _ : InnerStack => Bool) InnerLabel InnerControl :=
  SamplerMachineSearch.program SamplerMachineIrreducibility.program
    SamplerMachineIrreducibility.source (.inr .fill)
    SamplerMachineIrreducibility.initial SamplerMachineIrreducibility.accepts

def innerInitial : InnerControl := (SamplerMachineIrreducibility.initial, false, none)

def innerCfg (l : Option InnerLabel) (s : InnerControl) (candidate work : List Bool) : InnerConfig :=
  SamplerMachineSearch.cfg SamplerMachineIrreducibility.source
    SamplerMachineIrreducibility.inputBank l s candidate work

def searchBound (n : ℕ) : ℕ := 2 ^ n * (SamplerMachineIrreducibility.timeBound n + 4 * n + 6)

theorem first_passing {n : ℕ} (hn : 0 < n) :
    (counterWords n).find? (fun q => irreducibleTest n (decodeWord n q)) =
      some (encodeWord (chosenWord n)) := by
  have hnonempty : (allWords n).find? (irreducibleTest n) ≠ none := by
    intro heq
    obtain ⟨c, hc⟩ := exists_passing_word n hn
    exact (List.find?_eq_none.mp heq c (mem_allWords c)) hc
  rw [counterWords_find]
  cases heq : (allWords n).find? (irreducibleTest n) with
  | none => exact False.elim (hnonempty heq)
  | some c => simp only [chosenWord, heq, Option.map_some, Option.getD_some]

/-- Both finite searches and all factor arithmetic are now instantiated. -/
theorem search_run {n : ℕ} (hn : 0 < n) :
    ∃ (t : ℕ) (s : InnerControl), t ≤ searchBound n ∧
      ((advance innerProgram)^[t])
        (innerCfg (some (.inl (.inr .fill))) innerInitial (List.replicate n false) []) =
        innerCfg none s (encodeWord (chosenWord n)) [] := by
  obtain ⟨t, s, ht, _, hr⟩ := SamplerMachineSearch.search_allWords
    SamplerMachineIrreducibility.program SamplerMachineIrreducibility.source (.inr .fill)
    SamplerMachineIrreducibility.initial SamplerMachineIrreducibility.accepts
    SamplerMachineIrreducibility.inputBank n (SamplerMachineIrreducibility.timeBound n)
    (fun q => irreducibleTest n (decodeWord n q))
    (SamplerMachineIrreducibility.predicate_contract hn)
    (encodeWord (chosenWord n)) (first_passing hn)
  exact ⟨t, (s, false, none), ht, hr⟩

inductive Admin where
  | scan | restore | check
  deriving DecidableEq, Fintype

abbrev Stack := InnerStack ⊕ Unit
abbrev Label := InnerLabel ⊕ Admin
abbrev Control := InnerControl × Option Bool
abbrev Config := TM2.Cfg (fun _ : Stack => Bool) Label Control

def source : Stack := .inl (.inl SamplerMachineIrreducibility.source)
def initial : Control := (innerInitial, none)

def program : Label → TM2.Stmt (fun _ : Stack => Bool) Label Control
  | .inl l => liftStmt none (innerProgram l)
  | .inr .scan => pop source (fun s b => (s.1, b))
      (branch (fun s => s.2.isSome)
        (push (.inr ()) (fun _ => false) (goto (fun _ => .inr .scan)))
        (goto (fun _ => .inr .restore)))
  | .inr .restore => pop (.inr ()) (fun s b => (s.1, b))
      (branch (fun s => s.2.isSome)
        (push source (fun _ => false) (goto (fun _ => .inr .restore)))
        (goto (fun _ => .inr .check)))
  | .inr .check => pop source (fun s b => (s.1, b))
      (branch (fun s => s.2.isSome)
        (push source (fun s => s.2.getD false)
          (load (fun _ => initial) (goto (fun _ => .inl (.inl (.inr .fill))))))
        (load (fun _ => initial) halt))

def cfg (l : Option Label) (s : Control) (candidate work saved : List Bool) : Config :=
  ⟨l, s, Sum.elim (innerCfg none s.1 candidate work).stk (fun _ => saved)⟩

def run (t : ℕ) (q : Config) := ((advance program)^[t]) q

private theorem run_add (t s : ℕ) (q : Config) : run (t + s) q = run t (run s q) :=
  Function.iterate_add_apply _ _ _ _

private theorem run_succ {c d : Config} (h : TM2.step program c = some d) (n : ℕ) :
    run (n + 1) c = run n d := by
  simp only [run, Function.iterate_succ_apply, advance, h, Option.getD_some]

private theorem step_scan_cons (s : Control) (b : Bool) (c work saved : List Bool) :
    TM2.step program (cfg (some (.inr .scan)) s (b :: c) work saved) =
      some (cfg (some (.inr .scan)) (s.1, some b) c work (false :: saved)) := by
  dsimp only [TM2.step, TM2.stepAux, program, cfg, innerCfg, SamplerMachineSearch.cfg, source,
    Sum.elim_inl, Sum.elim_inr]
  simp only [Function.update_self, List.head?_cons, List.tail_cons, Option.isSome_some,
    Bool.cond_true, Option.some.injEq]
  congr 1
  funext k
  rcases k with k | k
  · rcases k with k | k
    · by_cases h : k = SamplerMachineIrreducibility.source <;>
        simp only [Function.update_apply, Sum.elim_inl, Sum.inl.injEq, h, ↓reduceIte, reduceCtorEq]
    · rfl
  · rfl

private theorem step_scan_nil (s : Control) (work saved : List Bool) :
    TM2.step program (cfg (some (.inr .scan)) s [] work saved) =
      some (cfg (some (.inr .restore)) (s.1, none) [] work saved) := by
  dsimp only [TM2.step, TM2.stepAux, program, cfg, innerCfg, SamplerMachineSearch.cfg, source,
    Sum.elim_inl, Sum.elim_inr]
  simp only [Function.update_self, List.head?_nil, List.tail_nil, Option.isSome_none,
    Bool.cond_false, Option.some.injEq]
  congr 1
  funext k
  rcases k with k | k
  · rcases k with k | k
    · by_cases h : k = SamplerMachineIrreducibility.source <;>
        simp only [Function.update_apply, Sum.elim_inl, Sum.inl.injEq, h, ↓reduceIte, reduceCtorEq]
    · rfl
  · rfl

private theorem step_restore_cons (s : Control) (b : Bool) (c work saved : List Bool) :
    TM2.step program (cfg (some (.inr .restore)) s c work (b :: saved)) =
      some (cfg (some (.inr .restore)) (s.1, some b) (false :: c) work saved) := by
  dsimp only [TM2.step, TM2.stepAux, program, cfg, innerCfg, SamplerMachineSearch.cfg, source,
    Sum.elim_inl, Sum.elim_inr]
  simp only [List.head?_cons, List.tail_cons, Option.isSome_some,
    Bool.cond_true, Option.some.injEq]
  congr 1
  funext k
  rcases k with k | k
  · rcases k with k | k
    · by_cases h : k = SamplerMachineIrreducibility.source <;>
        simp only [Function.update_apply, Sum.elim_inl, Sum.inl.injEq, h, ↓reduceIte, reduceCtorEq]
    · rfl
  · rfl

private theorem step_restore_nil (s : Control) (c work : List Bool) :
    TM2.step program (cfg (some (.inr .restore)) s c work []) =
      some (cfg (some (.inr .check)) (s.1, none) c work []) := by
  dsimp only [TM2.step, TM2.stepAux, program, cfg, innerCfg, SamplerMachineSearch.cfg, source,
    Sum.elim_inl, Sum.elim_inr]
  simp only [List.head?_nil, List.tail_nil, Option.isSome_none,
    Bool.cond_false, Option.some.injEq]
  congr 1
  funext k
  rcases k with k | k <;> rfl

theorem scan_run (s : Control) (c work saved : List Bool) :
    run (c.length + 1) (cfg (some (.inr .scan)) s c work saved) =
      cfg (some (.inr .restore)) (s.1, none) [] work
        (List.replicate c.length false ++ saved) := by
  induction c generalizing s saved with
  | nil => simpa using run_succ (step_scan_nil s work saved) 0
  | cons b c ih =>
      rw [List.length_cons, run_succ (step_scan_cons s b c work saved)]
      simpa only [List.replicate_succ', List.append_assoc, List.singleton_append] using
        ih (s.1, some b) (false :: saved)

theorem restore_run (s : Control) (c work saved : List Bool) :
    run (saved.length + 1) (cfg (some (.inr .restore)) s c work saved) =
      cfg (some (.inr .check)) (s.1, none) (List.replicate saved.length false ++ c) work [] := by
  induction saved generalizing s c with
  | nil => simpa using run_succ (step_restore_nil s c work) 0
  | cons b saved ih =>
      rw [List.length_cons, run_succ (step_restore_cons s b c work saved)]
      simpa only [List.replicate_succ', List.append_assoc, List.singleton_append] using
        ih (s.1, some b) (false :: c)

theorem initialize_run (c : List Bool) :
    run (2 * c.length + 2) (cfg (some (.inr .scan)) initial c [] []) =
      cfg (some (.inr .check)) initial (List.replicate c.length false) [] [] := by
  have hs := scan_run initial c [] []
  have hr := restore_run initial [] [] (List.replicate c.length false)
  simp only [List.length_replicate, List.append_nil] at hs hr
  change run (c.length + 1) _ = cfg (some (.inr .restore)) initial [] []
    (List.replicate c.length false) at hs
  change run (c.length + 1) _ = cfg (some (.inr .check)) initial
    (List.replicate c.length false) [] [] at hr
  rw [show 2 * c.length + 2 = (c.length + 1) + (c.length + 1) by omega, run_add, hs, hr]

private theorem step_check_cons (b : Bool) (c : List Bool) :
    TM2.step program (cfg (some (.inr .check)) initial (b :: c) [] []) =
      some (cfg (some (.inl (.inl (.inr .fill)))) initial (b :: c) [] []) := by
  dsimp only [TM2.step, TM2.stepAux, program, cfg, innerCfg, SamplerMachineSearch.cfg, source,
    Sum.elim_inl, Sum.elim_inr]
  simp only [Function.update_self, List.head?_cons, List.tail_cons, Option.isSome_some,
    Option.getD_some, Bool.cond_true, Option.some.injEq]
  congr 1
  funext k
  rcases k with k | k
  · rcases k with k | k
    · by_cases h : k = SamplerMachineIrreducibility.source <;>
        simp only [Function.update_apply, Sum.elim_inl, Sum.inl.injEq, h, ↓reduceIte, reduceCtorEq]
    · rfl
  · rfl

theorem inner_cfg (l : Option InnerLabel) (s : InnerControl) (c work saved : List Bool) :
    liftCfg (none : Option Admin) (none : Option Bool) (fun _ : Unit => saved) (innerCfg l s c work) =
      cfg (l.map Sum.inl) (s, none) c work saved := by
  cases l <;> rfl

theorem search_call {n : ℕ} (hn : 0 < n) :
    ∃ (t : ℕ) (s : Control), t ≤ searchBound n ∧
      run t (cfg (some (.inl (.inl (.inr .fill)))) initial (List.replicate n false) [] []) =
        cfg none s (encodeWord (chosenWord n)) [] [] := by
  obtain ⟨t, s, ht, hr⟩ := search_run hn
  have hh : (((advance innerProgram)^[t])
      (innerCfg (some (.inl (.inr .fill))) innerInitial (List.replicate n false) [])).l = none := by
    rw [hr]; rfl
  obtain ⟨t', ht', hrun⟩ := BitMachineSubroutine.lift_outputs innerProgram program
    none (fun _ => rfl) (none : Option Bool) (fun _ : Unit => [])
    (innerCfg (some (.inl (.inr .fill))) innerInitial (List.replicate n false) []) t hh
  rw [hr, inner_cfg, inner_cfg] at hrun
  exact ⟨t', (s, none), ht'.trans ht, hrun⟩

def timeBound (n : ℕ) : ℕ := searchBound n + 2 * n + 3

/-- Complete exact computation, including arbitrary-input initialization and
the zero-degree edge case. Only the output candidate stack remains occupied. -/
theorem run_chosenWord (bits : List Bool) :
    ∃ (t : ℕ) (s : Control), t ≤ timeBound bits.length ∧
      run t (cfg (some (.inr .scan)) initial bits [] []) =
        cfg none s (encodeWord (chosenWord bits.length)) [] [] := by
  have hi := initialize_run bits
  by_cases hn : 0 < bits.length
  · obtain ⟨t, s, ht, hr⟩ := search_call hn
    have hc : run 1 (cfg (some (.inr .check)) initial (List.replicate bits.length false) [] []) =
        cfg (some (.inl (.inl (.inr .fill)))) initial (List.replicate bits.length false) [] [] := by
      cases hlen : bits.length with
      | zero => omega
      | succ n => simpa only [List.replicate_succ, run, Function.iterate_zero_apply] using
          run_succ (step_check_cons false (List.replicate n false)) 0
    refine ⟨t + (1 + (2 * bits.length + 2)), s, by unfold timeBound; omega, ?_⟩
    rw [run_add t (1 + (2 * bits.length + 2)), run_add 1 (2 * bits.length + 2), hi, hc, hr]
  · have hz : bits.length = 0 := by omega
    have hb : bits = [] := List.length_eq_zero_iff.mp hz
    subst bits
    refine ⟨3, initial, by simp [timeBound, searchBound], ?_⟩
    rw [show 3 = 1 + (2 * ([] : List Bool).length + 2) by rfl, run_add, hi]
    change run 1 (cfg (some (.inr .check)) initial [] [] []) = _
    have he : encodeWord (chosenWord 0) = [] := by simp [encodeWord]
    simp only [List.length_nil, he]
    simp only [run, Function.iterate_one, advance]
    dsimp only [TM2.step, TM2.stepAux, program,
      cfg, innerCfg, SamplerMachineSearch.cfg, source, Sum.elim_inl, Sum.elim_inr]
    try simp only [Function.update_self, List.head?_nil, List.tail_nil, Option.isSome_none,
      Bool.cond_false, Option.getD_some]
    congr 1
    funext k
    rcases k with k | k
    · rcases k with k | k
      · by_cases h : k = SamplerMachineIrreducibility.source <;>
          simp only [Function.update_apply, Sum.elim_inl, Sum.inl.injEq, h, ↓reduceIte]
      · rfl
    · rfl

noncomputable def bitMachine : BitMachine.Machine :=
  ofFinite source source (.inr .scan : Label) initial program

private theorem initial_eq (bits : List Bool) :
    rawInit source (.inr .scan : Label) initial bits =
      cfg (some (.inr .scan)) initial bits [] [] := by
  unfold rawInit cfg innerCfg SamplerMachineSearch.cfg source
  congr 1
  funext k
  rcases k with k | k
  · rcases k with k | k
    · by_cases h : k = SamplerMachineIrreducibility.source <;>
        simp only [Function.update_apply, Sum.elim_inl, Sum.inl.injEq, h, ↓reduceIte,
          SamplerMachineIrreducibility.inputBank]
    · rfl
  · rfl

/-- A single fixed finite Boolean-stack machine implements the exact selected
modulus for every input length. Its runtime is output-scale, not polynomial
in the field degree alone. -/
theorem bitMachine_outputs (bits : List Bool) :
    bitMachine.OutputsWithin bits (encodeWord (chosenWord bits.length)) (timeBound bits.length) := by
  obtain ⟨t, s, ht, hr⟩ := run_chosenWord bits
  apply outputsWithin_of_raw_run source source (.inr .scan : Label) initial program bits
    (encodeWord (chosenWord bits.length)) t (timeBound bits.length) ht
  · change (run t _).l = none
    rw [initial_eq, hr]
    rfl
  · change (run t _).stk source = _
    rw [initial_eq, hr]
    rfl

/-- Exhaustive search is polynomial in the field cardinality. This is not
a claim of polynomial time in the logarithmic degree encoding. -/
theorem timeBound_polynomial (n : ℕ) : timeBound n ≤ 128 * (2 ^ n) ^ 5 := by
  let q := 2 ^ n
  have hq : 1 ≤ q := by
    have hp : 0 < q := by dsimp [q]; positivity
    omega
  have hn : n ≤ q := Nat.lt_two_pow_self.le
  have hnn : n ^ 2 ≤ q ^ 2 := Nat.pow_le_pow_left hn 2
  have hqq : q ≤ q ^ 2 := by nlinarith
  have hq2 : 1 ≤ q ^ 2 := hq.trans hqq
  have hpoly : 16 * n ^ 2 + 44 * n + 36 ≤ 96 * q ^ 2 := by nlinarith
  have hmain : q ^ 3 * (16 * n ^ 2 + 44 * n + 36) ≤ 96 * q ^ 5 := by
    calc
      _ ≤ q ^ 3 * (96 * q ^ 2) := Nat.mul_le_mul_left _ hpoly
      _ = _ := by ring
  have hq5 : q ≤ q ^ 5 := by
    simpa only [pow_one] using Nat.pow_le_pow_right hq (by decide : 1 ≤ 5)
  have hq25 : q ^ 2 ≤ q ^ 5 := Nat.pow_le_pow_right hq (by decide : 2 ≤ 5)
  have hprod : q * n ≤ q ^ 5 := by
    calc
      _ ≤ q * q := Nat.mul_le_mul_left q hn
      _ = q ^ 2 := by ring
      _ ≤ q ^ 5 := hq25
  have hlast : 1 ≤ q ^ 5 := hq.trans hq5
  have hexpand : timeBound n =
      q ^ 3 * (16 * n ^ 2 + 44 * n + 36) + 8 * (q * n) + 9 * q + 2 * n + 3 := by
    dsimp [timeBound, searchBound, SamplerMachineIrreducibility.timeBound,
      SamplerMachineIrreducibility.innerBound, q]
    rw [show 2 * n = n * 2 by omega, pow_mul]
    ring
  change timeBound n ≤ 128 * q ^ 5
  rw [hexpand]
  omega

theorem bitMachine_outputs_polynomial (bits : List Bool) :
    bitMachine.OutputsWithin bits (encodeWord (chosenWord bits.length))
      (128 * (2 ^ bits.length) ^ 5) := by
  obtain ⟨t, s, ht, hr⟩ := run_chosenWord bits
  apply outputsWithin_of_raw_run source source (.inr .scan : Label) initial program bits
    (encodeWord (chosenWord bits.length)) t (128 * (2 ^ bits.length) ^ 5)
    (ht.trans (timeBound_polynomial _))
  · change (run t _).l = none
    rw [initial_eq, hr]
    rfl
  · change (run t _).stk source = _
    rw [initial_eq, hr]
    rfl

end EthInapproximability.CurrentPaper.SamplerMachineChosenWord
