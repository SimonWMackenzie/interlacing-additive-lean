import EthInapproximability.CurrentPaper.SamplerMachineTraceBit
import EthInapproximability.CurrentPaper.BitMachineSubroutineRenaming

/-!
# Computing one exact sampler coordinate

Source: locked v8 Appendix E, `lem:exact-families`. Starting with the
two seed words, selected modulus, and a unary coordinate index, repeated
multiplication directly forms `x*y^i`: the accumulator starts at `x`, not
at one. A final trace computation returns the exact sampler bit. All input
seed and loop words are consumed, the modulus is preserved, and every
scratch stack is empty on return. The supplied unary index is counted in
the runtime and is not stored in finite control.
-/

namespace EthInapproximability.CurrentPaper.SamplerMachineCoordinate

open Turing Turing.TM2.Stmt BitMachineEncoding BitMachineComposition
open ExecutableSmallBiasSampler SamplerMachine

inductive Admin where
  | clear
  deriving DecidableEq, Fintype

abbrev Stack := SamplerMachinePower.Stack ⊕ Unit
abbrev Label := SamplerMachinePower.Label ⊕ (SamplerMachineTraceBit.Label ⊕ Admin)
abbrev Control := SamplerMachinePower.Control × SamplerMachineTraceBit.Control
abbrev Config := TM2.Cfg (fun _ : Stack => Bool) Label Control

def initial : Control := (SamplerMachinePower.initial, SamplerMachineTraceBit.initial)
def result (s : Control) : Bool := SamplerMachineTraceBit.result s.2

def traceStack : (SamplerMachineTraceBit.Stack ⊕ Fin 0) ≃ Stack where
  toFun := Sum.elim (Sum.elim (Sum.elim
    (fun k => .inl (.inl k))
    (fun i => if i = 0 then .inl (.inr ()) else .inr ())) Fin.elim0) Fin.elim0
  invFun := Sum.elim (Sum.elim
    (fun k => .inl (.inl (.inl k)))
    (fun _ => .inl (.inl (.inr 0))))
    (fun _ => .inl (.inl (.inr 1)))
  left_inv := by
    intro k
    rcases k with ((k | k) | k) | k
    · rfl
    · fin_cases k <;> rfl
    · exact Fin.elim0 k
    · exact Fin.elim0 k
  right_inv := by
    intro k
    rcases k with (k | k) | k <;> rfl

def traceLabel : (SamplerMachineTraceBit.Label ⊕ (SamplerMachinePower.Label ⊕ Admin)) ≃ Label where
  toFun := Sum.elim (fun l => .inr (.inl l)) (Sum.elim Sum.inl (fun l => .inr (.inr l)))
  invFun := Sum.elim (fun l => .inr (.inl l)) (Sum.elim Sum.inl (fun l => .inr (.inr l)))
  left_inv := by intro l; rcases l with l | (l | l) <;> rfl
  right_inv := by intro l; rcases l with l | (l | l) <;> rfl

def traceControl : (SamplerMachineTraceBit.Control × SamplerMachinePower.Control) ≃ Control :=
  Equiv.prodComm _ _

def program : Label → TM2.Stmt (fun _ : Stack => Bool) Label Control
  | .inl l => liftStmt (some (.inr .clear)) (SamplerMachinePower.program l)
  | .inr (.inl l) => renameStmt traceStack traceLabel traceControl
      (liftStmt none (SamplerMachineTraceBit.program l))
  | .inr (.inr .clear) => pop (.inl (.inl (.inl 1)))
      (fun s b => (s.1, s.2.1, s.2.2.1, b))
      (branch (fun s => s.2.2.2.isSome)
        (goto (fun _ => .inr (.inr .clear)))
        (load (fun s => (s.1, SamplerMachineTraceBit.initial))
          (goto (fun _ => .inr (.inl (.inr .fill))))))

def cfg (l : Option Label) (s : Control)
    (a u c fuel extra : List Bool) : Config :=
  ⟨l, s, Sum.elim (SamplerMachinePower.cfg none s.1 a u [] [] c [] fuel).stk (fun _ => extra)⟩

def run (t : ℕ) (q : Config) := ((advance program)^[t]) q

private theorem run_add (t s : ℕ) (q : Config) : run (t + s) q = run t (run s q) :=
  Function.iterate_add_apply _ _ _ _

private theorem run_succ {c d : Config} (h : TM2.step program c = some d) (n : ℕ) :
    run (n + 1) c = run n d := by
  simp only [run, Function.iterate_succ_apply, advance, h, Option.getD_some]

theorem iterate_seed_product (n : ℕ) (x y : BinaryWord n) (k : ℕ) :
    ((wordMul n y)^[k]) x = wordMul n x (wordPow n y k) := by
  by_cases hn : 0 < n
  · have he (j : ℕ) : wordEval n (((wordMul n y)^[j]) x) =
        wordEval n y ^ j * wordEval n x := by
      induction j with
      | zero => simp
      | succ j ih =>
          rw [Function.iterate_succ_apply', wordEval_mul, ih, pow_succ]
          ring
    apply (wordEval_bijective n).injective
    rw [he, wordEval_mul, wordEval_pow hn]
    ring
  · have hz : n = 0 := by omega
    subst n
    funext i
    exact Fin.elim0 i

theorem power_cfg (l : Option SamplerMachinePower.Label) (s : SamplerMachinePower.Control)
    (a u c fuel extra : List Bool) :
    liftCfg (some (.inr .clear)) SamplerMachineTraceBit.initial (fun _ : Unit => extra)
      (SamplerMachinePower.cfg l s a u [] [] c [] fuel) =
      cfg (match l with | none => some (.inr (.inr .clear)) | some l => some (.inl l))
        (s, SamplerMachineTraceBit.initial) a u c fuel extra := by cases l <;> rfl

def powerTime (n i : ℕ) : ℕ := i * (n * (4 * n + 5) + 2 * n + 4) + 1

theorem power_call (n : ℕ) (x y : BinaryWord n) (fuel : List Bool) :
    ∃ t ≤ powerTime n fuel.length,
      run t (cfg (some (.inl (.inr .loop))) initial (encodeWord x) (encodeWord y)
        (encodeWord (chosenWord n)) fuel []) =
      cfg (some (.inr (.inr .clear))) initial
        (encodeWord (wordMul n x (wordPow n y fuel.length))) (encodeWord y)
        (encodeWord (chosenWord n)) [] [] := by
  obtain ⟨t, ht, hr⟩ := SamplerMachinePower.run_multiply_iterate SamplerMachinePower.initial y x fuel
  have hh : (SamplerMachinePower.run t
      (SamplerMachinePower.cfg (some (.inr .loop)) SamplerMachinePower.initial
        (encodeWord x) (encodeWord y) [] [] (encodeWord (chosenWord n)) [] fuel)).l = none := by
    rw [hr]; rfl
  obtain ⟨t', ht', hrun⟩ := BitMachineSubroutine.lift_outputs SamplerMachinePower.program program
    (some (.inr .clear)) (fun _ => rfl) SamplerMachineTraceBit.initial (fun _ : Unit => [])
    (SamplerMachinePower.cfg (some (.inr .loop)) SamplerMachinePower.initial
      (encodeWord x) (encodeWord y) [] [] (encodeWord (chosenWord n)) [] fuel) t hh
  dsimp only [SamplerMachinePower.run] at hr
  rw [hr, power_cfg, power_cfg, iterate_seed_product] at hrun
  exact ⟨t', ht'.trans ht, hrun⟩

private theorem step_clear_cons (s : Control) (b : Bool) (a u c fuel extra : List Bool) :
    TM2.step program (cfg (some (.inr (.inr .clear))) s a (b :: u) c fuel extra) =
      some (cfg (some (.inr (.inr .clear))) (s.1, s.2.1, s.2.2.1, some b) a u c fuel extra) := by
  dsimp only [TM2.step, TM2.stepAux, program, cfg, SamplerMachinePower.cfg,
    SamplerMachineProduct.cfg, SamplerMachineProduct.foreign,
    SamplerMachineAccumulate.stackContents, Sum.elim_inl, Sum.elim_inr]
  simp only [show (1 : Fin 4) ≠ 0 by decide, ↓reduceIte, List.head?_cons, List.tail_cons,
    Option.isSome_some, Bool.cond_true, Option.some.injEq]
  congr 1
  funext k
  rcases k with ((k | k) | k) | k <;> (try fin_cases k) <;> rfl

private theorem step_clear_nil (s : Control) (a c fuel extra : List Bool) :
    TM2.step program (cfg (some (.inr (.inr .clear))) s a [] c fuel extra) =
      some (cfg (some (.inr (.inl (.inr .fill))))
        (s.1, SamplerMachineTraceBit.initial) a [] c fuel extra) := by
  dsimp only [TM2.step, TM2.stepAux, program, cfg, SamplerMachinePower.cfg,
    SamplerMachineProduct.cfg, SamplerMachineProduct.foreign,
    SamplerMachineAccumulate.stackContents, Sum.elim_inl, Sum.elim_inr]
  simp only [show (1 : Fin 4) ≠ 0 by decide, ↓reduceIte, List.head?_nil, List.tail_nil,
    Option.isSome_none, Bool.cond_false, Option.some.injEq]
  congr 1
  funext k
  rcases k with ((k | k) | k) | k <;> (try fin_cases k) <;> rfl

theorem clear_run (s : Control) (a u c fuel extra : List Bool) :
    run (u.length + 1) (cfg (some (.inr (.inr .clear))) s a u c fuel extra) =
      cfg (some (.inr (.inl (.inr .fill)))) (s.1, SamplerMachineTraceBit.initial) a [] c fuel extra := by
  induction u generalizing s with
  | nil => simpa using run_succ (step_clear_nil s a c fuel extra) 0
  | cons b u ih =>
      rw [List.length_cons, run_succ (step_clear_cons s b a u c fuel extra)]
      exact ih (s.1, s.2.1, s.2.2.1, some b)

theorem trace_cfg (l : Option SamplerMachineTraceBit.Label) (s : SamplerMachineTraceBit.Control)
    (a c : List Bool) :
    renameCfg traceStack traceLabel traceControl
      (liftCfg (none : Option (SamplerMachinePower.Label ⊕ Admin)) SamplerMachinePower.initial
        Fin.elim0 (SamplerMachineTraceBit.cfg l s a [] c [] [])) =
      cfg (l.map (fun l => .inr (.inl l))) (SamplerMachinePower.initial, s) a [] c [] [] := by
  cases l <;> unfold renameCfg liftCfg cfg traceStack traceLabel traceControl
    SamplerMachineTraceBit.cfg SamplerMachineTrace.cfg SamplerMachinePower.cfg
  all_goals
    congr 1
    funext k
    rcases k with (k | k) | k
    · rfl
    · rfl
    · rfl

theorem trace_call (n : ℕ) (u : BinaryWord n) :
    ∃ t ≤ SamplerMachineTraceBit.timeBound n,
      run t (cfg (some (.inr (.inl (.inr .fill)))) initial
        (encodeWord u) [] (encodeWord (chosenWord n)) [] []) =
      cfg none (SamplerMachinePower.initial,
        SamplerMachineTrace.initial, encodeBit (traceBit n u), none)
        [] [] (encodeWord (chosenWord n)) [] [] := by
  obtain ⟨t, ht, hr⟩ := SamplerMachineTraceBit.run_traceBit n u
  have hh : (SamplerMachineTraceBit.run t
      (SamplerMachineTraceBit.cfg (some (.inr .fill)) SamplerMachineTraceBit.initial
        (encodeWord u) [] (encodeWord (chosenWord n)) [] [])).l = none := by rw [hr]; rfl
  obtain ⟨t', ht', hrun⟩ := BitMachineSubroutineRenaming.lift_outputs_renamed
    traceStack traceLabel traceControl SamplerMachineTraceBit.program program
    none (fun _ => rfl) SamplerMachinePower.initial Fin.elim0
    (SamplerMachineTraceBit.cfg (some (.inr .fill)) SamplerMachineTraceBit.initial
      (encodeWord u) [] (encodeWord (chosenWord n)) [] []) t hh
  dsimp only [SamplerMachineTraceBit.run] at hr
  rw [hr, trace_cfg, trace_cfg] at hrun
  exact ⟨t', ht'.trans ht, hrun⟩

def timeBound (n i : ℕ) : ℕ := powerTime n i + n + 1 + SamplerMachineTraceBit.timeBound n

/-- Exact disposable-seed coordinate evaluation, with every arithmetic,
loop preparation, trace, and cleanup transition charged. -/
theorem run_coordinate (n : ℕ) (x y : BinaryWord n) (fuel : List Bool) :
    ∃ t ≤ timeBound n fuel.length,
      run t (cfg (some (.inl (.inr .loop))) initial
        (encodeWord x) (encodeWord y) (encodeWord (chosenWord n)) fuel []) =
      cfg none (SamplerMachinePower.initial, SamplerMachineTrace.initial,
        encodeBit (traceBit n (wordMul n x (wordPow n y fuel.length))), none)
        [] [] (encodeWord (chosenWord n)) [] [] := by
  obtain ⟨tp, htp, hp⟩ := power_call n x y fuel
  have hc := clear_run initial (encodeWord (wordMul n x (wordPow n y fuel.length)))
    (encodeWord y) (encodeWord (chosenWord n)) [] []
  simp only [encodeWord_length] at hc
  change run (n + 1) _ = cfg (some (.inr (.inl (.inr .fill)))) initial
    (encodeWord (wordMul n x (wordPow n y fuel.length))) []
    (encodeWord (chosenWord n)) [] [] at hc
  obtain ⟨tt, htt, ht⟩ := trace_call n (wordMul n x (wordPow n y fuel.length))
  refine ⟨tt + ((n + 1) + tp), by unfold timeBound; omega, ?_⟩
  rw [run_add tt ((n + 1) + tp), run_add (n + 1) tp, hp, hc, ht]

theorem timeBound_polynomial (n i : ℕ) :
    timeBound n i ≤ 32 * (i + 1) * (n + 1) ^ 3 := by
  have hp : n * (4 * n + 5) + 2 * n + 4 ≤ 16 * (n + 1) ^ 3 := by
    nlinarith [Nat.zero_le (n ^ 3)]
  have hc : n + 2 ≤ 2 * (n + 1) ^ 3 := by nlinarith [Nat.zero_le (n ^ 3)]
  have ht := SamplerMachineTraceBit.timeBound_polynomial n
  have hm := Nat.mul_le_mul_left i hp
  unfold timeBound powerTime
  nlinarith

/-- The returned bit agrees with the existing executable sampler coordinate,
including its exact seed words and zero-based coordinate convention. -/
theorem run_executableTraceBits (n L : ℕ) (seed : BinaryWord n × BinaryWord n) (i : Fin L) :
    ∃ t ≤ 32 * (i.val + 1) * (n + 1) ^ 3,
      run t (cfg (some (.inl (.inr .loop))) initial (encodeWord seed.1)
        (encodeWord seed.2) (encodeWord (chosenWord n)) (List.replicate i.val true) []) =
      cfg none (SamplerMachinePower.initial, SamplerMachineTrace.initial,
        encodeBit (executableTraceBits n L seed i), none)
        [] [] (encodeWord (chosenWord n)) [] [] := by
  obtain ⟨t, ht, hr⟩ := run_coordinate n seed.1 seed.2 (List.replicate i.val true)
  simp only [List.length_replicate] at ht hr
  exact ⟨t, ht.trans (timeBound_polynomial n i.val), hr⟩

end EthInapproximability.CurrentPaper.SamplerMachineCoordinate
