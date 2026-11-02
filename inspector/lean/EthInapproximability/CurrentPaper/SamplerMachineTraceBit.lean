import EthInapproximability.CurrentPaper.SamplerMachineTrace

/-!
# Computing one trace bit with initialization and cleanup

Source: locked v8 Appendix E, `lem:exact-families`. The input word and
selected modulus are stored as coefficient lists. Actual scans construct
the zero accumulator and unary loop counter. The verified trace controller
is then called, its first coefficient is read into finite control, and all
temporary words are cleared. The modulus is preserved. The input word is
disposable, as needed after multiplication in the coordinate evaluator.
-/

namespace EthInapproximability.CurrentPaper.SamplerMachineTraceBit

open Turing Turing.TM2.Stmt BitMachineEncoding BitMachineComposition
open ExecutableSmallBiasSampler SamplerMachine

inductive Admin where
  | fill | restore | extract | clearSum | clearPower
  deriving DecidableEq, Fintype

abbrev Stack := SamplerMachineTrace.Stack ⊕ Fin 0
abbrev Label := SamplerMachineTrace.Label ⊕ Admin
abbrev Control := SamplerMachineTrace.Control × (Bool × Option Bool)
abbrev Config := TM2.Cfg (fun _ : Stack => Bool) Label Control

def initial : Control := (SamplerMachineTrace.initial, false, none)
def source : Stack := .inl (.inl (.inl 0))
def saved : Stack := .inl (.inl (.inl 1))
def modulus : Stack := .inl (.inl (.inr 0))
def sumStack : Stack := .inl (.inr 0)
def fuelStack : Stack := .inl (.inr 1)

def program : Label → TM2.Stmt (fun _ : Stack => Bool) Label Control
  | .inl l => liftStmt (some .extract) (SamplerMachineTrace.program l)
  | .inr .fill => pop source (fun s b => (s.1, s.2.1, b))
      (branch (fun s => s.2.2.isSome)
        (push saved (fun s => s.2.2.getD false)
          (push sumStack (fun _ => false) (push fuelStack (fun _ => true)
            (goto (fun _ => .inr .fill)))))
        (goto (fun _ => .inr .restore)))
  | .inr .restore => pop saved (fun s b => (s.1, s.2.1, b))
      (branch (fun s => s.2.2.isSome)
        (push source (fun s => s.2.2.getD false) (goto (fun _ => .inr .restore)))
        (load (fun _ => initial) (goto (fun _ => .inl (.inr .loop)))))
  | .inr .extract => pop sumStack (fun s b => (s.1, b.getD false, none))
      (goto (fun _ => .inr .clearSum))
  | .inr .clearSum => pop sumStack (fun s b => (s.1, s.2.1, b))
      (branch (fun s => s.2.2.isSome)
        (goto (fun _ => .inr .clearSum))
        (goto (fun _ => .inr .clearPower)))
  | .inr .clearPower => pop source (fun s b => (s.1, s.2.1, b))
      (branch (fun s => s.2.2.isSome)
        (goto (fun _ => .inr .clearPower))
        (load (fun s => (s.1, s.2.1, none)) halt))

def cfg (l : Option Label) (s : Control) (a work c sum fuel : List Bool) : Config :=
  ⟨l, s, Sum.elim (SamplerMachineTrace.cfg none s.1 a work [] [] c [] sum fuel).stk
    Fin.elim0⟩

def run (t : ℕ) (q : Config) := ((advance program)^[t]) q
def result (s : Control) : Bool := s.2.1

private theorem run_add (t s : ℕ) (q : Config) : run (t + s) q = run t (run s q) :=
  Function.iterate_add_apply _ _ _ _

private theorem run_succ {c d : Config} (h : TM2.step program c = some d) (t : ℕ) :
    run (t + 1) c = run t d := by
  simp only [run, Function.iterate_succ_apply, advance, h, Option.getD_some]

private theorem step_fill_cons (s : Control) (b : Bool) (a work c sum fuel : List Bool) :
    TM2.step program (cfg (some (.inr .fill)) s (b :: a) work c sum fuel) =
      some (cfg (some (.inr .fill)) (s.1, s.2.1, some b) a (b :: work) c
        (false :: sum) (true :: fuel)) := by
  dsimp only [TM2.step, TM2.stepAux, program, cfg, source, saved, sumStack, fuelStack,
    SamplerMachineTrace.cfg, SamplerMachineProduct.cfg, SamplerMachineProduct.foreign,
    SamplerMachineAccumulate.stackContents, Sum.elim_inl, Sum.elim_inr]
  simp only [↓reduceIte, List.head?_cons, List.tail_cons, Option.isSome_some,
    Option.getD_some, Bool.cond_true, Option.some.injEq]
  congr 1
  funext k
  rcases k with ((k | k) | k) | k <;> fin_cases k <;> rfl

private theorem step_fill_nil (s : Control) (work c sum fuel : List Bool) :
    TM2.step program (cfg (some (.inr .fill)) s [] work c sum fuel) =
      some (cfg (some (.inr .restore)) (s.1, s.2.1, none) [] work c sum fuel) := by
  dsimp only [TM2.step, TM2.stepAux, program, cfg, source,
    SamplerMachineTrace.cfg, SamplerMachineProduct.cfg, SamplerMachineProduct.foreign,
    SamplerMachineAccumulate.stackContents, Sum.elim_inl, Sum.elim_inr]
  simp only [↓reduceIte, List.head?_nil, List.tail_nil, Option.isSome_none,
    Bool.cond_false, Option.some.injEq]
  congr 1
  funext k
  rcases k with ((k | k) | k) | k <;> fin_cases k <;> rfl

private theorem step_restore_cons (s : Control) (b : Bool) (a work c sum fuel : List Bool) :
    TM2.step program (cfg (some (.inr .restore)) s a (b :: work) c sum fuel) =
      some (cfg (some (.inr .restore)) (s.1, s.2.1, some b) (b :: a) work c sum fuel) := by
  dsimp only [TM2.step, TM2.stepAux, program, cfg, source, saved,
    SamplerMachineTrace.cfg, SamplerMachineProduct.cfg, SamplerMachineProduct.foreign,
    SamplerMachineAccumulate.stackContents, Sum.elim_inl, Sum.elim_inr]
  simp only [show (1 : Fin 4) ≠ 0 by decide, ↓reduceIte, List.head?_cons, List.tail_cons,
    Option.isSome_some, Option.getD_some, Bool.cond_true, Option.some.injEq]
  congr 1
  funext k
  rcases k with ((k | k) | k) | k <;> fin_cases k <;> rfl

private theorem step_restore_nil (s : Control) (a c sum fuel : List Bool) :
    TM2.step program (cfg (some (.inr .restore)) s a [] c sum fuel) =
      some (cfg (some (.inl (.inr .loop))) initial a [] c sum fuel) := by
  dsimp only [TM2.step, TM2.stepAux, program, cfg, saved,
    SamplerMachineTrace.cfg, SamplerMachineProduct.cfg, SamplerMachineProduct.foreign,
    SamplerMachineAccumulate.stackContents, Sum.elim_inl, Sum.elim_inr]
  simp only [show (1 : Fin 4) ≠ 0 by decide, ↓reduceIte, List.head?_nil, List.tail_nil,
    Option.isSome_none, Bool.cond_false, Option.some.injEq]
  congr 1
  funext k
  rcases k with ((k | k) | k) | k <;> fin_cases k <;> rfl

private theorem step_extract (s : Control) (a work c sum fuel : List Bool) :
    TM2.step program (cfg (some (.inr .extract)) s a work c sum fuel) =
      some (cfg (some (.inr .clearSum)) (s.1, sum.head?.getD false, none)
        a work c sum.tail fuel) := by
  dsimp only [TM2.step, TM2.stepAux, program, cfg, sumStack,
    SamplerMachineTrace.cfg, SamplerMachineProduct.cfg, SamplerMachineProduct.foreign,
    SamplerMachineAccumulate.stackContents, Sum.elim_inl, Sum.elim_inr]
  simp only [↓reduceIte, Option.some.injEq]
  congr 1
  funext k
  rcases k with ((k | k) | k) | k <;> fin_cases k <;> rfl

private theorem step_clearSum_cons (s : Control) (b : Bool) (a work c sum fuel : List Bool) :
    TM2.step program (cfg (some (.inr .clearSum)) s a work c (b :: sum) fuel) =
      some (cfg (some (.inr .clearSum)) (s.1, s.2.1, some b) a work c sum fuel) := by
  dsimp only [TM2.step, TM2.stepAux, program, cfg, sumStack,
    SamplerMachineTrace.cfg, SamplerMachineProduct.cfg, SamplerMachineProduct.foreign,
    SamplerMachineAccumulate.stackContents, Sum.elim_inl, Sum.elim_inr]
  simp only [↓reduceIte, List.head?_cons, List.tail_cons, Option.isSome_some,
    Bool.cond_true, Option.some.injEq]
  congr 1
  funext k
  rcases k with ((k | k) | k) | k <;> fin_cases k <;> rfl

private theorem step_clearSum_nil (s : Control) (a work c fuel : List Bool) :
    TM2.step program (cfg (some (.inr .clearSum)) s a work c [] fuel) =
      some (cfg (some (.inr .clearPower)) (s.1, s.2.1, none) a work c [] fuel) := by
  dsimp only [TM2.step, TM2.stepAux, program, cfg, sumStack,
    SamplerMachineTrace.cfg, SamplerMachineProduct.cfg, SamplerMachineProduct.foreign,
    SamplerMachineAccumulate.stackContents, Sum.elim_inl, Sum.elim_inr]
  simp only [↓reduceIte, List.head?_nil, List.tail_nil, Option.isSome_none,
    Bool.cond_false, Option.some.injEq]
  congr 1
  funext k
  rcases k with ((k | k) | k) | k <;> fin_cases k <;> rfl

private theorem step_clearPower_cons (s : Control) (b : Bool) (a work c sum fuel : List Bool) :
    TM2.step program (cfg (some (.inr .clearPower)) s (b :: a) work c sum fuel) =
      some (cfg (some (.inr .clearPower)) (s.1, s.2.1, some b) a work c sum fuel) := by
  dsimp only [TM2.step, TM2.stepAux, program, cfg, source,
    SamplerMachineTrace.cfg, SamplerMachineProduct.cfg, SamplerMachineProduct.foreign,
    SamplerMachineAccumulate.stackContents, Sum.elim_inl, Sum.elim_inr]
  simp only [↓reduceIte, List.head?_cons, List.tail_cons, Option.isSome_some,
    Bool.cond_true, Option.some.injEq]
  congr 1
  funext k
  rcases k with ((k | k) | k) | k <;> fin_cases k <;> rfl

private theorem step_clearPower_nil (s : Control) (work c sum fuel : List Bool) :
    TM2.step program (cfg (some (.inr .clearPower)) s [] work c sum fuel) =
      some (cfg none (s.1, s.2.1, none) [] work c sum fuel) := by
  dsimp only [TM2.step, TM2.stepAux, program, cfg, source,
    SamplerMachineTrace.cfg, SamplerMachineProduct.cfg, SamplerMachineProduct.foreign,
    SamplerMachineAccumulate.stackContents, Sum.elim_inl, Sum.elim_inr]
  simp only [↓reduceIte, List.head?_nil, List.tail_nil, Option.isSome_none,
    Bool.cond_false, Option.some.injEq]
  congr 1
  funext k
  rcases k with ((k | k) | k) | k <;> fin_cases k <;> rfl

theorem fill_run (s : Control) (a work c sum fuel : List Bool) :
    run (a.length + 1) (cfg (some (.inr .fill)) s a work c sum fuel) =
      cfg (some (.inr .restore)) (s.1, s.2.1, none) [] (a.reverse ++ work) c
        (List.replicate a.length false ++ sum) (List.replicate a.length true ++ fuel) := by
  induction a generalizing s work sum fuel with
  | nil => simpa using run_succ (step_fill_nil s work c sum fuel) 0
  | cons b a ih =>
      rw [List.length_cons, run_succ (step_fill_cons s b a work c sum fuel)]
      simpa only [List.length_cons, List.reverse_cons, List.replicate_succ',
        List.append_assoc, List.singleton_append] using
        ih (s.1, s.2.1, some b) (b :: work) (false :: sum) (true :: fuel)

theorem restore_run (s : Control) (a work c sum fuel : List Bool) :
    run (work.length + 1) (cfg (some (.inr .restore)) s a work c sum fuel) =
      cfg (some (.inl (.inr .loop))) initial (work.reverse ++ a) [] c sum fuel := by
  induction work generalizing s a with
  | nil => simpa using run_succ (step_restore_nil s a c sum fuel) 0
  | cons b work ih =>
      rw [List.length_cons, run_succ (step_restore_cons s b a work c sum fuel)]
      simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using
        ih (s.1, s.2.1, some b) (b :: a)

theorem prepare_run (a c : List Bool) :
    run (2 * a.length + 2) (cfg (some (.inr .fill)) initial a [] c [] []) =
      cfg (some (.inl (.inr .loop))) initial a [] c
        (List.replicate a.length false) (List.replicate a.length true) := by
  have hf := fill_run initial a [] c [] []
  simp only [List.append_nil] at hf
  have hr := restore_run (initial.1, initial.2.1, none) [] a.reverse c
    (List.replicate a.length false) (List.replicate a.length true)
  simp only [List.length_reverse, List.reverse_reverse, List.append_nil] at hr
  rw [show 2 * a.length + 2 = (a.length + 1) + (a.length + 1) by omega, run_add, hf, hr]

theorem clearSum_run (s : Control) (a work c sum fuel : List Bool) :
    run (sum.length + 1) (cfg (some (.inr .clearSum)) s a work c sum fuel) =
      cfg (some (.inr .clearPower)) (s.1, s.2.1, none) a work c [] fuel := by
  induction sum generalizing s with
  | nil => simpa using run_succ (step_clearSum_nil s a work c fuel) 0
  | cons b sum ih =>
      rw [List.length_cons, run_succ (step_clearSum_cons s b a work c sum fuel)]
      exact ih (s.1, s.2.1, some b)

theorem clearPower_run (s : Control) (a work c sum fuel : List Bool) :
    run (a.length + 1) (cfg (some (.inr .clearPower)) s a work c sum fuel) =
      cfg none (s.1, s.2.1, none) [] work c sum fuel := by
  induction a generalizing s with
  | nil => simpa using run_succ (step_clearPower_nil s work c sum fuel) 0
  | cons b a ih =>
      rw [List.length_cons, run_succ (step_clearPower_cons s b a work c sum fuel)]
      exact ih (s.1, s.2.1, some b)

theorem extract_run (s : Control) (a c sum : List Bool) :
    run (a.length + sum.tail.length + 3) (cfg (some (.inr .extract)) s a [] c sum []) =
      cfg none (s.1, sum.head?.getD false, none) [] [] c [] [] := by
  rw [show a.length + sum.tail.length + 3 =
    ((a.length + 1) + (sum.tail.length + 1)) + 1 by omega,
    run_succ (step_extract s a [] c sum []), run_add,
    clearSum_run, clearPower_run]

theorem trace_cfg (l : Option SamplerMachineTrace.Label)
    (s : SamplerMachineTrace.Control) (a c sum fuel : List Bool) :
    liftCfg (some .extract) (false, (none : Option Bool)) Fin.elim0
      (SamplerMachineTrace.cfg l s a [] [] [] c [] sum fuel) =
      cfg (match l with | none => some (.inr .extract) | some l => some (.inl l))
        (s, false, none) a [] c sum fuel := by cases l <;> rfl

def traceTime (n : ℕ) : ℕ := n * (n * (4 * n + 5) + 5 * n + 7) + 1

theorem trace_call {n : ℕ} (hn : 0 < n) (u : BinaryWord n) :
    ∃ t ≤ traceTime n,
      run t (cfg (some (.inl (.inr .loop))) initial (encodeWord u) []
        (encodeWord (chosenWord n)) (List.replicate n false) (List.replicate n true)) =
      cfg (some (.inr .extract)) initial
        (encodeWord (((SamplerMachineTrace.frobeniusStep n)^[n]) (u, 0)).1) []
        (encodeWord (chosenWord n)) (encodeWord (wordFrobeniusSum n u)) [] := by
  obtain ⟨t, ht, hr⟩ := SamplerMachineTrace.run_frobeniusSum hn u
  have hh : (SamplerMachineTrace.run t
      (SamplerMachineTrace.cfg (some (.inr .loop)) SamplerMachineTrace.initial
        (encodeWord u) [] [] [] (encodeWord (chosenWord n)) []
        (encodeWord (0 : BinaryWord n)) (List.replicate n true))).l = none := by rw [hr]; rfl
  obtain ⟨t', ht', hrun⟩ := BitMachineSubroutine.lift_outputs SamplerMachineTrace.program
    program (some .extract) (fun _ => rfl) (false, (none : Option Bool)) Fin.elim0
    (SamplerMachineTrace.cfg (some (.inr .loop)) SamplerMachineTrace.initial
      (encodeWord u) [] [] [] (encodeWord (chosenWord n)) []
      (encodeWord (0 : BinaryWord n)) (List.replicate n true)) t hh
  dsimp only [SamplerMachineTrace.run] at hr
  rw [hr, trace_cfg, trace_cfg] at hrun
  refine ⟨t', ht'.trans ht, ?_⟩
  have hz : encodeWord (0 : BinaryWord n) = List.replicate n false :=
    SamplerMachinePower.encodeWord_zero n
  rw [hz] at hrun
  exact hrun

def timeBound (n : ℕ) : ℕ := traceTime n + 4 * n + 5

theorem run_traceBit_pos {n : ℕ} (hn : 0 < n) (u : BinaryWord n) :
    ∃ t ≤ timeBound n,
      run t (cfg (some (.inr .fill)) initial (encodeWord u) []
        (encodeWord (chosenWord n)) [] []) =
      cfg none (SamplerMachineTrace.initial, encodeBit (traceBit n u), none)
        [] [] (encodeWord (chosenWord n)) [] [] := by
  have hp := prepare_run (encodeWord u) (encodeWord (chosenWord n))
  simp only [encodeWord_length] at hp
  obtain ⟨t, ht, hr⟩ := trace_call hn u
  have hc := extract_run initial
    (encodeWord (((SamplerMachineTrace.frobeniusStep n)^[n]) (u, 0)).1)
    (encodeWord (chosenWord n)) (encodeWord (wordFrobeniusSum n u))
  simp only [encodeWord_length, List.length_tail, SamplerMachineTrace.head_trace_word] at hc
  refine ⟨(n + (n - 1) + 3) + (t + (2 * n + 2)), ?_, ?_⟩
  · unfold timeBound
    omega
  · rw [run_add (n + (n - 1) + 3) (t + (2 * n + 2)), run_add t (2 * n + 2), hp, hr, hc]
    rfl

private theorem step_trace_empty :
    TM2.step program (cfg (some (.inl (.inr .loop))) initial [] [] [] [] []) =
      some (cfg (some (.inr .extract)) initial [] [] [] [] []) := by
  dsimp only [TM2.step, TM2.stepAux, program, cfg, initial, liftStmt,
    SamplerMachineTrace.program, SamplerMachineTrace.cfg, SamplerMachineProduct.cfg,
    SamplerMachineProduct.foreign, SamplerMachineAccumulate.stackContents,
    Sum.elim_inl, Sum.elim_inr]
  simp only [show (1 : Fin 2) ≠ 0 by decide, ↓reduceIte, List.head?_nil, List.tail_nil,
    Option.isSome_none, Bool.cond_false, Option.some.injEq]
  congr 1
  funext k
  rcases k with ((k | k) | k) | k <;> fin_cases k <;> rfl

theorem run_traceBit_zero (u : BinaryWord 0) :
    run 6 (cfg (some (.inr .fill)) initial (encodeWord u) []
      (encodeWord (chosenWord 0)) [] []) =
      cfg none (SamplerMachineTrace.initial, encodeBit (traceBit 0 u), none)
        [] [] (encodeWord (chosenWord 0)) [] [] := by
  have hp := prepare_run [] []
  have ht := run_succ step_trace_empty 0
  have hc := extract_run initial [] [] []
  simp only [List.length_nil, List.tail_nil, List.head?_nil, Option.getD_none,
    List.replicate_zero, Nat.mul_zero, Nat.zero_add] at hp ht hc
  have hpre : run 3 (cfg (some (.inr .fill)) initial [] [] [] [] []) =
      cfg (some (.inr .extract)) initial [] [] [] [] [] := by
    rw [show (3 : ℕ) = 1 + 2 by omega, run_add, hp, ht]
    rfl
  have hr : run 6 (cfg (some (.inr .fill)) initial [] [] [] [] []) =
      cfg none initial [] [] [] [] [] := by
    rw [show (6 : ℕ) = 3 + 3 by omega, run_add, hpre, hc]
    rfl
  simpa [encodeWord, traceBit, encodeBit, initial] using hr

/-- One fixed program computes the exact bit in every dimension, builds its
own loop data, preserves the modulus, and clears the disposable input and
all work. No arithmetic or runtime contract remains as a premise. -/
theorem run_traceBit (n : ℕ) (u : BinaryWord n) :
    ∃ t ≤ timeBound n,
      run t (cfg (some (.inr .fill)) initial (encodeWord u) []
        (encodeWord (chosenWord n)) [] []) =
      cfg none (SamplerMachineTrace.initial, encodeBit (traceBit n u), none)
        [] [] (encodeWord (chosenWord n)) [] [] := by
  cases n with
  | zero => exact ⟨6, by norm_num [timeBound, traceTime], run_traceBit_zero u⟩
  | succ n => exact run_traceBit_pos (Nat.succ_pos n) u

theorem timeBound_polynomial (n : ℕ) : timeBound n ≤ 16 * (n + 1) ^ 3 := by
  unfold timeBound traceTime
  nlinarith [Nat.zero_le (n ^ 3)]

end EthInapproximability.CurrentPaper.SamplerMachineTraceBit
