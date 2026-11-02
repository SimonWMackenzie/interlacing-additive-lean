import EthInapproximability.CurrentPaper.SamplerMachineSeedRow
import EthInapproximability.CurrentPaper.SamplerMachineCounterMap

/-!
# The complete ordered binary sampler table

Source: locked v8 Appendix E, `lem:exact-families`. A real scan of the
selected modulus initializes the seed counter. The implemented seed-row
callback is invoked once per counter. The final seed counter is cleared,
and one last physical reversal puts the table into seed-major order.
-/

namespace EthInapproximability.CurrentPaper.SamplerMachineTable

open Turing Turing.TM2.Stmt BitMachineEncoding BitMachineComposition
open ExecutableSmallBiasSampler SamplerMachine SamplerSeedEnumeration

abbrev InnerStack := SamplerMachineSearch.Stack SamplerMachineSeedRow.Stack
abbrev InnerLabel := SamplerMachineSearch.Label SamplerMachineSeedRow.Label
abbrev InnerControl := SamplerMachineSearch.Control SamplerMachineSeedRow.Control
abbrev InnerConfig := TM2.Cfg (fun _ : InnerStack => Bool) InnerLabel InnerControl

def innerProgram : InnerLabel → TM2.Stmt (fun _ : InnerStack => Bool) InnerLabel InnerControl :=
  SamplerMachineSearch.program SamplerMachineSeedRow.program SamplerMachineSeedRow.source
    (.inr (.inl .scanU)) SamplerMachineSeedRow.initial (fun _ => false)

def innerInitial : InnerControl := (SamplerMachineSeedRow.initial, false, none)

def innerCfg (l : Option InnerLabel) (s : InnerControl)
    (c q length bits work : List Bool) : InnerConfig :=
  ⟨l, s, Sum.elim (SamplerMachineSeedRow.cfg none s.1 c q length [] [] [] bits).stk (fun _ => work)⟩

inductive Admin where
  | fill | restore | clear | reverse
  deriving DecidableEq, Fintype

abbrev Stack := InnerStack ⊕ Unit
abbrev Label := InnerLabel ⊕ Admin
abbrev Control := InnerControl × Option Bool
abbrev Config := TM2.Cfg (fun _ : Stack => Bool) Label Control

def initial : Control := (innerInitial, none)
def modulus : Stack := .inl (.inl (.inl (.inl (.inl (.inl (.inr 0))))))
def source : Stack := .inl (.inl SamplerMachineSeedRow.source)
def lengthSource : Stack := .inl (.inl SamplerMachineSeedRow.lengthSource)
def innerOutput : Stack := .inl (.inl SamplerMachineSeedRow.output)
def output : Stack := .inr ()

def program : Label → TM2.Stmt (fun _ : Stack => Bool) Label Control
  | .inl l => liftStmt (some .clear) (innerProgram l)
  | .inr .fill => pop modulus (fun s b => (s.1, b))
      (branch (fun s => s.2.isSome)
        (push output (fun s => s.2.getD false)
          (push source (fun _ => false) (push source (fun _ => false)
            (goto (fun _ => .inr .fill)))))
        (goto (fun _ => .inr .restore)))
  | .inr .restore => pop output (fun s b => (s.1, b))
      (branch (fun s => s.2.isSome)
        (push modulus (fun s => s.2.getD false) (goto (fun _ => .inr .restore)))
        (load (fun _ => initial) (goto (fun _ => .inl (.inl (.inr (.inl .scanU)))))))
  | .inr .clear => pop source (fun s b => (s.1, b))
      (branch (fun s => s.2.isSome)
        (goto (fun _ => .inr .clear))
        (goto (fun _ => .inr .reverse)))
  | .inr .reverse => pop innerOutput (fun s b => (s.1, b))
      (branch (fun s => s.2.isSome)
        (push output (fun s => s.2.getD false) (goto (fun _ => .inr .reverse)))
        (load (fun _ => initial) halt))

def cfg (l : Option Label) (s : Control)
    (c q length bits work saved : List Bool) : Config :=
  ⟨l, s, Sum.elim (innerCfg none s.1 c q length bits work).stk (fun _ => saved)⟩

def run (t : ℕ) (q : Config) := ((advance program)^[t]) q

private theorem run_add (t s : ℕ) (q : Config) : run (t + s) q = run t (run s q) :=
  Function.iterate_add_apply _ _ _ _

private theorem run_succ {c d : Config} (h : TM2.step program c = some d) (n : ℕ) :
    run (n + 1) c = run n d := by
  simp only [run, Function.iterate_succ_apply, advance, h, Option.getD_some]

private theorem step_fill_cons (s : Control) (b : Bool) (c q length bits work saved : List Bool) :
    TM2.step program (cfg (some (.inr .fill)) s (b :: c) q length bits work saved) =
      some (cfg (some (.inr .fill)) (s.1, some b) c (false :: false :: q) length bits work (b :: saved)) := by
  dsimp only [TM2.step, TM2.stepAux, program, cfg, innerCfg, modulus, source, output,
    SamplerMachineSeedRow.cfg, SamplerMachineSeedRow.source, SamplerMachineSeedRow.splitRegister,
    SamplerMachineRow.cfg, SamplerMachineCoordinate.cfg, SamplerMachinePower.cfg,
    SamplerMachineProduct.cfg, SamplerMachineProduct.foreign, SamplerMachineAccumulate.stackContents,
    Sum.elim_inl, Sum.elim_inr]
  simp only [↓reduceIte, List.head?_cons, List.tail_cons, Option.isSome_some,
    Option.getD_some, Bool.cond_true, Option.some.injEq]
  congr 1
  funext k
  rcases k with ((((((k | k) | k) | k) | k) | k) | k) | k <;> (try fin_cases k) <;> rfl

private theorem step_fill_nil (s : Control) (q length bits work saved : List Bool) :
    TM2.step program (cfg (some (.inr .fill)) s [] q length bits work saved) =
      some (cfg (some (.inr .restore)) (s.1, none) [] q length bits work saved) := by
  dsimp only [TM2.step, TM2.stepAux, program, cfg, innerCfg, modulus, source, output,
    SamplerMachineSeedRow.cfg, SamplerMachineSeedRow.source, SamplerMachineSeedRow.splitRegister,
    SamplerMachineRow.cfg, SamplerMachineCoordinate.cfg, SamplerMachinePower.cfg,
    SamplerMachineProduct.cfg, SamplerMachineProduct.foreign, SamplerMachineAccumulate.stackContents,
    Sum.elim_inl, Sum.elim_inr]
  simp only [↓reduceIte, List.head?_nil, List.tail_nil, Option.isSome_none,
    Bool.cond_false, Option.some.injEq]
  congr 1
  funext k
  rcases k with ((((((k | k) | k) | k) | k) | k) | k) | k <;> (try fin_cases k) <;> rfl

private theorem step_restore_cons (s : Control) (b : Bool) (c q length bits work saved : List Bool) :
    TM2.step program (cfg (some (.inr .restore)) s c q length bits work (b :: saved)) =
      some (cfg (some (.inr .restore)) (s.1, some b) (b :: c) q length bits work saved) := by
  dsimp only [TM2.step, TM2.stepAux, program, cfg, innerCfg, modulus, output,
    SamplerMachineSeedRow.cfg, SamplerMachineSeedRow.splitRegister,
    SamplerMachineRow.cfg, SamplerMachineCoordinate.cfg, SamplerMachinePower.cfg,
    SamplerMachineProduct.cfg, SamplerMachineProduct.foreign, SamplerMachineAccumulate.stackContents,
    Sum.elim_inl, Sum.elim_inr]
  simp only [List.head?_cons, List.tail_cons, Option.isSome_some,
    Option.getD_some, Bool.cond_true, Option.some.injEq]
  congr 1
  funext k
  rcases k with ((((((k | k) | k) | k) | k) | k) | k) | k <;> (try fin_cases k) <;> rfl

private theorem step_restore_nil (s : Control) (c q length bits work : List Bool) :
    TM2.step program (cfg (some (.inr .restore)) s c q length bits work []) =
      some (cfg (some (.inl (.inl (.inr (.inl .scanU))))) initial c q length bits work []) := by
  dsimp only [TM2.step, TM2.stepAux, program, cfg, innerCfg, output, Sum.elim_inr]
  simp only [List.head?_nil, List.tail_nil, Option.isSome_none, Bool.cond_false, Option.some.injEq]
  congr 1
  funext k
  rcases k with k | k <;> rfl

theorem fill_run (s : Control) (c q length bits work saved : List Bool) :
    run (c.length + 1) (cfg (some (.inr .fill)) s c q length bits work saved) =
      cfg (some (.inr .restore)) (s.1, none) [] (List.replicate (2 * c.length) false ++ q)
        length bits work (c.reverse ++ saved) := by
  induction c generalizing s q saved with
  | nil => simpa using run_succ (step_fill_nil s q length bits work saved) 0
  | cons b c ih =>
      rw [List.length_cons, run_succ (step_fill_cons s b c q length bits work saved)]
      have he : List.replicate (2 * c.length) false ++ false :: false :: q =
          List.replicate (2 * (c.length + 1)) false ++ q := by
        rw [show 2 * (c.length + 1) = 2 * c.length + 2 by omega, List.replicate_add]
        simp
      simpa only [List.reverse_cons, List.append_assoc, List.singleton_append, he] using
        ih (s.1, some b) (false :: false :: q) (b :: saved)

theorem restore_run (s : Control) (c q length bits work saved : List Bool) :
    run (saved.length + 1) (cfg (some (.inr .restore)) s c q length bits work saved) =
      cfg (some (.inl (.inl (.inr (.inl .scanU))))) initial (saved.reverse ++ c)
        q length bits work [] := by
  induction saved generalizing s c with
  | nil => simpa using run_succ (step_restore_nil s c q length bits work) 0
  | cons b saved ih =>
      rw [List.length_cons, run_succ (step_restore_cons s b c q length bits work saved)]
      simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using ih (s.1, some b) (b :: c)

theorem prepare_run (c length : List Bool) :
    run (2 * c.length + 2) (cfg (some (.inr .fill)) initial c [] length [] [] []) =
      cfg (some (.inl (.inl (.inr (.inl .scanU))))) initial c
        (List.replicate (2 * c.length) false) length [] [] [] := by
  have hf := fill_run initial c [] length [] [] []
  have hr := restore_run (initial.1, none) [] (List.replicate (2 * c.length) false) length [] [] c.reverse
  simp only [List.append_nil, List.length_reverse, List.reverse_reverse] at hf hr
  rw [show 2 * c.length + 2 = (c.length + 1) + (c.length + 1) by omega, run_add, hf, hr]

private theorem step_clear_cons (s : Control) (b : Bool) (c q length bits work saved : List Bool) :
    TM2.step program (cfg (some (.inr .clear)) s c (b :: q) length bits work saved) =
      some (cfg (some (.inr .clear)) (s.1, some b) c q length bits work saved) := by
  dsimp only [TM2.step, TM2.stepAux, program, cfg, innerCfg, source,
    SamplerMachineSeedRow.cfg, SamplerMachineSeedRow.source, Sum.elim_inl, Sum.elim_inr]
  simp only [↓reduceIte, List.head?_cons, List.tail_cons, Option.isSome_some, Bool.cond_true, Option.some.injEq]
  congr 1
  funext k
  rcases k with k | k
  · rcases k with k | k
    · rcases k with k | k
      · rfl
      · fin_cases k <;> rfl
    · rfl
  · rfl

private theorem step_clear_nil (s : Control) (c length bits work saved : List Bool) :
    TM2.step program (cfg (some (.inr .clear)) s c [] length bits work saved) =
      some (cfg (some (.inr .reverse)) (s.1, none) c [] length bits work saved) := by
  dsimp only [TM2.step, TM2.stepAux, program, cfg, innerCfg, source,
    SamplerMachineSeedRow.cfg, SamplerMachineSeedRow.source, Sum.elim_inl, Sum.elim_inr]
  simp only [↓reduceIte, List.head?_nil, List.tail_nil, Option.isSome_none, Bool.cond_false, Option.some.injEq]
  congr 1
  funext k
  rcases k with k | k
  · rcases k with k | k
    · rcases k with k | k
      · rfl
      · fin_cases k <;> rfl
    · rfl
  · rfl

private theorem step_reverse_cons (s : Control) (b : Bool) (c q length bits work saved : List Bool) :
    TM2.step program (cfg (some (.inr .reverse)) s c q length (b :: bits) work saved) =
      some (cfg (some (.inr .reverse)) (s.1, some b) c q length bits work (b :: saved)) := by
  dsimp only [TM2.step, TM2.stepAux, program, cfg, innerCfg, innerOutput, output,
    SamplerMachineSeedRow.cfg, SamplerMachineSeedRow.output, SamplerMachineRow.cfg,
    SamplerMachineRow.foreign, Sum.elim_inl, Sum.elim_inr]
  simp only [show (4 : Fin 6) ≠ 0 by decide, show (4 : Fin 6) ≠ 1 by decide,
    show (4 : Fin 6) ≠ 2 by decide, show (4 : Fin 6) ≠ 3 by decide, ↓reduceIte,
    List.head?_cons, List.tail_cons, Option.isSome_some, Option.getD_some,
    Bool.cond_true, Option.some.injEq]
  congr 1
  funext k
  rcases k with k | k
  · rcases k with k | k
    · rcases k with k | k
      · rcases k with k | k
        · rfl
        · fin_cases k <;> rfl
      · rfl
    · rfl
  · rfl

private theorem step_reverse_nil (s : Control) (c q length work saved : List Bool) :
    TM2.step program (cfg (some (.inr .reverse)) s c q length [] work saved) =
      some (cfg none initial c q length [] work saved) := by
  dsimp only [TM2.step, TM2.stepAux, program, cfg, innerCfg, innerOutput, output,
    SamplerMachineSeedRow.cfg, SamplerMachineSeedRow.output, SamplerMachineRow.cfg,
    SamplerMachineRow.foreign, Sum.elim_inl, Sum.elim_inr]
  simp only [show (4 : Fin 6) ≠ 0 by decide, show (4 : Fin 6) ≠ 1 by decide,
    show (4 : Fin 6) ≠ 2 by decide, show (4 : Fin 6) ≠ 3 by decide, ↓reduceIte,
    List.head?_nil, List.tail_nil, Option.isSome_none, Bool.cond_false, Option.some.injEq]
  congr 1
  funext k
  rcases k with k | k
  · rcases k with k | k
    · rcases k with k | k
      · rcases k with k | k
        · rfl
        · fin_cases k <;> rfl
      · rfl
    · rfl
  · rfl

theorem clear_run (s : Control) (c q length bits work saved : List Bool) :
    run (q.length + 1) (cfg (some (.inr .clear)) s c q length bits work saved) =
      cfg (some (.inr .reverse)) (s.1, none) c [] length bits work saved := by
  induction q generalizing s with
  | nil => simpa using run_succ (step_clear_nil s c length bits work saved) 0
  | cons b q ih =>
      rw [List.length_cons, run_succ (step_clear_cons s b c q length bits work saved)]
      exact ih (s.1, some b)

theorem reverse_run (s : Control) (c q length bits work saved : List Bool) :
    run (bits.length + 1) (cfg (some (.inr .reverse)) s c q length bits work saved) =
      cfg none initial c q length [] work (bits.reverse ++ saved) := by
  induction bits generalizing s saved with
  | nil => simpa using run_succ (step_reverse_nil s c q length work saved) 0
  | cons b bits ih =>
      rw [List.length_cons, run_succ (step_reverse_cons s b c q length bits work saved)]
      simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using ih (s.1, some b) (b :: saved)

theorem map_cfg (n L : ℕ) (l : Option InnerLabel) (s : InnerControl) (q out work : List Bool) :
    SamplerMachineCounterMap.cfg SamplerMachineSeedRow.source SamplerMachineSeedRow.output
      (SamplerMachineSeedRow.inputBank n L) l s q out work =
      innerCfg l s (encodeWord (chosenWord n)) q (List.replicate L true) out work := by
  change (⟨l, s, Sum.elim (SamplerMachineCounterMap.bank SamplerMachineSeedRow.source
    SamplerMachineSeedRow.output (SamplerMachineSeedRow.inputBank n L) q out) (fun _ => work)⟩ : InnerConfig) = _
  rw [SamplerMachineSeedRow.inputBank_update]
  rfl

def innerBound (n L : ℕ) : ℕ :=
  2 ^ (2 * n) * (SamplerMachineSeedRow.timeBound n L + 8 * n + 6)

/-- The actual counter mapper is installed with the complete seed-row
implementation, so no callback or runtime premise remains. -/
theorem inner_run (n L : ℕ) :
    ∃ (t : ℕ) (s : InnerControl) (last : List Bool), t ≤ innerBound n L ∧ last.length = 2 * n ∧
      ((advance innerProgram)^[t])
        (innerCfg (some (.inl (.inr (.inl .scanU)))) innerInitial (encodeWord (chosenWord n))
          (List.replicate (2 * n) false) (List.replicate L true) [] []) =
        innerCfg none s (encodeWord (chosenWord n)) last (List.replicate L true)
          (counterTraceTable n L).reverse [] := by
  obtain ⟨t, s, last, ht, hlast, _, hr, _⟩ := SamplerMachineCounterMap.map_allWords
    SamplerMachineSeedRow.program SamplerMachineSeedRow.source SamplerMachineSeedRow.output
    (.inr (.inl .scanU)) SamplerMachineSeedRow.initial (SamplerMachineSeedRow.inputBank n L)
    (by decide) (2 * n) (SamplerMachineSeedRow.timeBound n L) (SamplerMachineSeedRow.row n L)
    (SamplerMachineSeedRow.predicate_contract n L) []
  simp only [SamplerMachineCounterMap.run, SamplerMachineCounterMap.program,
    map_cfg, List.append_nil] at hr
  refine ⟨t, (s, true, none), last, ?_, hlast, hr⟩
  simpa only [innerBound, show 4 * (2 * n) = 8 * n by omega] using ht

theorem inner_cfg (l : Option InnerLabel) (s : InnerControl)
    (c q length bits work saved : List Bool) :
    liftCfg (some .clear) (none : Option Bool) (fun _ : Unit => saved) (innerCfg l s c q length bits work) =
      cfg (match l with | none => some (.inr .clear) | some l => some (.inl l))
        (s, none) c q length bits work saved := by cases l <;> rfl

theorem table_call (n L : ℕ) :
    ∃ (t : ℕ) (s : Control) (last : List Bool), t ≤ innerBound n L ∧ last.length = 2 * n ∧
      run t (cfg (some (.inl (.inl (.inr (.inl .scanU))))) initial (encodeWord (chosenWord n))
        (List.replicate (2 * n) false) (List.replicate L true) [] [] []) =
      cfg (some (.inr .clear)) s (encodeWord (chosenWord n)) last (List.replicate L true)
        (counterTraceTable n L).reverse [] [] := by
  obtain ⟨t, s, last, ht, hlast, hr⟩ := inner_run n L
  have hh : (((advance innerProgram)^[t])
      (innerCfg (some (.inl (.inr (.inl .scanU)))) innerInitial (encodeWord (chosenWord n))
        (List.replicate (2 * n) false) (List.replicate L true) [] [])).l = none := by rw [hr]; rfl
  obtain ⟨t', ht', hrun⟩ := BitMachineSubroutine.lift_outputs innerProgram program
    (some .clear) (fun _ => rfl) (none : Option Bool) (fun _ : Unit => [])
    (innerCfg (some (.inl (.inr (.inl .scanU)))) innerInitial (encodeWord (chosenWord n))
      (List.replicate (2 * n) false) (List.replicate L true) [] []) t hh
  rw [hr, inner_cfg, inner_cfg] at hrun
  exact ⟨t', (s, none), last, ht'.trans ht, hlast, hrun⟩

def timeBound (n L : ℕ) : ℕ := innerBound n L + (2 ^ n) ^ 2 * L + 4 * n + 4

/-- Complete ordered table generation on the selected-modulus bank. The
seed counter, row indices and argument copies are constructed and cleared
by the machine; only modulus and unary row length are supplied. -/
theorem run_table (n L : ℕ) :
    ∃ t ≤ timeBound n L,
      run t (cfg (some (.inr .fill)) initial (encodeWord (chosenWord n)) []
        (List.replicate L true) [] [] []) =
      cfg none initial (encodeWord (chosenWord n)) [] (List.replicate L true) [] []
        (counterTraceTable n L) := by
  have hp := prepare_run (encodeWord (chosenWord n)) (List.replicate L true)
  simp only [encodeWord_length] at hp
  obtain ⟨t, s, last, ht, hlast, hr⟩ := table_call n L
  have hc := clear_run s (encodeWord (chosenWord n)) last (List.replicate L true)
    (counterTraceTable n L).reverse [] []
  rw [hlast] at hc
  have hf := reverse_run (s.1, none) (encodeWord (chosenWord n)) [] (List.replicate L true)
    (counterTraceTable n L).reverse [] []
  simp only [List.length_reverse, counterTraceTable_length, List.reverse_reverse, List.append_nil] at hf
  refine ⟨((2 ^ n) ^ 2 * L + 1) + ((2 * n + 1) + (t + (2 * n + 2))), ?_, ?_⟩
  · unfold timeBound
    omega
  · rw [run_add ((2 ^ n) ^ 2 * L + 1) ((2 * n + 1) + (t + (2 * n + 2))),
      run_add (2 * n + 1) (t + (2 * n + 2)), run_add t (2 * n + 2), hp, hr, hc, hf]

theorem run_indexedTable (L B : ℕ) :
    let n := SmallBiasSampler.fieldExponent L B
    ∃ t ≤ timeBound n L,
      run t (cfg (some (.inr .fill)) initial (encodeWord (chosenWord n)) []
        (List.replicate L true) [] [] []) =
      cfg none initial (encodeWord (chosenWord n)) [] (List.replicate L true) [] []
        ((List.ofFn fun seed : Fin ((2 ^ n) ^ 2) =>
          List.ofFn fun i : Fin L => encodeBit (indexedTraceBits L B seed i)).flatten) := by
  simpa only [counterTraceTable_indexed] using run_table (SmallBiasSampler.fieldExponent L B) L

end EthInapproximability.CurrentPaper.SamplerMachineTable
