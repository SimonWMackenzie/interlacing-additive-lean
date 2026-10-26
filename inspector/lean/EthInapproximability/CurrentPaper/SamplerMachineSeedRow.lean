import EthInapproximability.CurrentPaper.SamplerMachineRow
import EthInapproximability.CurrentPaper.SamplerMachineFactorSplit
import EthInapproximability.CurrentPaper.SamplerSeedEnumeration
import EthInapproximability.CurrentPaper.SamplerMachineCounterMap

/-!
# From one enumerated seed counter to its complete sampler row

Source: locked v8 Appendix E, `lem:exact-families`. The low half of the
counter is `y`, the high half is `x`, matching the original seed labels.
This controller splits that real counter, copies a stored row-length
counter, executes the complete row loop, and clears the seed copies. The
counter, modulus, and row length are all preserved for the next seed.
-/

namespace EthInapproximability.CurrentPaper.SamplerMachineSeedRow

open Turing Turing.TM2.Stmt BitMachineEncoding BitMachineComposition
open ExecutableSmallBiasSampler SamplerMachine

inductive Admin where
  | reset | copy (l : BitMachineCopy.Label) | call | clearX | clearY
  deriving DecidableEq, Fintype

abbrev Stack := SamplerMachineRow.Stack ⊕ Fin 2
abbrev Label := SamplerMachineRow.Label ⊕ (SamplerMachineFactorSplit.Label ⊕ Admin)
abbrev Control := SamplerMachineRow.Control × (SamplerMachineFactorSplit.Control × Option Bool)
abbrev Config := TM2.Cfg (fun _ : Stack => Bool) Label Control

def initial : Control := (SamplerMachineRow.initial, SamplerMachineFactorSplit.initial, none)
def source : Stack := .inr 0
def lengthSource : Stack := .inr 1
def output : Stack := .inl (.inr 4)
def modulus : Stack := .inl (.inl (.inl (.inl (.inr 0))))

def splitRegister : SamplerMachineFactorSplit.Stack ↪ Stack where
  toFun := fun k => match k with
    | .candidate => .inl (.inl (.inl (.inl (.inr 0))))
    | .counter => source
    | .factorU => .inl (.inr 1)
    | .factorV => .inl (.inr 0)
    | .savedC => .inl (.inl (.inl (.inl (.inl 0))))
    | .savedQ => .inl (.inl (.inl (.inl (.inl 1))))
  inj' := by intro a b h; cases a <;> cases b <;> simp_all [source]

def copyRegister : Fin 3 ↪ Stack where
  toFun := fun k => if k = 0 then lengthSource else if k = 1 then .inl (.inr 3) else .inl (.inr 5)
  inj' := by intro a b h; fin_cases a <;> fin_cases b <;> simp_all [lengthSource]

def splitEmbed (s : SamplerMachineFactorSplit.Control) : Control := (SamplerMachineRow.initial, s, none)
def copyEmbed (b : Option Bool) : Control := (SamplerMachineRow.initial, SamplerMachineFactorSplit.initial, b)

def program : Label → TM2.Stmt (fun _ : Stack => Bool) Label Control
  | .inl l => liftStmt (some (.inr .clearX)) (SamplerMachineRow.program l)
  | .inr (.inl l) => BitMachineStackEmbedding.stmt splitRegister
      (fun l => .inr (.inl l)) splitEmbed (fun s => s.2.1) (some (.inr (.inr .reset)))
      (SamplerMachineFactorSplit.program l)
  | .inr (.inr .reset) => load (fun _ => initial) (goto (fun _ => .inr (.inr (.copy .scan))))
  | .inr (.inr (.copy l)) => BitMachineStackEmbedding.stmt copyRegister
      (fun l => .inr (.inr (.copy l))) copyEmbed (fun s => s.2.2) (some (.inr (.inr .call)))
      (BitMachineCopy.program l)
  | .inr (.inr .call) => load (fun _ => initial) (goto (fun _ => .inl (.inr .loop)))
  | .inr (.inr .clearX) => pop (.inl (.inr 0)) (fun s b => (s.1, s.2.1, b))
      (branch (fun s => s.2.2.isSome)
        (goto (fun _ => .inr (.inr .clearX)))
        (goto (fun _ => .inr (.inr .clearY))))
  | .inr (.inr .clearY) => pop (.inl (.inr 1)) (fun s b => (s.1, s.2.1, b))
      (branch (fun s => s.2.2.isSome)
        (goto (fun _ => .inr (.inr .clearY)))
        (load (fun _ => initial) halt))

def cfg (l : Option Label) (s : Control) (c q length x y budget out : List Bool) : Config :=
  ⟨l, s, Sum.elim (SamplerMachineRow.cfg none s.1 [] [] c [] x y [] budget out []).stk
    (fun i => if i = 0 then q else length)⟩

def run (t : ℕ) (q : Config) := ((advance program)^[t]) q

private theorem run_add (t s : ℕ) (q : Config) : run (t + s) q = run t (run s q) :=
  Function.iterate_add_apply _ _ _ _

private theorem run_zero (q : Config) : run 0 q = q := rfl

private theorem run_succ {c d : Config} (h : TM2.step program c = some d) (n : ℕ) :
    run (n + 1) c = run n d := by
  simp only [run, Function.iterate_succ_apply, advance, h, Option.getD_some]

theorem split_bank (c q u v length out : List Bool) :
    BitMachineStackEmbedding.bank splitRegister (cfg none initial c q length [] [] [] out).stk
      (SamplerMachineFactorSplit.stackContents c q u v [] []) =
      (cfg none initial c q length v u [] out).stk := by
  classical
  funext k
  rcases k with ((((k | k) | k) | k) | k) | k <;> (try fin_cases k)
  all_goals first
    | exact BitMachineStackEmbedding.bank_at splitRegister _ _ .candidate
    | exact BitMachineStackEmbedding.bank_at splitRegister _ _ .counter
    | exact BitMachineStackEmbedding.bank_at splitRegister _ _ .factorU
    | exact BitMachineStackEmbedding.bank_at splitRegister _ _ .factorV
    | exact BitMachineStackEmbedding.bank_at splitRegister _ _ .savedC
    | exact BitMachineStackEmbedding.bank_at splitRegister _ _ .savedQ
    | apply BitMachineStackEmbedding.bank_outside
      rintro ⟨j, h⟩
      cases j <;> cases h

theorem split_cfg (l : Option SamplerMachineFactorSplit.Label) (s : SamplerMachineFactorSplit.Control)
    (c q u v length out : List Bool) :
    BitMachineStackEmbedding.cfg splitRegister (cfg none initial c q length [] [] [] out).stk
      (fun l => .inr (.inl l)) splitEmbed (some (.inr (.inr .reset)))
      (SamplerMachineFactorSplit.cfg l s c q u v [] []) =
      cfg (match l with | none => some (.inr (.inr .reset)) | some l => some (.inr (.inl l)))
        (splitEmbed s) c q length v u [] out := by
  cases l <;> dsimp only [BitMachineStackEmbedding.cfg, BitMachineStackEmbedding.stackCfg,
    BitMachineInline.cfg, SamplerMachineFactorSplit.cfg, cfg, Option.map_some]
  all_goals congr 1; exact split_bank c q u v length out

theorem split_call (n : ℕ) (x y : BinaryWord n) (length out : List Bool) :
    ∃ (t : ℕ) (s : SamplerMachineFactorSplit.Control), t ≤ 4 * n + 4 ∧
      run t (cfg (some (.inr (.inl .scanU))) initial (encodeWord (chosenWord n))
        (encodeWord y ++ encodeWord x) length [] [] [] out) =
      cfg (some (.inr (.inr .reset))) (splitEmbed s) (encodeWord (chosenWord n))
        (encodeWord y ++ encodeWord x) length (encodeWord x) (encodeWord y) [] out := by
  have hr := SamplerMachineFactorSplit.split_coefficients (chosenWord n) y x
  have hh : (SamplerMachineFactorSplit.run (4 * n + 4)
      (SamplerMachineFactorSplit.cfg (some .scanU) SamplerMachineFactorSplit.initial
        (encodeWord (chosenWord n)) (encodeWord y ++ encodeWord x) [] [] [] [])).l = none := by
    simp only [SamplerMachineFactorSplit.initial]
    rw [hr]; rfl
  obtain ⟨t, ht, hrun⟩ := BitMachineStackEmbedding.outputs splitRegister
    (cfg none initial (encodeWord (chosenWord n)) (encodeWord y ++ encodeWord x) length [] [] [] out).stk
    (fun l => .inr (.inl l)) splitEmbed (fun s => s.2.1) (fun _ => rfl)
    (some (.inr (.inr .reset))) SamplerMachineFactorSplit.program program (fun _ => rfl)
    (SamplerMachineFactorSplit.cfg (some .scanU) SamplerMachineFactorSplit.initial
      (encodeWord (chosenWord n)) (encodeWord y ++ encodeWord x) [] [] [] []) (4 * n + 4) hh
  dsimp only [SamplerMachineFactorSplit.run] at hr
  simp only [SamplerMachineFactorSplit.initial] at hrun
  rw [hr, split_cfg, split_cfg] at hrun
  exact ⟨t, _, ht, hrun⟩

theorem copy_bank (c q length x y out : List Bool) (budget : List Bool) :
    BitMachineStackEmbedding.bank copyRegister (cfg none initial c q length x y [] out).stk
      (BitMachineCopy.stackContents length budget []) =
      (cfg none initial c q length x y budget out).stk := by
  classical
  funext k
  rcases k with ((((k | k) | k) | k) | k) | k <;> (try fin_cases k)
  all_goals first
    | exact BitMachineStackEmbedding.bank_at copyRegister _ _ 0
    | exact BitMachineStackEmbedding.bank_at copyRegister _ _ 1
    | exact BitMachineStackEmbedding.bank_at copyRegister _ _ 2
    | apply BitMachineStackEmbedding.bank_outside
      rintro ⟨j, h⟩
      fin_cases j <;> cases h

theorem copy_cfg (l : Option BitMachineCopy.Label) (c q length x y out budget : List Bool) :
    BitMachineStackEmbedding.cfg copyRegister (cfg none initial c q length x y [] out).stk
      (fun l => .inr (.inr (.copy l))) copyEmbed (some (.inr (.inr .call)))
      (BitMachineCopy.cfg l none length budget []) =
      cfg (match l with | none => some (.inr (.inr .call)) | some l => some (.inr (.inr (.copy l))))
        initial c q length x y budget out := by
  cases l <;> dsimp only [BitMachineStackEmbedding.cfg, BitMachineStackEmbedding.stackCfg,
    BitMachineInline.cfg, BitMachineCopy.cfg, cfg, Option.map_some]
  all_goals congr 1; exact copy_bank c q length x y out budget

theorem copy_call (c q length x y out : List Bool) :
    ∃ t ≤ 2 * length.length + 2,
      run t (cfg (some (.inr (.inr (.copy .scan)))) initial c q length x y [] out) =
      cfg (some (.inr (.inr .call))) initial c q length x y length out := by
  have hr := BitMachineCopy.run_correct none length []
  simp only [List.append_nil] at hr
  have hh : (BitMachineCopy.run (2 * length.length + 2)
      (BitMachineCopy.cfg (some .scan) none length [] [])).l = none := by rw [hr]; rfl
  obtain ⟨t, ht, hrun⟩ := BitMachineStackEmbedding.outputs copyRegister
    (cfg none initial c q length x y [] out).stk
    (fun l => .inr (.inr (.copy l))) copyEmbed (fun s => s.2.2) (fun _ => rfl)
    (some (.inr (.inr .call))) BitMachineCopy.program program (fun _ => rfl)
    (BitMachineCopy.cfg (some .scan) none length [] []) (2 * length.length + 2) hh
  dsimp only [BitMachineCopy.run] at hr
  rw [hr, copy_cfg, copy_cfg] at hrun
  exact ⟨t, ht, hrun⟩

private theorem step_reset (s : SamplerMachineFactorSplit.Control)
    (c q length x y out : List Bool) :
    TM2.step program (cfg (some (.inr (.inr .reset))) (splitEmbed s) c q length x y [] out) =
      some (cfg (some (.inr (.inr (.copy .scan)))) initial c q length x y [] out) := rfl

private theorem step_call (c q length x y budget out : List Bool) :
    TM2.step program (cfg (some (.inr (.inr .call))) initial c q length x y budget out) =
      some (cfg (some (.inl (.inr .loop))) initial c q length x y budget out) := rfl

theorem row_cfg (l : Option SamplerMachineRow.Label) (s : SamplerMachineRow.Control)
    (c q length x y budget out : List Bool) :
    liftCfg (some (.inr .clearX)) (SamplerMachineFactorSplit.initial, (none : Option Bool))
      (fun i : Fin 2 => if i = 0 then q else length)
      (SamplerMachineRow.cfg l s [] [] c [] x y [] budget out []) =
      cfg (match l with | none => some (.inr (.inr .clearX)) | some l => some (.inl l))
        (s, SamplerMachineFactorSplit.initial, none) c q length x y budget out := by
  cases l <;> rfl

theorem row_call (n L : ℕ) (x y : BinaryWord n) (q out : List Bool) :
    ∃ t ≤ L * SamplerMachineRow.roundBound n L + L + 2,
      run t (cfg (some (.inl (.inr .loop))) initial (encodeWord (chosenWord n)) q
        (List.replicate L true) (encodeWord x) (encodeWord y) (List.replicate L true) out) =
      cfg (some (.inr (.inr .clearX))) initial (encodeWord (chosenWord n)) q
        (List.replicate L true) (encodeWord x) (encodeWord y) []
        ((List.ofFn fun j : Fin L => encodeBit (executableTraceBits n L (x, y) j)).reverse ++ out) := by
  obtain ⟨t, ht, hr⟩ := SamplerMachineRow.run_executableRow n L x y out
  have hh : (SamplerMachineRow.run t
      (SamplerMachineRow.cfg (some (.inr .loop)) SamplerMachineRow.initial [] []
        (encodeWord (chosenWord n)) [] (encodeWord x) (encodeWord y) []
        (List.replicate L true) out [])).l = none := by rw [hr]; rfl
  obtain ⟨t', ht', hrun⟩ := BitMachineSubroutine.lift_outputs SamplerMachineRow.program
    program (some (.inr .clearX)) (fun _ => rfl)
    (SamplerMachineFactorSplit.initial, (none : Option Bool))
    (fun i : Fin 2 => if i = 0 then q else List.replicate L true)
    (SamplerMachineRow.cfg (some (.inr .loop)) SamplerMachineRow.initial [] []
      (encodeWord (chosenWord n)) [] (encodeWord x) (encodeWord y) []
      (List.replicate L true) out []) t hh
  dsimp only [SamplerMachineRow.run] at hr
  rw [hr, row_cfg, row_cfg] at hrun
  exact ⟨t', ht'.trans ht, hrun⟩

private theorem step_clearX_cons (s : Control) (b : Bool) (c q length x y out : List Bool) :
    TM2.step program (cfg (some (.inr (.inr .clearX))) s c q length (b :: x) y [] out) =
      some (cfg (some (.inr (.inr .clearX))) (s.1, s.2.1, some b) c q length x y [] out) := by
  dsimp only [TM2.step, TM2.stepAux, program, cfg, SamplerMachineRow.cfg,
    SamplerMachineRow.foreign, Sum.elim_inl, Sum.elim_inr]
  simp only [↓reduceIte, List.head?_cons, List.tail_cons, Option.isSome_some,
    Bool.cond_true, Option.some.injEq]
  congr 1
  funext k
  rcases k with (k | k) | k
  · rfl
  · fin_cases k <;> rfl
  · rfl

private theorem step_clearX_nil (s : Control) (c q length y out : List Bool) :
    TM2.step program (cfg (some (.inr (.inr .clearX))) s c q length [] y [] out) =
      some (cfg (some (.inr (.inr .clearY))) (s.1, s.2.1, none) c q length [] y [] out) := by
  dsimp only [TM2.step, TM2.stepAux, program, cfg, SamplerMachineRow.cfg,
    SamplerMachineRow.foreign, Sum.elim_inl, Sum.elim_inr]
  simp only [↓reduceIte, List.head?_nil, List.tail_nil, Option.isSome_none,
    Bool.cond_false, Option.some.injEq]
  congr 1
  funext k
  rcases k with (k | k) | k
  · rfl
  · fin_cases k <;> rfl
  · rfl

private theorem step_clearY_cons (s : Control) (b : Bool) (c q length y out : List Bool) :
    TM2.step program (cfg (some (.inr (.inr .clearY))) s c q length [] (b :: y) [] out) =
      some (cfg (some (.inr (.inr .clearY))) (s.1, s.2.1, some b) c q length [] y [] out) := by
  dsimp only [TM2.step, TM2.stepAux, program, cfg, SamplerMachineRow.cfg,
    SamplerMachineRow.foreign, Sum.elim_inl, Sum.elim_inr]
  simp only [show (1 : Fin 6) ≠ 0 by decide, ↓reduceIte, List.head?_cons, List.tail_cons,
    Option.isSome_some, Bool.cond_true, Option.some.injEq]
  congr 1
  funext k
  rcases k with (k | k) | k
  · rfl
  · fin_cases k <;> rfl
  · rfl

private theorem step_clearY_nil (s : Control) (c q length out : List Bool) :
    TM2.step program (cfg (some (.inr (.inr .clearY))) s c q length [] [] [] out) =
      some (cfg none initial c q length [] [] [] out) := by
  dsimp only [TM2.step, TM2.stepAux, program, cfg, SamplerMachineRow.cfg,
    SamplerMachineRow.foreign, Sum.elim_inl, Sum.elim_inr]
  simp only [show (1 : Fin 6) ≠ 0 by decide, ↓reduceIte, List.head?_nil, List.tail_nil,
    Option.isSome_none, Bool.cond_false, Option.some.injEq]
  congr 1
  funext k
  rcases k with (k | k) | k
  · rfl
  · fin_cases k <;> rfl
  · rfl

theorem clearX_run (s : Control) (c q length x y out : List Bool) :
    run (x.length + 1) (cfg (some (.inr (.inr .clearX))) s c q length x y [] out) =
      cfg (some (.inr (.inr .clearY))) (s.1, s.2.1, none) c q length [] y [] out := by
  induction x generalizing s with
  | nil => simpa using run_succ (step_clearX_nil s c q length y out) 0
  | cons b x ih =>
      rw [List.length_cons, run_succ (step_clearX_cons s b c q length x y out)]
      exact ih (s.1, s.2.1, some b)

theorem clearY_run (s : Control) (c q length y out : List Bool) :
    run (y.length + 1) (cfg (some (.inr (.inr .clearY))) s c q length [] y [] out) =
      cfg none initial c q length [] [] [] out := by
  induction y generalizing s with
  | nil => simpa using run_succ (step_clearY_nil s c q length out) 0
  | cons b y ih =>
      rw [List.length_cons, run_succ (step_clearY_cons s b c q length y out)]
      exact ih (s.1, s.2.1, some b)

theorem clear_run (s : Control) (c q length x y out : List Bool) :
    run (x.length + y.length + 2) (cfg (some (.inr (.inr .clearX))) s c q length x y [] out) =
      cfg none initial c q length [] [] [] out := by
  rw [show x.length + y.length + 2 = (y.length + 1) + (x.length + 1) by omega,
    run_add, clearX_run, clearY_run]

def timeBound (n L : ℕ) : ℕ :=
  (L * SamplerMachineRow.roundBound n L + L + 2) + 6 * n + 2 * L + 10

theorem run_seedRow (n L : ℕ) (x y : BinaryWord n) (out : List Bool) :
    ∃ t ≤ timeBound n L,
      run t (cfg (some (.inr (.inl .scanU))) initial (encodeWord (chosenWord n))
        (encodeWord y ++ encodeWord x) (List.replicate L true) [] [] [] out) =
      cfg none initial (encodeWord (chosenWord n)) (encodeWord y ++ encodeWord x)
        (List.replicate L true) [] [] []
        ((List.ofFn fun j : Fin L => encodeBit (executableTraceBits n L (x, y) j)).reverse ++ out) := by
  obtain ⟨ts, s, hts, hs⟩ := split_call n x y (List.replicate L true) out
  have hreset := run_succ (step_reset s (encodeWord (chosenWord n))
    (encodeWord y ++ encodeWord x) (List.replicate L true) (encodeWord x) (encodeWord y) out) 0
  obtain ⟨tc, htc, hc⟩ := copy_call (encodeWord (chosenWord n))
    (encodeWord y ++ encodeWord x) (List.replicate L true) (encodeWord x) (encodeWord y) out
  have hcall := run_succ (step_call (encodeWord (chosenWord n))
    (encodeWord y ++ encodeWord x) (List.replicate L true) (encodeWord x) (encodeWord y)
    (List.replicate L true) out) 0
  obtain ⟨tr, htr, hr⟩ := row_call n L x y (encodeWord y ++ encodeWord x) out
  have hclear := clear_run initial (encodeWord (chosenWord n)) (encodeWord y ++ encodeWord x)
    (List.replicate L true) (encodeWord x) (encodeWord y)
    ((List.ofFn fun j : Fin L => encodeBit (executableTraceBits n L (x, y) j)).reverse ++ out)
  simp only [List.length_replicate] at htc
  simp only [encodeWord_length] at hclear
  simp only [run_zero, Nat.zero_add] at hreset hcall
  refine ⟨(2 * n + 2) + (tr + (1 + (tc + (1 + ts)))), ?_, ?_⟩
  · unfold timeBound
    omega
  · rw [run_add (2 * n + 2) (tr + (1 + (tc + (1 + ts)))),
      run_add tr (1 + (tc + (1 + ts))), run_add 1 (tc + (1 + ts)),
      run_add tc (1 + ts), run_add 1 ts, hs, hreset, hc, hcall, hr]
    simpa only [show n + n = 2 * n by omega] using hclear

def inputBank (n L : ℕ) : Stack → List Bool :=
  (cfg none initial (encodeWord (chosenWord n)) [] (List.replicate L true) [] [] [] []).stk

theorem inputBank_update (n L : ℕ) (q out : List Bool) :
    SamplerMachineCounterMap.bank source output (inputBank n L) q out =
      (cfg none initial (encodeWord (chosenWord n)) q (List.replicate L true) [] [] [] out).stk := by
  funext k
  rcases k with ((((k | k) | k) | k) | k) | k <;> (try fin_cases k) <;> rfl

def row (n L : ℕ) (q : List Bool) : List Bool :=
  List.ofFn fun j : Fin L => encodeBit
    (executableTraceBits n L (SamplerSeedEnumeration.seedOfCounter n q) j)

/-- The fully implemented callback contract consumed by the table loop. -/
theorem callback_contract (n L : ℕ) (q out : List Bool) (hq : q.length = 2 * n) :
    ∃ (t : ℕ) (v : Control), t ≤ timeBound n L ∧
      ((advance program)^[t])
        ⟨some (.inr (.inl .scanU)), initial,
          SamplerMachineCounterMap.bank source output (inputBank n L) q out⟩ =
        ⟨none, v, SamplerMachineCounterMap.bank source output (inputBank n L) q
          ((row n L q).reverse ++ out)⟩ := by
  obtain ⟨y, x, rfl⟩ := SamplerFactorEnumeration.exists_counter_decomposition n q hq
  obtain ⟨t, ht, hr⟩ := run_seedRow n L x y out
  refine ⟨t, initial, ht, ?_⟩
  rw [inputBank_update, inputBank_update]
  simpa only [row, SamplerSeedEnumeration.seedOfCounter,
    SamplerFactorEnumeration.upperWord_encoded, SamplerFactorEnumeration.lowerWord_encoded] using hr

theorem predicate_contract (n L : ℕ) (q out : List Bool) (hq : q.length = 2 * n) :
    ∃ (t : ℕ) (v : Control), t ≤ timeBound n L ∧
      ((advance program)^[t])
        ⟨some (.inr (.inl .scanU)), initial,
          SamplerMachineCounterMap.bank source output (inputBank n L) q out⟩ =
        ⟨none, v, SamplerMachineCounterMap.bank source output (inputBank n L) q
          ((row n L q).reverse ++ out)⟩ :=
  callback_contract n L q out hq

end EthInapproximability.CurrentPaper.SamplerMachineSeedRow
