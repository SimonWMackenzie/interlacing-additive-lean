import CurrentAdditive.WordOutputMachine
import CurrentAdditive.OneWordMachine
import CurrentAdditive.UnaryFuelCopyMachine
import CurrentAdditive.SeedPairSplit
import CurrentAdditive.CounterNatBridge
import EthInapproximability.CurrentPaper.BitMachineStackEmbedding

/-! A literal finite callback controller for one row-major field-list seed.
The source pair counter, lower-modulus word, and unary length are persistent.
All temporary words are built and cleared physically. The output is prepended
to the global output stack, as required by `SamplerMachineCounterMap`. -/

namespace CurrentAdditive.FiniteFieldMachine.SeedCallbackMachine

open Turing Turing.TM2.Stmt
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper.BitMachineComposition

inductive Admin where
  | resetSplit | resetOne | resetFuel | clearAcc | clearBase | clearSeed | copyFinal
  deriving DecidableEq, Fintype

abbrev Stack := WordOutputMachine.Stack ⊕ Fin 3
abbrev Label := WordOutputMachine.Label ⊕
  (SamplerMachineFactorSplit.Label ⊕
    (OneWordMachine.Label ⊕ (UnaryFuelCopyMachine.Label ⊕ Admin)))
abbrev Control := WordOutputMachine.Control ×
  (SamplerMachineFactorSplit.Control ×
    (OneWordMachine.Control × (UnaryFuelCopyMachine.Control × Option Bool)))
abbrev Config := TM2.Cfg (fun _ : Stack => Bool) Label Control

def initial : Control :=
  (WordOutputMachine.initial,
    (SamplerMachineFactorSplit.initial,
      (OneWordMachine.initial, (none, none))))

def inner (k : StreamingBitMachine.Stack) : Stack := .inl (.inl k)
def acc : Stack := inner StreamingBitMachine.acc
def base : Stack := inner StreamingBitMachine.base
def wa : Stack := inner (.inl (.inl 2))
def wo : Stack := inner (.inl (.inl 3))
def modulus : Stack := inner StreamingBitMachine.modulusBank
def fuel : Stack := inner StreamingBitMachine.fuelBank
def seed : Stack := inner StreamingBitMachine.seed
def finalWord : Stack := .inl WordOutputMachine.finalWord
def source : Stack := .inr 0
def lengthSource : Stack := .inr 1
def output : Stack := .inr 2

def splitRegister : SamplerMachineFactorSplit.Stack ↪ Stack where
  toFun := fun k => match k with
    | .candidate => modulus
    | .counter => source
    | .factorU => base
    | .factorV => seed
    | .savedC => wa
    | .savedQ => wo
  inj' := by
    intro a b h
    cases a <;> cases b <;> simp_all [modulus, source, base, seed, wa, wo, inner,
      StreamingBitMachine.modulusBank, StreamingBitMachine.base,
      StreamingBitMachine.seed]

def oneRegister : OneWordMachine.Stack ↪ Stack where
  toFun := fun k => match k with
    | .width => modulus
    | .savedWidth => wa
    | .tempOne => wo
    | .one => acc
  inj' := by
    intro a b h
    cases a <;> cases b <;> simp_all [modulus, wa, wo, acc, inner,
      StreamingBitMachine.modulusBank, StreamingBitMachine.acc]

def fuelRegister : UnaryFuelCopyMachine.Stack ↪ Stack where
  toFun := fun k => if k = 0 then lengthSource else if k = 1 then wa else fuel
  inj' := by
    intro a b h
    fin_cases a <;> fin_cases b <;> simp_all [lengthSource, wa, fuel, inner,
      StreamingBitMachine.fuelBank]

def splitEmbed (s : SamplerMachineFactorSplit.Control) : Control :=
  (WordOutputMachine.initial, (s, (OneWordMachine.initial, (none, none))))
def oneEmbed (s : OneWordMachine.Control) : Control :=
  (WordOutputMachine.initial,
    (SamplerMachineFactorSplit.initial, (s, (none, none))))
def fuelEmbed (s : UnaryFuelCopyMachine.Control) : Control :=
  (WordOutputMachine.initial,
    (SamplerMachineFactorSplit.initial, (OneWordMachine.initial, (s, none))))

def program : Label → TM2.Stmt (fun _ : Stack => Bool) Label Control
  | .inl l => liftStmt (some (.inr (.inr (.inr .clearAcc))))
      (WordOutputMachine.program l)
  | .inr (.inl l) => BitMachineStackEmbedding.stmt splitRegister
      (fun l => .inr (.inl l)) splitEmbed (fun s => s.2.1)
      (some (.inr (.inr (.inr (.inr .resetSplit)))))
      (SamplerMachineFactorSplit.program l)
  | .inr (.inr (.inl l)) => BitMachineStackEmbedding.stmt oneRegister
      (fun l => .inr (.inr (.inl l))) oneEmbed (fun s => s.2.2.1)
      (some (.inr (.inr (.inr (.inr .resetOne)))))
      (OneWordMachine.program l)
  | .inr (.inr (.inr (.inl l))) => BitMachineStackEmbedding.stmt fuelRegister
      (fun l => .inr (.inr (.inr (.inl l)))) fuelEmbed (fun s => s.2.2.2.1)
      (some (.inr (.inr (.inr (.inr .resetFuel)))))
      (UnaryFuelCopyMachine.program l)
  | .inr (.inr (.inr (.inr .resetSplit))) =>
      load (fun _ => initial) (goto (fun _ => .inr (.inr (.inl .scan))))
  | .inr (.inr (.inr (.inr .resetOne))) =>
      load (fun _ => initial) (goto (fun _ => .inr (.inr (.inr (.inl .scan)))))
  | .inr (.inr (.inr (.inr .resetFuel))) =>
      load (fun _ => initial) (goto (fun _ => .inl (.inl (.inr .check))))
  | .inr (.inr (.inr (.inr .clearAcc))) => pop acc (fun s b => (s.1, s.2.1,
      s.2.2.1, (s.2.2.2.1, b)))
      (branch (fun s => s.2.2.2.2.isSome)
        (goto (fun _ => .inr (.inr (.inr (.inr .clearAcc)))))
        (goto (fun _ => .inr (.inr (.inr (.inr .clearBase))))))
  | .inr (.inr (.inr (.inr .clearBase))) => pop base (fun s b => (s.1, s.2.1,
      s.2.2.1, (s.2.2.2.1, b)))
      (branch (fun s => s.2.2.2.2.isSome)
        (goto (fun _ => .inr (.inr (.inr (.inr .clearBase)))))
        (goto (fun _ => .inr (.inr (.inr (.inr .clearSeed))))))
  | .inr (.inr (.inr (.inr .clearSeed))) => pop seed (fun s b => (s.1, s.2.1,
      s.2.2.1, (s.2.2.2.1, b)))
      (branch (fun s => s.2.2.2.2.isSome)
        (goto (fun _ => .inr (.inr (.inr (.inr .clearSeed)))))
        (goto (fun _ => .inr (.inr (.inr (.inr .copyFinal))))))
  | .inr (.inr (.inr (.inr .copyFinal))) => pop finalWord
      (fun s b => (s.1, s.2.1, s.2.2.1, (s.2.2.2.1, b)))
      (branch (fun s => s.2.2.2.2.isSome)
        (push output (fun s => s.2.2.2.2.getD false)
          (goto (fun _ => .inr (.inr (.inr (.inr .copyFinal))))))
        (load (fun _ => initial) halt))

def cfg (l : Option Label) (s : Control)
    (a y waWord woWord c fuelWord x sx sa stream final q length out : List Bool) : Config :=
  ⟨l, s, Sum.elim
    (WordOutputMachine.cfg none s.1 a y waWord woWord c [] fuelWord x sx sa stream final).stk
    (fun i => if i = 0 then q else if i = 1 then length else out)⟩

def run (t : ℕ) (q : Config) := ((advance program)^[t]) q

private theorem run_add (t u : ℕ) (q : Config) :
    run (t + u) q = run u (run t q) := by
  rw [Nat.add_comm t u]
  simp only [run, Function.iterate_add_apply]

private theorem run_succ {q r : Config} (h : TM2.step program q = some r) (t : ℕ) :
    run (t + 1) q = run t r := by
  simp only [run, Function.iterate_succ_apply, advance, h, Option.getD_some]

theorem split_bank (c q y x sc sq length out : List Bool) :
    BitMachineStackEmbedding.bank splitRegister
      (cfg none initial [] [] [] [] c [] [] [] [] [] [] q length out).stk
      (SamplerMachineFactorSplit.cfg none SamplerMachineFactorSplit.initial
        c q y x sc sq).stk =
    (cfg none initial [] y sc sq c [] x [] [] [] [] q length out).stk := by
  classical
  funext k
  rcases k with ((((k | k) | k) | k) | k) <;> (try fin_cases k)
  all_goals first
    | simpa [cfg, splitRegister, modulus, source, base, seed, wa, wo, inner,
        SamplerMachineFactorSplit.cfg, WordOutputMachine.cfg,
        StreamingBitMachine.cfg, SamplerMachineProduct.cfg]
        using (BitMachineStackEmbedding.bank_at splitRegister
          (cfg none initial [] [] [] [] c [] [] [] [] [] [] q length out).stk
          (SamplerMachineFactorSplit.cfg none SamplerMachineFactorSplit.initial
            c q y x sc sq).stk .candidate)
    | simpa [cfg, splitRegister, modulus, source, base, seed, wa, wo, inner,
        SamplerMachineFactorSplit.cfg, WordOutputMachine.cfg,
        StreamingBitMachine.cfg, SamplerMachineProduct.cfg]
        using (BitMachineStackEmbedding.bank_at splitRegister
          (cfg none initial [] [] [] [] c [] [] [] [] [] [] q length out).stk
          (SamplerMachineFactorSplit.cfg none SamplerMachineFactorSplit.initial
            c q y x sc sq).stk .counter)
    | simpa [cfg, splitRegister, modulus, source, base, seed, wa, wo, inner,
        SamplerMachineFactorSplit.cfg, WordOutputMachine.cfg,
        StreamingBitMachine.cfg, SamplerMachineProduct.cfg]
        using (BitMachineStackEmbedding.bank_at splitRegister
          (cfg none initial [] [] [] [] c [] [] [] [] [] [] q length out).stk
          (SamplerMachineFactorSplit.cfg none SamplerMachineFactorSplit.initial
            c q y x sc sq).stk .factorU)
    | simpa [cfg, splitRegister, modulus, source, base, seed, wa, wo, inner,
        SamplerMachineFactorSplit.cfg, WordOutputMachine.cfg,
        StreamingBitMachine.cfg, SamplerMachineProduct.cfg]
        using (BitMachineStackEmbedding.bank_at splitRegister
          (cfg none initial [] [] [] [] c [] [] [] [] [] [] q length out).stk
          (SamplerMachineFactorSplit.cfg none SamplerMachineFactorSplit.initial
            c q y x sc sq).stk .factorV)
    | simpa [cfg, splitRegister, modulus, source, base, seed, wa, wo, inner,
        SamplerMachineFactorSplit.cfg, WordOutputMachine.cfg,
        StreamingBitMachine.cfg, SamplerMachineProduct.cfg]
        using (BitMachineStackEmbedding.bank_at splitRegister
          (cfg none initial [] [] [] [] c [] [] [] [] [] [] q length out).stk
          (SamplerMachineFactorSplit.cfg none SamplerMachineFactorSplit.initial
            c q y x sc sq).stk .savedC)
    | simpa [cfg, splitRegister, modulus, source, base, seed, wa, wo, inner,
        SamplerMachineFactorSplit.cfg, WordOutputMachine.cfg,
        StreamingBitMachine.cfg, SamplerMachineProduct.cfg]
        using (BitMachineStackEmbedding.bank_at splitRegister
          (cfg none initial [] [] [] [] c [] [] [] [] [] [] q length out).stk
          (SamplerMachineFactorSplit.cfg none SamplerMachineFactorSplit.initial
            c q y x sc sq).stk .savedQ)
    | (rw [BitMachineStackEmbedding.bank_outside splitRegister
        (cfg none initial [] [] [] [] c [] [] [] [] [] [] q length out).stk
        (SamplerMachineFactorSplit.cfg none SamplerMachineFactorSplit.initial
          c q y x sc sq).stk _ (by decide)]; rfl)

theorem split_cfg (l : Option SamplerMachineFactorSplit.Label)
    (s : SamplerMachineFactorSplit.Control)
    (c q y x sc sq length out : List Bool) :
    BitMachineStackEmbedding.cfg splitRegister
      (cfg none initial [] [] [] [] c [] [] [] [] [] [] q length out).stk
      (fun l => .inr (.inl l)) splitEmbed
      (some (.inr (.inr (.inr (.inr .resetSplit)))))
      (SamplerMachineFactorSplit.cfg l s c q y x sc sq) =
    cfg (match l with
      | none => some (.inr (.inr (.inr (.inr .resetSplit))))
      | some l => some (.inr (.inl l)))
      (splitEmbed s) [] y sc sq c [] x [] [] [] [] q length out := by
  cases l <;> dsimp only [BitMachineStackEmbedding.cfg,
    BitMachineStackEmbedding.stackCfg, BitMachineInline.cfg,
    SamplerMachineFactorSplit.cfg, cfg, Option.map_some]
  all_goals congr 1; exact split_bank c q y x sc sq length out

/-- The first stage physically splits the persistent `2d`-bit pair counter.
The lower half is the base `y`, and the upper half is the seed `x`. -/
theorem split_call (d : ℕ) (c y x length out : List Bool)
    (hc : c.length = d) (hy : y.length = d) (hx : x.length = d) :
    ∃ t ≤ 4 * d + 4,
      run t (cfg (some (.inr (.inl .scanU))) initial
        [] [] [] [] c [] [] [] [] [] [] (y ++ x) length out) =
      cfg (some (.inr (.inr (.inr (.inr .resetSplit)))))
        (splitEmbed (SamplerMachineFactorSplit.flags
          (y.tail.any id) (x.tail.any id)))
        [] y [] [] c [] x [] [] [] [] (y ++ x) length out := by
  have hcy : c.length = y.length := hc.trans hy.symm
  have hcx : c.length = x.length := hc.trans hx.symm
  have hr := SamplerMachineFactorSplit.split_run c y x hcy hcx
  have hh :
      (((advance SamplerMachineFactorSplit.program)^[4 * c.length + 4])
        (SamplerMachineFactorSplit.cfg (some .scanU)
          (SamplerMachineFactorSplit.flags false false) c (y ++ x) [] [] [] [])).l = none := by
    change (SamplerMachineFactorSplit.run (4 * c.length + 4)
      (SamplerMachineFactorSplit.cfg (some .scanU)
        (SamplerMachineFactorSplit.flags false false) c (y ++ x) [] [] [] [])).l = none
    rw [hr]
    rfl
  obtain ⟨t, ht, hrun⟩ := BitMachineStackEmbedding.outputs splitRegister
    (cfg none initial [] [] [] [] c [] [] [] [] [] [] (y ++ x) length out).stk
    (fun l => .inr (.inl l)) splitEmbed (fun s => s.2.1) (by intro s; rfl)
    (some (.inr (.inr (.inr (.inr .resetSplit)))))
    SamplerMachineFactorSplit.program program (by intro l; rfl)
    (SamplerMachineFactorSplit.cfg (some .scanU)
      (SamplerMachineFactorSplit.flags false false) c (y ++ x) [] [] [] [])
    (4 * c.length + 4) hh
  dsimp only [SamplerMachineFactorSplit.run] at hr
  rw [hr, split_cfg, split_cfg] at hrun
  refine ⟨t, ?_, hrun⟩
  simpa only [hc] using ht

private theorem step_resetSplit (s : SamplerMachineFactorSplit.Control)
    (c q y x length out : List Bool) :
    TM2.step program (cfg (some (.inr (.inr (.inr (.inr .resetSplit)))))
      (splitEmbed s) [] y [] [] c [] x [] [] [] [] q length out) =
    some (cfg (some (.inr (.inr (.inl .scan)))) initial
      [] y [] [] c [] x [] [] [] [] q length out) := rfl

theorem one_bank (c oldWidth sw tw one y x q length out : List Bool) :
    BitMachineStackEmbedding.bank oneRegister
      (cfg none initial [] y [] [] oldWidth [] x [] [] [] [] q length out).stk
      (OneWordMachine.cfg none OneWordMachine.initial c sw tw one).stk =
    (cfg none initial one y sw tw c [] x [] [] [] [] q length out).stk := by
  classical
  funext k
  rcases k with ((((k | k) | k) | k) | k) <;> (try fin_cases k)
  all_goals first
    | simpa [cfg, oneRegister, modulus, acc, wa, wo, inner,
        OneWordMachine.cfg, WordOutputMachine.cfg,
        StreamingBitMachine.cfg, SamplerMachineProduct.cfg]
        using (BitMachineStackEmbedding.bank_at oneRegister
          (cfg none initial [] y [] [] oldWidth [] x [] [] [] [] q length out).stk
          (OneWordMachine.cfg none OneWordMachine.initial c sw tw one).stk .width)
    | simpa [cfg, oneRegister, modulus, acc, wa, wo, inner,
        OneWordMachine.cfg, WordOutputMachine.cfg,
        StreamingBitMachine.cfg, SamplerMachineProduct.cfg]
        using (BitMachineStackEmbedding.bank_at oneRegister
          (cfg none initial [] y [] [] oldWidth [] x [] [] [] [] q length out).stk
          (OneWordMachine.cfg none OneWordMachine.initial c sw tw one).stk .savedWidth)
    | simpa [cfg, oneRegister, modulus, acc, wa, wo, inner,
        OneWordMachine.cfg, WordOutputMachine.cfg,
        StreamingBitMachine.cfg, SamplerMachineProduct.cfg]
        using (BitMachineStackEmbedding.bank_at oneRegister
          (cfg none initial [] y [] [] oldWidth [] x [] [] [] [] q length out).stk
          (OneWordMachine.cfg none OneWordMachine.initial c sw tw one).stk .tempOne)
    | simpa [cfg, oneRegister, modulus, acc, wa, wo, inner,
        OneWordMachine.cfg, WordOutputMachine.cfg,
        StreamingBitMachine.cfg, SamplerMachineProduct.cfg]
        using (BitMachineStackEmbedding.bank_at oneRegister
          (cfg none initial [] y [] [] oldWidth [] x [] [] [] [] q length out).stk
          (OneWordMachine.cfg none OneWordMachine.initial c sw tw one).stk .one)
    | (rw [BitMachineStackEmbedding.bank_outside oneRegister
        (cfg none initial [] y [] [] oldWidth [] x [] [] [] [] q length out).stk
        (OneWordMachine.cfg none OneWordMachine.initial c sw tw one).stk _ (by decide)]; rfl)

theorem one_cfg (l : Option OneWordMachine.Label) (s : OneWordMachine.Control)
    (c oldWidth sw tw one y x q length out : List Bool) :
    BitMachineStackEmbedding.cfg oneRegister
      (cfg none initial [] y [] [] oldWidth [] x [] [] [] [] q length out).stk
      (fun l => .inr (.inr (.inl l))) oneEmbed
      (some (.inr (.inr (.inr (.inr .resetOne)))))
      (OneWordMachine.cfg l s c sw tw one) =
    cfg (match l with
      | none => some (.inr (.inr (.inr (.inr .resetOne))))
      | some l => some (.inr (.inr (.inl l))))
      (oneEmbed s) one y sw tw c [] x [] [] [] [] q length out := by
  cases l <;> dsimp only [BitMachineStackEmbedding.cfg,
    BitMachineStackEmbedding.stackCfg, BitMachineInline.cfg,
    OneWordMachine.cfg, cfg, Option.map_some]
  all_goals congr 1; exact one_bank c oldWidth sw tw one y x q length out

/-- The second stage constructs the low-first coefficient word `1` from the
nonempty stored modulus word, restoring that modulus. -/
theorem one_call (b : Bool) (width y x q length out : List Bool) :
    ∃ t ≤ 2 * (b :: width).length + 2,
      run t (cfg (some (.inr (.inr (.inl .scan)))) initial
        [] y [] [] (b :: width) [] x [] [] [] [] q length out) =
      cfg (some (.inr (.inr (.inr (.inr .resetOne))))) initial
        (true :: List.replicate width.length false)
        y [] [] (b :: width) [] x [] [] [] [] q length out := by
  have hr := OneWordMachine.run_one b width
  have hh :
      (((advance OneWordMachine.program)^[2 * (b :: width).length + 2])
        (OneWordMachine.cfg (some .scan) OneWordMachine.initial
          (b :: width) [] [] [])).l = none := by
    change (OneWordMachine.run (2 * (b :: width).length + 2)
      (OneWordMachine.cfg (some .scan) OneWordMachine.initial
        (b :: width) [] [] [])).l = none
    rw [hr]
    rfl
  obtain ⟨t, ht, hrun⟩ := BitMachineStackEmbedding.outputs oneRegister
    (cfg none initial [] y [] [] (b :: width) [] x [] [] [] [] q length out).stk
    (fun l => .inr (.inr (.inl l))) oneEmbed (fun s => s.2.2.1)
    (by intro s; rfl)
    (some (.inr (.inr (.inr (.inr .resetOne)))))
    OneWordMachine.program program (by intro l; rfl)
    (OneWordMachine.cfg (some .scan) OneWordMachine.initial
      (b :: width) [] [] [])
    (2 * (b :: width).length + 2) hh
  dsimp only [OneWordMachine.run] at hr
  rw [hr, one_cfg, one_cfg] at hrun
  exact ⟨t, ht, hrun⟩

private theorem step_resetOne (s : OneWordMachine.Control)
    (a c y x q length out : List Bool) :
    TM2.step program (cfg (some (.inr (.inr (.inr (.inr .resetOne)))))
      (oneEmbed s) a y [] [] c [] x [] [] [] [] q length out) =
    some (cfg (some (.inr (.inr (.inr (.inl .scan))))) initial
      a y [] [] c [] x [] [] [] [] q length out) := rfl

theorem fuel_bank (a y c x q oldLength src saved fuelWord out : List Bool) :
    BitMachineStackEmbedding.bank fuelRegister
      (cfg none initial a y [] [] c [] x [] [] [] [] q oldLength out).stk
      (UnaryFuelCopyMachine.cfg none none src saved fuelWord).stk =
    (cfg none initial a y saved [] c fuelWord x [] [] [] [] q src out).stk := by
  classical
  funext k
  rcases k with ((((k | k) | k) | k) | k) <;> (try fin_cases k)
  all_goals first
    | simpa [cfg, fuelRegister, lengthSource, wa, fuel, inner,
        UnaryFuelCopyMachine.cfg, WordOutputMachine.cfg,
        StreamingBitMachine.cfg, SamplerMachineProduct.cfg]
        using (BitMachineStackEmbedding.bank_at fuelRegister
          (cfg none initial a y [] [] c [] x [] [] [] [] q oldLength out).stk
          (UnaryFuelCopyMachine.cfg none none src saved fuelWord).stk 0)
    | simpa [cfg, fuelRegister, lengthSource, wa, fuel, inner,
        UnaryFuelCopyMachine.cfg, WordOutputMachine.cfg,
        StreamingBitMachine.cfg, SamplerMachineProduct.cfg]
        using (BitMachineStackEmbedding.bank_at fuelRegister
          (cfg none initial a y [] [] c [] x [] [] [] [] q oldLength out).stk
          (UnaryFuelCopyMachine.cfg none none src saved fuelWord).stk 1)
    | simpa [cfg, fuelRegister, lengthSource, wa, fuel, inner,
        UnaryFuelCopyMachine.cfg, WordOutputMachine.cfg,
        StreamingBitMachine.cfg, SamplerMachineProduct.cfg]
        using (BitMachineStackEmbedding.bank_at fuelRegister
          (cfg none initial a y [] [] c [] x [] [] [] [] q oldLength out).stk
          (UnaryFuelCopyMachine.cfg none none src saved fuelWord).stk 2)
    | (rw [BitMachineStackEmbedding.bank_outside fuelRegister
        (cfg none initial a y [] [] c [] x [] [] [] [] q oldLength out).stk
        (UnaryFuelCopyMachine.cfg none none src saved fuelWord).stk _ (by decide)]; rfl)

theorem fuel_cfg (l : Option UnaryFuelCopyMachine.Label)
    (s : UnaryFuelCopyMachine.Control)
    (a y c x q oldLength src saved fuelWord out : List Bool) :
    BitMachineStackEmbedding.cfg fuelRegister
      (cfg none initial a y [] [] c [] x [] [] [] [] q oldLength out).stk
      (fun l => .inr (.inr (.inr (.inl l)))) fuelEmbed
      (some (.inr (.inr (.inr (.inr .resetFuel)))))
      (UnaryFuelCopyMachine.cfg l s src saved fuelWord) =
    cfg (match l with
      | none => some (.inr (.inr (.inr (.inr .resetFuel))))
      | some l => some (.inr (.inr (.inr (.inl l)))))
      (fuelEmbed s) a y saved [] c fuelWord x [] [] [] [] q src out := by
  cases l <;> dsimp only [BitMachineStackEmbedding.cfg,
    BitMachineStackEmbedding.stackCfg, BitMachineInline.cfg,
    UnaryFuelCopyMachine.cfg, cfg, Option.map_some]
  all_goals congr 1; exact fuel_bank a y c x q oldLength src saved fuelWord out

theorem fuel_call (a y c x q : List Bool) (n : ℕ) (out : List Bool) :
    ∃ t ≤ 2 * n + 2,
      run t (cfg (some (.inr (.inr (.inr (.inl .scan))))) initial
        a y [] [] c [] x [] [] [] [] q (List.replicate n true) out) =
      cfg (some (.inr (.inr (.inr (.inr .resetFuel)))))
        (fuelEmbed none) a y [] [] c (List.replicate n true)
        x [] [] [] [] q (List.replicate n true) out := by
  have hr := UnaryFuelCopyMachine.run_unary_fuel n
  have hh :
      (((advance UnaryFuelCopyMachine.program)^[2 * n + 2])
        (UnaryFuelCopyMachine.cfg (some .scan) none
          (List.replicate n true) [] [])).l = none := by
    change (UnaryFuelCopyMachine.run (2 * n + 2)
      (UnaryFuelCopyMachine.cfg (some .scan) none
        (List.replicate n true) [] [])).l = none
    rw [hr]
    rfl
  obtain ⟨t, ht, hrun⟩ := BitMachineStackEmbedding.outputs fuelRegister
    (cfg none initial a y [] [] c [] x [] [] [] [] q
      (List.replicate n true) out).stk
    (fun l => .inr (.inr (.inr (.inl l)))) fuelEmbed
    (fun s => s.2.2.2.1) (by intro s; rfl)
    (some (.inr (.inr (.inr (.inr .resetFuel)))))
    UnaryFuelCopyMachine.program program (by intro l; rfl)
    (UnaryFuelCopyMachine.cfg (some .scan) none
      (List.replicate n true) [] [])
    (2 * n + 2) hh
  dsimp only [UnaryFuelCopyMachine.run] at hr
  rw [hr, fuel_cfg, fuel_cfg] at hrun
  exact ⟨t, ht, hrun⟩

private theorem step_resetFuel (s : UnaryFuelCopyMachine.Control)
    (a c y x q length out : List Bool) :
    TM2.step program (cfg (some (.inr (.inr (.inr (.inr .resetFuel)))))
      (fuelEmbed s) a y [] [] c length x [] [] [] [] q length out) =
    some (cfg (some (.inl (.inl (.inr .check)))) initial
      a y [] [] c length x [] [] [] [] q length out) := rfl

def extraInitial : SamplerMachineFactorSplit.Control ×
    (OneWordMachine.Control × (UnaryFuelCopyMachine.Control × Option Bool)) :=
  (SamplerMachineFactorSplit.initial, (OneWordMachine.initial, (none, none)))

theorem word_cfg (l : Option WordOutputMachine.Label)
    (s : WordOutputMachine.Control)
    (a y waWord woWord c fuelWord x sx sa stream final q length out : List Bool) :
    liftCfg
      (some (.inr (.inr (.inr .clearAcc)))) extraInitial
      (fun i : Fin 3 => if i = 0 then q else if i = 1 then length else out)
      (WordOutputMachine.cfg l s a y waWord woWord c [] fuelWord x sx sa stream final) =
    cfg (match l with
      | none => some (.inr (.inr (.inr (.inr .clearAcc))))
      | some l => some (.inl l))
      (s, extraInitial) a y waWord woWord c fuelWord x sx sa stream final q length out := by
  cases l <;> rfl

/-- The already checked ordered one-seed printer is an actual subroutine of
the callback controller, with the pair counter, length source, and global
output bank framed. -/
theorem word_call (d tail n : ℕ)
    (htail : tail < 2 ^ d) (hd : 0 < d)
    (x y : Fin (2 ^ d)) (q out : List Bool) :
    let modulus := CurrentAdditive.FiniteFieldConstructor.TrialSearch.monicBits d tail
    let c := HornerNatBridge.lowerWord d modulus
    ∃ t ≤ n * (d * (4 * d + 5) + 4 * d + 7) + 2,
      run t (cfg (some (.inl (.inl (.inr .check)))) initial
        (SamplerMachine.encodeWord (CurrentAdditive.FiniteFieldConstructor.BitPolynomialBridge.xBits d
          ⟨1, Nat.one_lt_two_pow (by omega : d ≠ 0)⟩))
        (SamplerMachine.encodeWord (CurrentAdditive.FiniteFieldConstructor.BitPolynomialBridge.xBits d y)) [] []
        (SamplerMachine.encodeWord c) (List.replicate n true)
        (SamplerMachine.encodeWord (CurrentAdditive.FiniteFieldConstructor.BitPolynomialBridge.xBits d x))
        [] [] [] [] q (List.replicate n true) out) =
      cfg (some (.inr (.inr (.inr (.inr .clearAcc))))) initial
        (SamplerMachine.encodeWord (CurrentAdditive.FiniteFieldConstructor.BitPolynomialBridge.xBits d
          ⟨CurrentAdditive.FiniteFieldConstructor.BitPrinter.power d modulus y.val n,
            CurrentAdditive.FiniteFieldConstructor.BitPolynomialBridge.power_lt d modulus y.val n hd
              (CurrentAdditive.FiniteFieldConstructor.BitPolynomialBridge.monicBits_lt
                d tail htail)
              (CurrentAdditive.FiniteFieldConstructor.BitPolynomialBridge.monicBits_topBit
                d tail htail) y.isLt⟩))
        (SamplerMachine.encodeWord (CurrentAdditive.FiniteFieldConstructor.BitPolynomialBridge.xBits d y)) [] []
        (SamplerMachine.encodeWord c) []
        (SamplerMachine.encodeWord (CurrentAdditive.FiniteFieldConstructor.BitPolynomialBridge.xBits d x))
        [] [] []
        (CurrentAdditive.FiniteFieldConstructor.BitPrinter.word d modulus n x.val y.val)
        q (List.replicate n true) out := by
  intro modulus c
  obtain ⟨t, ht, hr⟩ := WordOutputMachine.run_bitPrinter_word_ordered
    d tail n htail hd x y
  have hh :
      (WordOutputMachine.run t (WordOutputMachine.cfg
        (some (.inl (.inr .check))) WordOutputMachine.initial
        (SamplerMachine.encodeWord (CurrentAdditive.FiniteFieldConstructor.BitPolynomialBridge.xBits d
          ⟨1, Nat.one_lt_two_pow (by omega : d ≠ 0)⟩))
        (SamplerMachine.encodeWord (CurrentAdditive.FiniteFieldConstructor.BitPolynomialBridge.xBits d y)) [] []
        (SamplerMachine.encodeWord c) []
        (List.replicate n true)
        (SamplerMachine.encodeWord (CurrentAdditive.FiniteFieldConstructor.BitPolynomialBridge.xBits d x))
        [] [] [] [])).l = none := by
    rw [hr]
    rfl
  obtain ⟨t', ht', hrun⟩ := BitMachineSubroutine.lift_outputs
    WordOutputMachine.program program
    (some (.inr (.inr (.inr .clearAcc)))) (fun _ => rfl)
    extraInitial
    (fun i : Fin 3 => if i = 0 then q else if i = 1 then List.replicate n true else out)
    (WordOutputMachine.cfg (some (.inl (.inr .check))) WordOutputMachine.initial
      (SamplerMachine.encodeWord (CurrentAdditive.FiniteFieldConstructor.BitPolynomialBridge.xBits d
        ⟨1, Nat.one_lt_two_pow (by omega : d ≠ 0)⟩))
      (SamplerMachine.encodeWord (CurrentAdditive.FiniteFieldConstructor.BitPolynomialBridge.xBits d y)) [] []
      (SamplerMachine.encodeWord c) []
      (List.replicate n true)
      (SamplerMachine.encodeWord (CurrentAdditive.FiniteFieldConstructor.BitPolynomialBridge.xBits d x))
      [] [] [] []) t hh
  dsimp only [WordOutputMachine.run] at hr
  rw [hr, word_cfg, word_cfg] at hrun
  exact ⟨t', ht'.trans ht, hrun⟩

def admin (a : Admin) : Label := .inr (.inr (.inr (.inr a)))
def readControl (s : Control) (b : Option Bool) : Control :=
  (s.1, s.2.1, s.2.2.1, (s.2.2.2.1, b))

private theorem step_clearAcc_cons (s : Control) (b : Bool)
    (a y c fuelWord x final q length out : List Bool) :
    TM2.step program (cfg (some (admin .clearAcc)) s
      (b :: a) y [] [] c fuelWord x [] [] [] final q length out) =
    some (cfg (some (admin .clearAcc)) (readControl s (some b))
      a y [] [] c fuelWord x [] [] [] final q length out) := by
  dsimp only [TM2.step, TM2.stepAux, program, admin, acc, readControl,
    cfg, inner, WordOutputMachine.cfg, StreamingBitMachine.cfg,
    StreamingBitMachine.foreign, SamplerMachineProduct.cfg,
    SamplerMachineProduct.foreign, SamplerMachineAccumulate.stackContents,
    StreamingBitMachine.acc, Sum.elim_inl, Sum.elim_inr]
  simp only [show (1 : Fin 4) ≠ 0 by decide, if_neg,
    ↓reduceIte, List.head?_cons, List.tail_cons, Option.isSome_some,
    Bool.cond_true, Option.some.injEq]
  congr 1
  funext k
  rcases k with ((((k | k) | k) | k) | k) <;> (try fin_cases k) <;> rfl

private theorem step_clearAcc_nil (s : Control)
    (y c fuelWord x final q length out : List Bool) :
    TM2.step program (cfg (some (admin .clearAcc)) s
      [] y [] [] c fuelWord x [] [] [] final q length out) =
    some (cfg (some (admin .clearBase)) (readControl s none)
      [] y [] [] c fuelWord x [] [] [] final q length out) := by
  dsimp only [TM2.step, TM2.stepAux, program, admin, acc, readControl,
    cfg, inner, WordOutputMachine.cfg, StreamingBitMachine.cfg,
    StreamingBitMachine.foreign, SamplerMachineProduct.cfg,
    SamplerMachineProduct.foreign, SamplerMachineAccumulate.stackContents,
    StreamingBitMachine.acc, Sum.elim_inl, Sum.elim_inr]
  simp only [show (1 : Fin 4) ≠ 0 by decide, if_neg,
    ↓reduceIte, List.head?_nil, List.tail_nil, Option.isSome_none,
    Bool.cond_false, Option.some.injEq]
  congr 1
  funext k
  rcases k with ((((k | k) | k) | k) | k) <;> (try fin_cases k) <;> rfl

theorem clearAcc_run (s : Control)
    (a y c fuelWord x final q length out : List Bool) :
    run (a.length + 1) (cfg (some (admin .clearAcc)) s
      a y [] [] c fuelWord x [] [] [] final q length out) =
    cfg (some (admin .clearBase)) (readControl s none)
      [] y [] [] c fuelWord x [] [] [] final q length out := by
  induction a generalizing s with
  | nil => simpa using (run_succ
      (step_clearAcc_nil s y c fuelWord x final q length out) 0)
  | cons b a ih =>
      rw [List.length_cons, run_succ
        (step_clearAcc_cons s b a y c fuelWord x final q length out)]
      exact ih (readControl s (some b))

private theorem step_clearBase_cons (s : Control) (b : Bool)
    (y c fuelWord x final q length out : List Bool) :
    TM2.step program (cfg (some (admin .clearBase)) s
      [] (b :: y) [] [] c fuelWord x [] [] [] final q length out) =
    some (cfg (some (admin .clearBase)) (readControl s (some b))
      [] y [] [] c fuelWord x [] [] [] final q length out) := by
  dsimp only [TM2.step, TM2.stepAux, program, admin, base, readControl,
    cfg, inner, WordOutputMachine.cfg, StreamingBitMachine.cfg,
    StreamingBitMachine.foreign, SamplerMachineProduct.cfg,
    SamplerMachineProduct.foreign, SamplerMachineAccumulate.stackContents,
    StreamingBitMachine.base, Sum.elim_inl, Sum.elim_inr]
  simp only [show (1 : Fin 4) ≠ 0 by decide, if_neg,
    ↓reduceIte, List.head?_cons, List.tail_cons, Option.isSome_some,
    Bool.cond_true, Option.some.injEq]
  congr 1
  funext k
  rcases k with ((((k | k) | k) | k) | k) <;> (try fin_cases k) <;> rfl

private theorem step_clearBase_nil (s : Control)
    (c fuelWord x final q length out : List Bool) :
    TM2.step program (cfg (some (admin .clearBase)) s
      [] [] [] [] c fuelWord x [] [] [] final q length out) =
    some (cfg (some (admin .clearSeed)) (readControl s none)
      [] [] [] [] c fuelWord x [] [] [] final q length out) := by
  dsimp only [TM2.step, TM2.stepAux, program, admin, base, readControl,
    cfg, inner, WordOutputMachine.cfg, StreamingBitMachine.cfg,
    StreamingBitMachine.foreign, SamplerMachineProduct.cfg,
    SamplerMachineProduct.foreign, SamplerMachineAccumulate.stackContents,
    StreamingBitMachine.base, Sum.elim_inl, Sum.elim_inr]
  simp only [show (1 : Fin 4) ≠ 0 by decide, if_neg,
    ↓reduceIte, List.head?_nil, List.tail_nil, Option.isSome_none,
    Bool.cond_false, Option.some.injEq]
  congr 1
  funext k
  rcases k with ((((k | k) | k) | k) | k) <;> (try fin_cases k) <;> rfl

theorem clearBase_run (s : Control)
    (y c fuelWord x final q length out : List Bool) :
    run (y.length + 1) (cfg (some (admin .clearBase)) s
      [] y [] [] c fuelWord x [] [] [] final q length out) =
    cfg (some (admin .clearSeed)) (readControl s none)
      [] [] [] [] c fuelWord x [] [] [] final q length out := by
  induction y generalizing s with
  | nil => simpa using (run_succ
      (step_clearBase_nil s c fuelWord x final q length out) 0)
  | cons b y ih =>
      rw [List.length_cons, run_succ
        (step_clearBase_cons s b y c fuelWord x final q length out)]
      exact ih (readControl s (some b))

private theorem step_clearSeed_cons (s : Control) (b : Bool)
    (c fuelWord x final q length out : List Bool) :
    TM2.step program (cfg (some (admin .clearSeed)) s
      [] [] [] [] c fuelWord (b :: x) [] [] [] final q length out) =
    some (cfg (some (admin .clearSeed)) (readControl s (some b))
      [] [] [] [] c fuelWord x [] [] [] final q length out) := by
  dsimp only [TM2.step, TM2.stepAux, program, admin, seed, readControl,
    cfg, inner, WordOutputMachine.cfg, StreamingBitMachine.cfg,
    StreamingBitMachine.foreign, SamplerMachineProduct.cfg,
    SamplerMachineProduct.foreign, SamplerMachineAccumulate.stackContents,
    StreamingBitMachine.seed, Sum.elim_inl, Sum.elim_inr]
  simp only [show (1 : Fin 5) ≠ 0 by decide, if_neg,
    ↓reduceIte, List.head?_cons, List.tail_cons, Option.isSome_some,
    Bool.cond_true, Option.some.injEq]
  congr 1
  funext k
  rcases k with ((((k | k) | k) | k) | k) <;> (try fin_cases k) <;> rfl

private theorem step_clearSeed_nil (s : Control)
    (c fuelWord final q length out : List Bool) :
    TM2.step program (cfg (some (admin .clearSeed)) s
      [] [] [] [] c fuelWord [] [] [] [] final q length out) =
    some (cfg (some (admin .copyFinal)) (readControl s none)
      [] [] [] [] c fuelWord [] [] [] [] final q length out) := by
  dsimp only [TM2.step, TM2.stepAux, program, admin, seed, readControl,
    cfg, inner, WordOutputMachine.cfg, StreamingBitMachine.cfg,
    StreamingBitMachine.foreign, SamplerMachineProduct.cfg,
    SamplerMachineProduct.foreign, SamplerMachineAccumulate.stackContents,
    StreamingBitMachine.seed, Sum.elim_inl, Sum.elim_inr]
  simp only [show (1 : Fin 5) ≠ 0 by decide, if_neg,
    ↓reduceIte, List.head?_nil, List.tail_nil, Option.isSome_none,
    Bool.cond_false, Option.some.injEq]
  congr 1
  funext k
  rcases k with ((((k | k) | k) | k) | k) <;> (try fin_cases k) <;> rfl

theorem clearSeed_run (s : Control)
    (c fuelWord x final q length out : List Bool) :
    run (x.length + 1) (cfg (some (admin .clearSeed)) s
      [] [] [] [] c fuelWord x [] [] [] final q length out) =
    cfg (some (admin .copyFinal)) (readControl s none)
      [] [] [] [] c fuelWord [] [] [] [] final q length out := by
  induction x generalizing s with
  | nil => simpa using (run_succ
      (step_clearSeed_nil s c fuelWord final q length out) 0)
  | cons b x ih =>
      rw [List.length_cons, run_succ
        (step_clearSeed_cons s b c fuelWord x final q length out)]
      exact ih (readControl s (some b))

private theorem step_copyFinal_cons (s : Control) (b : Bool)
    (c fuelWord final q length out : List Bool) :
    TM2.step program (cfg (some (admin .copyFinal)) s
      [] [] [] [] c fuelWord [] [] [] [] (b :: final) q length out) =
    some (cfg (some (admin .copyFinal)) (readControl s (some b))
      [] [] [] [] c fuelWord [] [] [] [] final q length (b :: out)) := by
  dsimp only [TM2.step, TM2.stepAux, program, admin, finalWord, output,
    readControl, cfg, WordOutputMachine.cfg, WordOutputMachine.finalWord,
    Sum.elim_inl, Sum.elim_inr]
  simp only [show (2 : Fin 3) ≠ 0 by decide,
    show (2 : Fin 3) ≠ 1 by decide, if_neg, ↓reduceIte,
    List.head?_cons, List.tail_cons, Option.isSome_some,
    Option.getD_some, Bool.cond_true, Option.some.injEq]
  congr 1
  funext k
  rcases k with ((((k | k) | k) | k) | k) <;> (try fin_cases k) <;> rfl

private theorem step_copyFinal_nil (s : Control)
    (c fuelWord q length out : List Bool) :
    TM2.step program (cfg (some (admin .copyFinal)) s
      [] [] [] [] c fuelWord [] [] [] [] [] q length out) =
    some (cfg none initial
      [] [] [] [] c fuelWord [] [] [] [] [] q length out) := by
  dsimp only [TM2.step, TM2.stepAux, program, admin, finalWord, output,
    readControl, cfg, WordOutputMachine.cfg, WordOutputMachine.finalWord,
    Sum.elim_inl, Sum.elim_inr]
  simp only [show (2 : Fin 3) ≠ 0 by decide,
    show (2 : Fin 3) ≠ 1 by decide, if_neg, ↓reduceIte,
    List.head?_nil, List.tail_nil, Option.isSome_none,
    Bool.cond_false, Option.some.injEq]
  congr 1
  funext k
  rcases k with ((((k | k) | k) | k) | k) <;> (try fin_cases k) <;> rfl

/-- Draining the normal-order word to the global stack prepends its reverse,
which is the counter mapper's required callback payload convention. -/
theorem copyFinal_run (s : Control)
    (c fuelWord final q length out : List Bool) :
    run (final.length + 1) (cfg (some (admin .copyFinal)) s
      [] [] [] [] c fuelWord [] [] [] [] final q length out) =
    cfg none initial [] [] [] [] c fuelWord [] [] [] [] [] q length
      (final.reverse ++ out) := by
  induction final generalizing s out with
  | nil => simpa using (run_succ
      (step_copyFinal_nil s c fuelWord q length out) 0)
  | cons b final ih =>
      rw [List.length_cons, run_succ
        (step_copyFinal_cons s b c fuelWord final q length out)]
      simpa only [List.reverse_cons, List.append_assoc,
        List.singleton_append] using
        ih (readControl s (some b)) (b :: out)

theorem cleanup_run (s : Control)
    (a y c x final q length out : List Bool) :
    run (a.length + y.length + x.length + final.length + 4)
      (cfg (some (admin .clearAcc)) s
        a y [] [] c [] x [] [] [] final q length out) =
    cfg none initial [] [] [] [] c [] [] [] [] [] [] q length
      (final.reverse ++ out) := by
  have ha := clearAcc_run s a y c [] x final q length out
  have hy := clearBase_run (readControl s none) y c [] x final q length out
  have hx := clearSeed_run (readControl (readControl s none) none)
    c [] x final q length out
  have hf := copyFinal_run
    (readControl (readControl (readControl s none) none) none)
    c [] final q length out
  have ht : a.length + y.length + x.length + final.length + 4 =
      (a.length + 1) + ((y.length + 1) +
        ((x.length + 1) + (final.length + 1))) := by omega
  rw [ht, run_add, ha, run_add, hy, run_add, hx, hf]

private theorem bitsValue_falseWord (n : ℕ) :
    EncodedCommunication.bitsValue (List.replicate n false) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp [List.replicate_succ, EncodedCommunication.bitsValue, ih]

theorem one_encoding (d : ℕ) (hd : 0 < d) :
    true :: List.replicate (d - 1) false =
      SamplerMachine.encodeWord
        (CurrentAdditive.FiniteFieldConstructor.BitPolynomialBridge.xBits d
          ⟨1, Nat.one_lt_two_pow (by omega : d ≠ 0)⟩) := by
  cases d with
  | zero => omega
  | succ k =>
      have hv : EncodedCommunication.bitsValue
          (true :: List.replicate k false) = 1 := by
        simp [EncodedCommunication.bitsValue, bitsValue_falseWord]
      have hn := CounterNatBridge.natBits_bitsValue
        (true :: List.replicate k false)
      simp only [List.length_cons, List.length_replicate, hv] at hn
      simpa only [Nat.add_sub_cancel_left, StreamingBitMachine.encodeWord_xBits]
        using hn.symm

theorem one_call_width (d : ℕ) (hd : 0 < d)
    (c y x q length out : List Bool) (hc : c.length = d) :
    ∃ t ≤ 2 * d + 2,
      run t (cfg (some (.inr (.inr (.inl .scan)))) initial
        [] y [] [] c [] x [] [] [] [] q length out) =
      cfg (some (admin .resetOne)) initial
        (SamplerMachine.encodeWord
          (CurrentAdditive.FiniteFieldConstructor.BitPolynomialBridge.xBits d
            ⟨1, Nat.one_lt_two_pow (by omega : d ≠ 0)⟩))
        y [] [] c [] x [] [] [] [] q length out := by
  cases c with
  | nil => simp at hc; omega
  | cons b width =>
      obtain ⟨t, ht, hr⟩ := one_call b width y x q length out
      have hw : width.length = d - 1 := by simp at hc; omega
      rw [hw, one_encoding d hd] at hr
      exact ⟨t, by simpa only [hc] using ht, hr⟩

def callbackBound (d n : ℕ) : ℕ :=
  n * (d * (4 * d + 5) + 4 * d + 7) + 9 * d + 3 * n + 17

/-- A complete physical callback for one pair counter. The only prepared
inputs are the lower d coefficient bits of a monic modulus, the persistent
pair counter, and an already supplied unary length word. -/
theorem run_seed_callback (d tail n : ℕ)
    (htail : tail < 2 ^ d) (hd : 0 < d)
    (x y : Fin (2 ^ d)) (out : List Bool) :
    let modulus := CurrentAdditive.FiniteFieldConstructor.TrialSearch.monicBits d tail
    let c := SamplerMachine.encodeWord (HornerNatBridge.lowerWord d modulus)
    let yBits := SamplerMachine.encodeWord
      (CurrentAdditive.FiniteFieldConstructor.BitPolynomialBridge.xBits d y)
    let xBits := SamplerMachine.encodeWord
      (CurrentAdditive.FiniteFieldConstructor.BitPolynomialBridge.xBits d x)
    let q := yBits ++ xBits
    ∃ t ≤ callbackBound d n,
      run t (cfg (some (.inr (.inl .scanU))) initial
        [] [] [] [] c [] [] [] [] [] [] q (List.replicate n true) out) =
      cfg none initial [] [] [] [] c [] [] [] [] [] [] q
        (List.replicate n true)
        ((CurrentAdditive.FiniteFieldConstructor.BitPrinter.word
          d modulus n x.val y.val).reverse ++ out) := by
  intro modulus c yBits xBits q
  have hc : c.length = d := by simp [c]
  have hy : yBits.length = d := by simp [yBits]
  have hx : xBits.length = d := by simp [xBits]
  have hq : q = yBits ++ xBits := rfl
  obtain ⟨ts, hts, hs⟩ := split_call d c yBits xBits
    (List.replicate n true) out hc hy hx
  have hresetS :
      run 1 (cfg (some (admin .resetSplit))
        (splitEmbed (SamplerMachineFactorSplit.flags
          (yBits.tail.any id) (xBits.tail.any id)))
        [] yBits [] [] c [] xBits [] [] [] [] q (List.replicate n true) out) =
      cfg (some (.inr (.inr (.inl .scan)))) initial
        [] yBits [] [] c [] xBits [] [] [] [] q (List.replicate n true) out := by
    simpa [run] using (run_succ
      (step_resetSplit
        (SamplerMachineFactorSplit.flags (yBits.tail.any id) (xBits.tail.any id))
        c q yBits xBits (List.replicate n true) out) 0)
  obtain ⟨tOne, htOne, ho⟩ := one_call_width d hd c yBits xBits q
    (List.replicate n true) out hc
  have hresetO :
      run 1 (cfg (some (admin .resetOne)) initial
        (SamplerMachine.encodeWord
          (CurrentAdditive.FiniteFieldConstructor.BitPolynomialBridge.xBits d
            ⟨1, Nat.one_lt_two_pow (by omega : d ≠ 0)⟩))
        yBits [] [] c [] xBits [] [] [] [] q (List.replicate n true) out) =
      cfg (some (.inr (.inr (.inr (.inl .scan))))) initial
        (SamplerMachine.encodeWord
          (CurrentAdditive.FiniteFieldConstructor.BitPolynomialBridge.xBits d
            ⟨1, Nat.one_lt_two_pow (by omega : d ≠ 0)⟩))
        yBits [] [] c [] xBits [] [] [] [] q (List.replicate n true) out := by
    simpa [run, oneEmbed, initial] using (run_succ
      (step_resetOne OneWordMachine.initial
        (SamplerMachine.encodeWord
          (CurrentAdditive.FiniteFieldConstructor.BitPolynomialBridge.xBits d
            ⟨1, Nat.one_lt_two_pow (by omega : d ≠ 0)⟩))
        c yBits xBits q (List.replicate n true) out) 0)
  obtain ⟨tf, htf, hf⟩ := fuel_call
    (SamplerMachine.encodeWord
      (CurrentAdditive.FiniteFieldConstructor.BitPolynomialBridge.xBits d
        ⟨1, Nat.one_lt_two_pow (by omega : d ≠ 0)⟩))
    yBits c xBits q n out
  have hresetF :
      run 1 (cfg (some (admin .resetFuel)) (fuelEmbed none)
        (SamplerMachine.encodeWord
          (CurrentAdditive.FiniteFieldConstructor.BitPolynomialBridge.xBits d
            ⟨1, Nat.one_lt_two_pow (by omega : d ≠ 0)⟩))
        yBits [] [] c (List.replicate n true) xBits [] [] [] [] q
        (List.replicate n true) out) =
      cfg (some (.inl (.inl (.inr .check)))) initial
        (SamplerMachine.encodeWord
          (CurrentAdditive.FiniteFieldConstructor.BitPolynomialBridge.xBits d
            ⟨1, Nat.one_lt_two_pow (by omega : d ≠ 0)⟩))
        yBits [] [] c (List.replicate n true) xBits [] [] [] [] q
        (List.replicate n true) out := by
    simpa [run, initial, fuelEmbed] using (run_succ
      (step_resetFuel none
        (SamplerMachine.encodeWord
          (CurrentAdditive.FiniteFieldConstructor.BitPolynomialBridge.xBits d
            ⟨1, Nat.one_lt_two_pow (by omega : d ≠ 0)⟩))
        c yBits xBits q (List.replicate n true) out) 0)
  obtain ⟨tw, htw, hw⟩ := word_call d tail n htail hd x y q out
  let finalAcc := SamplerMachine.encodeWord
    (CurrentAdditive.FiniteFieldConstructor.BitPolynomialBridge.xBits d
      ⟨CurrentAdditive.FiniteFieldConstructor.BitPrinter.power d modulus y.val n,
        CurrentAdditive.FiniteFieldConstructor.BitPolynomialBridge.power_lt
          d modulus y.val n hd
          (CurrentAdditive.FiniteFieldConstructor.BitPolynomialBridge.monicBits_lt
            d tail htail)
          (CurrentAdditive.FiniteFieldConstructor.BitPolynomialBridge.monicBits_topBit
            d tail htail) y.isLt⟩)
  let finalWord := CurrentAdditive.FiniteFieldConstructor.BitPrinter.word
    d modulus n x.val y.val
  have hca : finalAcc.length = d := by simp [finalAcc]
  have hcw : finalWord.length = n := by
    simpa [finalWord] using
      CurrentAdditive.FiniteFieldConstructor.BitPrinter.word_length
        d modulus n x.val y.val
  have hclean := cleanup_run initial finalAcc yBits c xBits finalWord q
    (List.replicate n true) out
  rw [hca, hy, hx, hcw] at hclean
  have heq : ts + 1 + tOne + 1 + tf + 1 + tw + (3 * d + n + 4) =
      ts + (1 + (tOne + (1 + (tf + (1 + (tw + (3 * d + n + 4))))))) := by omega
  refine ⟨ts + 1 + tOne + 1 + tf + 1 + tw + (3 * d + n + 4), ?_, ?_⟩
  · unfold callbackBound
    omega
  · simp only [hq] at hresetS ho hresetO hf hresetF hw hclean ⊢
    simp only [admin] at hresetS ho hresetO hf hresetF hclean
    rw [heq, run_add, hs, run_add, hresetS,
      run_add, ho, run_add, hresetO,
      run_add, hf, run_add, hresetF,
      run_add, hw]
    rw [show 3 * d + n + 4 = d + d + d + n + 4 by omega, hclean]

#print axioms run_seed_callback

end CurrentAdditive.FiniteFieldMachine.SeedCallbackMachine
