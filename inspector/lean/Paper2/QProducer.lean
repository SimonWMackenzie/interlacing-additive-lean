import Paper2.QIdent
import EthInapproximability.CurrentPaper.MatrixStage4ScalarPreparationOps
import EthInapproximability.CurrentPaper.MatrixUnaryDivision
import EthInapproximability.CurrentPaper.ETHParameterScaleMachineLogCopy
import EthInapproximability.CurrentPaper.ETHParameterScaleMachineMax
import EthInapproximability.CurrentPaper.BitMachineRawSequence
import EthInapproximability.CurrentPaper.BitMachineStackRun

/-! Unit 3, segment (1): a physical producer of the unary public cover width
`Q = ParameterizedCanonicalSource.coverWidth n m L Δ γ` (value identity `QIdent.coverWidth_eq`).

Machine parameters (fixed per machine): `a`, `b` (at H-A3: `a = γ.num.toNat`, `b = γ.den`) and `Δ`.
Inputs: unary `n`, `m`, `L`, `s`, `w` in cells 0-4 (at H-A3: `s = width L`, `w = restorationWidth L`,
both produced by the admitted-candidate `LProducer`; `n`, `m` from the graph bytes).

Bank `QK = Fin 29 ⊕ LS`, `LS = ETHParameterScaleMachineLogCopy.Stack`. ONE fixed program `qProg`
(twenty-three parts, production `BitMachineRawSequence` handoffs):
single-step pushes of machine constants (24, 5, `2bΔ`, `a`, `6144 b`, `a - 1`); admitted
`MatrixStage4ScalarPreparationOps.unaryPowerProgram` (twice); admitted `multiplyProgram` (eight times);
admitted `copyProgram`; one pop step; admitted `MatrixUnaryDivision.program` (total form, twice);
admitted `ETHParameterScaleMachineMax.program` (twice, embedded by `stackStmt`); admitted
`ETHParameterScaleMachineLogCopy.program` (copy-then-clog). -/

set_option maxHeartbeats 16000000
set_option maxRecDepth 16384
set_option linter.unusedSimpArgs false

namespace Paper2.QProducer

noncomputable section

open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper.BitMachineStackEmbedding
open BitMachineRawSequence (leftLabel)

abbrev LS := ETHParameterScaleMachineLogCopy.Stack
abbrev QK := Fin 29 ⊕ LS

def u (n : ℕ) : List Bool := List.replicate n true

-- cells: 0 n, 1 m, 2 L, 3 s, 4 w, 5 u24, 6 2^24, 7 Lw, 8 Lws, 9 Lws2^24, 10 u5, 11 C0, 12 K1 = 2bΔ,
-- 13 C0 K1, 14 N2 (dividend), 15 a, 16 D2 = a m, 17 rem2, 18 A2, 19 K3 = 6144 b, 20 N3 (dividend),
-- 21 rem3, 22 A3, 23 max C0 A2, 24 Q, 25-27 arithmetic scratch, 28 copy scratch

def srcL : QK := .inr (.inl 0)
def outL : QK := .inr (ETHParameterScaleMachineLogCopy.logStack
  ETHParameterScaleMachineLogCopy.logMachine.output)

def ιL : LS ↪ QK := ⟨Sum.inr, fun _ _ h => Sum.inr_injective h⟩
def ιI : Fin 29 ↪ QK := ⟨Sum.inl, fun _ _ h => Sum.inl_injective h⟩

def e6 (v : Fin 6 → Fin 29) (h : Function.Injective v) : Fin 6 ↪ QK := (⟨v, h⟩ : Fin 6 ↪ Fin 29).trans ιI
def e3 (v : Fin 3 → Fin 29) (h : Function.Injective v) : Fin 3 ↪ QK := (⟨v, h⟩ : Fin 3 ↪ Fin 29).trans ιI
def e5 (v : Fin 5 → Fin 29) (h : Function.Injective v) : Fin 5 ↪ QK := (⟨v, h⟩ : Fin 5 ↪ Fin 29).trans ιI

def ιM1 : Fin 6 ↪ QK := e6 ![2, 4, 25, 26, 27, 7] (by decide)
def ιM2 : Fin 6 ↪ QK := e6 ![7, 3, 25, 26, 27, 8] (by decide)
def ιM3 : Fin 6 ↪ QK := e6 ![8, 6, 25, 26, 27, 9] (by decide)
def ιM4 : Fin 6 ↪ QK := e6 ![9, 10, 25, 26, 27, 11] (by decide)
def ιM5 : Fin 6 ↪ QK := e6 ![11, 12, 25, 26, 27, 13] (by decide)
def ιM6 : Fin 6 ↪ QK := e6 ![13, 0, 25, 26, 27, 14] (by decide)
def ιM7 : Fin 6 ↪ QK := e6 ![15, 1, 25, 26, 27, 16] (by decide)
def ιM8 : Fin 6 ↪ QK := e6 ![11, 19, 25, 26, 27, 20] (by decide)
def ιC1 : Fin 3 ↪ QK := e3 ![16, 14, 28] (by decide)
def ιD1 : Fin 6 ↪ QK := e6 ![14, 16, 25, 17, 18, 26] (by decide)
def ιD2 : Fin 6 ↪ QK := e6 ![20, 15, 25, 21, 22, 26] (by decide)
def ιX1 : Fin 5 ↪ QK := e5 ![11, 18, 25, 26, 23] (by decide)

def xF2 : Fin 5 → QK := ![.inl 23, .inl 22, .inl 25, .inl 26, srcL]
def ιX2 : Fin 5 ↪ QK := ⟨xF2, by
  intro x y h
  fin_cases x <;> fin_cases y <;> simp_all [xF2, srcL]⟩

def powF1 : MatrixUnaryPower.Stack → QK
  | .inl 0 => .inl 6
  | .inl 1 => .inl 25
  | .inl _ => .inl 26
  | .inr () => .inl 5

def ιP1 : MatrixUnaryPower.Stack ↪ QK := ⟨powF1, by
  intro x y h
  rcases x with x | x <;> rcases y with y | y
  · fin_cases x <;> fin_cases y <;> simp_all [powF1]
  · cases y; fin_cases x <;> simp_all [powF1]
  · cases x; fin_cases y <;> simp_all [powF1]
  · cases x; cases y; rfl⟩

def powF2 : MatrixUnaryPower.Stack → QK
  | .inl 0 => .inl 24
  | .inl 1 => .inl 25
  | .inl _ => .inl 26
  | .inr () => outL

def ιP2 : MatrixUnaryPower.Stack ↪ QK := ⟨powF2, by
  intro x y h
  rcases x with x | x <;> rcases y with y | y
  · fin_cases x <;> fin_cases y <;> simp_all [powF2]
  · cases y; fin_cases x <;> simp_all [powF2, outL]
  · cases x; fin_cases y <;> simp_all [powF2, outL]
  · cases x; cases y; rfl⟩

/-! ### Embedded admitted machines -/

def divProgram (ι : Fin 6 ↪ QK) :
    MatrixUnaryDivision.Label → TM2.Stmt (fun _ : QK => Bool) MatrixUnaryDivision.Label Bool :=
  fun l => stackStmt ι (MatrixUnaryDivision.program l)

theorem div_run (ι : Fin 6 ↪ QK) (S : QK → List Bool) (n m : ℕ)
    (h0 : S (ι 0) = u n) (h1 : S (ι 1) = u m) (h2 : S (ι 2) = []) (h3 : S (ι 3) = [])
    (h4 : S (ι 4) = []) (h5 : S (ι 5) = []) :
    ((advance (divProgram ι))^[MatrixUnaryDivision.totalTime n m])
        (⟨some .start, false, S⟩ : TM2.Cfg (fun _ : QK => Bool) MatrixUnaryDivision.Label Bool) =
      ⟨none, false, Function.update (Function.update (Function.update S (ι 0) []) (ι 3)
        (u (n % m))) (ι 4) (u (n / m))⟩ := by
  let c := MatrixUnaryDivision.cfg (some .start) false (u n) (u m) [] [] [] []
  have hstart : stackCfg ι S c =
      (⟨some .start, false, S⟩ : TM2.Cfg (fun _ : QK => Bool) MatrixUnaryDivision.Label Bool) := by
    dsimp [stackCfg, c, MatrixUnaryDivision.cfg]
    congr 1
    apply bank_eq_self
    intro k
    fin_cases k <;> simp [h0, h1, h2, h3, h4, h5]
  have hrun := BitMachineStackRun.run ι S MatrixUnaryDivision.program c
    (MatrixUnaryDivision.totalTime n m)
  rw [hstart] at hrun
  change _ = stackCfg ι S (MatrixUnaryDivision.run (MatrixUnaryDivision.totalTime n m) c) at hrun
  rw [show c = MatrixUnaryDivision.cfg (some .start) false (List.replicate n true)
      (List.replicate m true) [] [] [] [] from rfl, MatrixUnaryDivision.division_total_run n m] at hrun
  refine hrun.trans ?_
  dsimp [stackCfg, MatrixUnaryDivision.cfg]
  congr 1
  have hloc : (![[], List.replicate m true, [], List.replicate (n % m) true,
      List.replicate (n / m) true, []] : Fin 6 → List Bool) =
      Function.update (Function.update (Function.update (fun k : Fin 6 => S (ι k)) 0 []) 3
        (u (n % m))) 4 (u (n / m)) := by
    funext k
    fin_cases k <;> simp [h1, h2, h5, u]
  rw [hloc, bank_update, bank_update, bank_update, bank_restrict]

def maxProgram (ι : Fin 5 ↪ QK) :
    ETHParameterScaleMachineMax.Label →
      TM2.Stmt (fun _ : QK => Bool) ETHParameterScaleMachineMax.Label
        ETHParameterScaleMachineMax.Control :=
  fun l => stackStmt ι (ETHParameterScaleMachineMax.program l)

theorem max_lift (ι : Fin 5 ↪ QK) (S : QK → List Bool) (x y : ℕ)
    (h0 : S (ι 0) = u x) (h1 : S (ι 1) = u y) (h2 : S (ι 2) = []) (h3 : S (ι 3) = [])
    (h4 : S (ι 4) = []) :
    ((advance (maxProgram ι))^[max x y + x + y + 3])
        (⟨some .scan, (none, none), S⟩ : TM2.Cfg (fun _ : QK => Bool)
          ETHParameterScaleMachineMax.Label ETHParameterScaleMachineMax.Control) =
      ⟨none, (none, none), Function.update S (ι 4) (u (max x y))⟩ := by
  let c := ETHParameterScaleMachineMax.cfg (some .scan) (none, none)
    (List.replicate x true) (List.replicate y true) [] [] []
  have hstart : stackCfg ι S c =
      (⟨some .scan, (none, none), S⟩ : TM2.Cfg (fun _ : QK => Bool)
        ETHParameterScaleMachineMax.Label ETHParameterScaleMachineMax.Control) := by
    dsimp [stackCfg, c, ETHParameterScaleMachineMax.cfg]
    congr 1
    apply bank_eq_self
    intro k
    fin_cases k <;> simp [h0, h1, h2, h3, h4, u]
  have hrun := BitMachineStackRun.run ι S ETHParameterScaleMachineMax.program c
    (max x y + x + y + 3)
  rw [hstart] at hrun
  change _ = stackCfg ι S (ETHParameterScaleMachineMax.run (max x y + x + y + 3) c) at hrun
  have hm := ETHParameterScaleMachineMax.max_run (List.replicate x true) (List.replicate y true)
  simp only [List.length_replicate] at hm
  rw [show c = ETHParameterScaleMachineMax.cfg (some .scan) (none, none)
      (List.replicate x true) (List.replicate y true) [] [] [] from rfl, hm] at hrun
  refine hrun.trans ?_
  dsimp [stackCfg, ETHParameterScaleMachineMax.cfg]
  congr 1
  have hloc : (![List.replicate x true, List.replicate y true, [], [],
      List.replicate (max x y) true] : Fin 5 → List Bool) =
      Function.update (fun k : Fin 5 => S (ι k)) 4 (u (max x y)) := by
    funext k
    fin_cases k <;> simp [h0, h1, h2, h3, u]
  rw [hloc, bank_update, bank_restrict]

/-! ### The log region -/

def region (n : ℕ) : LS → List Bool := fun x => if x = .inl 0 then u n else []

theorem start_stk (q : List Bool) :
    (ETHParameterScaleMachineLogCopy.start q).stk = fun x => if x = .inl 0 then q else [] := by
  change BitMachineStackEmbedding.bank ETHParameterScaleMachineLogCopy.copyStack (fun _ => [])
    (BitMachineCopy.cfg (some .scan) none q [] []).stk = _
  funext k
  by_cases hk : ∃ p : Fin 3, ETHParameterScaleMachineLogCopy.copyStack p = k
  · obtain ⟨p, rfl⟩ := hk
    rw [BitMachineStackEmbedding.bank_at]
    fin_cases p <;> simp [ETHParameterScaleMachineLogCopy.copyStack, BitMachineCopy.cfg]
  · rw [BitMachineStackEmbedding.bank_outside _ _ _ _ hk]
    have hne : k ≠ (.inl (0 : Fin 1) : LS) := by
      intro he
      exact hk ⟨0, by simpa [ETHParameterScaleMachineLogCopy.copyStack] using he.symm⟩
    simp [hne]

def logP := fun l => stackStmt ιL (ETHParameterScaleMachineLogCopy.program l)

abbrev logCtl := ETHParameterScaleMachineLogCopy.copyControl none

def logBd (n : ℕ) : ℕ := 2 * n + 2 + (UnaryBinaryEncoding.coefficient + 6) * (n + 1) ^ 2

theorem log_lift (W : QK → List Bool) (n : ℕ) (hW : ∀ x : LS, W (.inr x) = region n x) :
    ∃ t ≤ logBd n, ∃ c : ETHParameterScaleMachineLogCopy.logMachine.Config,
      ((advance logP)^[t])
          (⟨some (.inl .scan), logCtl, W⟩ : TM2.Cfg (fun _ : QK => Bool) _ _) =
        ⟨none, (none, c.var),
          bank ιL W (ETHParameterScaleMachineLogCopy.afterLog (u n) c).stk⟩ ∧
      (ETHParameterScaleMachineLogCopy.afterLog (u n) c).stk
          (ETHParameterScaleMachineLogCopy.logStack
            ETHParameterScaleMachineLogCopy.logMachine.output) = u (Nat.clog 2 n) ∧
      (ETHParameterScaleMachineLogCopy.afterLog (u n) c).stk (.inl 0) = u n := by
  obtain ⟨t, c, ht, hr, hh, ho⟩ := ETHParameterScaleMachineLogCopy.copied_log_run n
  have hs := BitMachineStackRun.run ιL W ETHParameterScaleMachineLogCopy.program
    (ETHParameterScaleMachineLogCopy.start (u n)) t
  change _ = stackCfg ιL W (ETHParameterScaleMachineLogCopy.run t _) at hs
  have hr' : ETHParameterScaleMachineLogCopy.run t (ETHParameterScaleMachineLogCopy.start (u n)) =
      ETHParameterScaleMachineLogCopy.afterLog (u n) c := hr
  rw [hr'] at hs
  have hb : bank ιL W (ETHParameterScaleMachineLogCopy.start (u n)).stk = W := by
    apply bank_eq_self
    intro x
    rw [start_stk]
    show (if x = .inl 0 then u n else []) = W (.inr x)
    rw [hW]
    rfl
  have hst : stackCfg ιL W (ETHParameterScaleMachineLogCopy.start (u n)) =
      (⟨some (.inl .scan), logCtl, W⟩ : TM2.Cfg (fun _ : QK => Bool) _ _) := by
    simp only [stackCfg]
    rw [hb]
    rfl
  rw [hst] at hs
  have hl : (ETHParameterScaleMachineLogCopy.afterLog (u n) c).l = none := by
    simp [ETHParameterScaleMachineLogCopy.afterLog, BitMachineStackEmbedding.cfg, stackCfg,
      BitMachineInline.cfg, hh]
  refine ⟨t, by unfold logBd; exact ht, c, ?_, ?_, ?_⟩
  · refine hs.trans ?_
    simp only [stackCfg]
    rw [hl]
    rfl
  · exact (ETHParameterScaleMachineLogCopy.afterLog_output n c).trans ho
  · exact ETHParameterScaleMachineLogCopy.afterLog_source n c

theorem bank_inl (W : QK → List Bool) (F : LS → List Bool) (i : Fin 29) :
    bank ιL W F (.inl i) = W (.inl i) := by
  apply bank_outside
  rintro ⟨k, hk⟩
  cases hk

theorem bank_inr (W : QK → List Bool) (F : LS → List Bool) (y : LS) :
    bank ιL W F (.inr y) = F y :=
  bank_at ιL W F y

/-! ### Pushes of machine constants (one step each) -/

def pushN (a : QK) (k : ℕ) (q : TM2.Stmt (fun _ : QK => Bool) Unit Bool) :
    TM2.Stmt (fun _ : QK => Bool) Unit Bool :=
  match k with
  | 0 => q
  | k + 1 => TM2.Stmt.push a (fun _ => true) (pushN a k q)

def pushP (a : QK) (k : ℕ) : Unit → TM2.Stmt (fun _ : QK => Bool) Unit Bool := fun _ =>
  pushN a k TM2.Stmt.halt

theorem pushN_step (a : QK) (k : ℕ) (q : TM2.Stmt (fun _ : QK => Bool) Unit Bool) (v : Bool)
    (S : QK → List Bool) :
    TM2.stepAux (pushN a k q) v S =
      TM2.stepAux q v (Function.update S a (List.replicate k true ++ S a)) := by
  induction k generalizing S with
  | zero => simp [pushN]
  | succ k ih =>
      show TM2.stepAux (pushN a k q) v (Function.update S a (true :: S a)) = _
      rw [ih, Function.update_self, Function.update_idem]
      congr 2
      rw [List.replicate_succ', List.append_assoc]
      rfl

theorem pushP_run (a : QK) (k : ℕ) (S : QK → List Bool) (v : Bool) :
    ((advance (pushP a k))^[1]) (⟨some (), v, S⟩ : TM2.Cfg (fun _ : QK => Bool) Unit Bool) =
      ⟨none, v, Function.update S a (List.replicate k true ++ S a)⟩ := by
  show Option.getD (some (TM2.stepAux (pushN a k TM2.Stmt.halt) v S))
    (⟨some (), v, S⟩ : TM2.Cfg (fun _ : QK => Bool) Unit Bool) = _
  rw [pushN_step]
  rfl

def pop1 (a : QK) : Unit → TM2.Stmt (fun _ : QK => Bool) Unit Bool := fun _ =>
  TM2.Stmt.pop a (fun v _ => v) TM2.Stmt.halt

/-! ### The program -/

def cp (ι : Fin 3 ↪ QK) := MatrixStage4ScalarPreparationOps.copyProgram ι
def pw (ι : MatrixUnaryPower.Stack ↪ QK) := MatrixStage4ScalarPreparationOps.unaryPowerProgram ι
def mul (ι : Fin 6 ↪ QK) := MatrixStage4ScalarPreparationOps.multiplyProgram ι

abbrev powCtl : MatrixUnaryPower.Control := ((false, false), none)
abbrev oc := (none : Option Bool)
abbrev mxCtl : ETHParameterScaleMachineMax.Control := (none, none)

section prog
variable (a b Δ : ℕ)

def P1 := pushP (.inl 5) 24
def P2 := pw ιP1
def P3 := mul ιM1
def P4 := mul ιM2
def P5 := mul ιM3
def P6 := pushP (.inl 10) 5
def P7 := mul ιM4
def P8 := pushP (.inl 12) (2 * b * Δ)
def P9 := mul ιM5
def P10 := mul ιM6
def P11 := pushP (.inl 15) a
def P12 := mul ιM7
def P13 := cp ιC1
def P14 := pop1 (.inl 14)
def P15 := divProgram ιD1
def P16 := pushP (.inl 19) (6144 * b)
def P17 := mul ιM8
def P18 := pushP (.inl 20) (a - 1)
def P19 := divProgram ιD2
def P20 := maxProgram ιX1
def P21 := maxProgram ιX2
def P22 := logP
def P23 := pw ιP2

def s1 := BitMachineRawSequence.program P1 P2 (.inr false) false powCtl
def k1 := (false, powCtl)
def s2 := BitMachineRawSequence.program s1 P3 MatrixAddressMachine.Label.outer k1 false
def k2 := (k1, false)
def s3 := BitMachineRawSequence.program s2 P4 MatrixAddressMachine.Label.outer k2 false
def k3 := (k2, false)
def s4 := BitMachineRawSequence.program s3 P5 MatrixAddressMachine.Label.outer k3 false
def k4 := (k3, false)
def s5 := BitMachineRawSequence.program s4 P6 () k4 false
def k5 := (k4, false)
def s6 := BitMachineRawSequence.program s5 P7 MatrixAddressMachine.Label.outer k5 false
def k6 := (k5, false)
def s7 := BitMachineRawSequence.program s6 (P8 b Δ) () k6 false
def k7 := (k6, false)
def s8 := BitMachineRawSequence.program (s7 b Δ) P9 MatrixAddressMachine.Label.outer k7 false
def k8 := (k7, false)
def s9 := BitMachineRawSequence.program (s8 b Δ) P10 MatrixAddressMachine.Label.outer k8 false
def k9 := (k8, false)
def s10 := BitMachineRawSequence.program (s9 b Δ) (P11 a) () k9 false
def k10 := (k9, false)
def s11 := BitMachineRawSequence.program (s10 a b Δ) P12 MatrixAddressMachine.Label.outer k10 false
def k11 := (k10, false)
def s12 := BitMachineRawSequence.program (s11 a b Δ) P13 BitMachineCopy.Label.scan k11 oc
def k12 := (k11, oc)
def s13 := BitMachineRawSequence.program (s12 a b Δ) P14 () k12 false
def k13 := (k12, false)
def s14 := BitMachineRawSequence.program (s13 a b Δ) P15 MatrixUnaryDivision.Label.start k13 false
def k14 := (k13, false)
def s15 := BitMachineRawSequence.program (s14 a b Δ) (P16 b) () k14 false
def k15 := (k14, false)
def s16 := BitMachineRawSequence.program (s15 a b Δ) P17 MatrixAddressMachine.Label.outer k15 false
def k16 := (k15, false)
def s17 := BitMachineRawSequence.program (s16 a b Δ) (P18 a) () k16 false
def k17 := (k16, false)
def s18 := BitMachineRawSequence.program (s17 a b Δ) P19 MatrixUnaryDivision.Label.start k17 false
def k18 := (k17, false)
def s19 := BitMachineRawSequence.program (s18 a b Δ) P20 ETHParameterScaleMachineMax.Label.scan k18 mxCtl
def k19 := (k18, mxCtl)
def s20 := BitMachineRawSequence.program (s19 a b Δ) P21 ETHParameterScaleMachineMax.Label.scan k19 mxCtl
def k20 := (k19, mxCtl)
def s21 := BitMachineRawSequence.program (s20 a b Δ) P22 (.inl .scan) k20 logCtl
def k21 := (k20, logCtl)
/-- The cover-width producer: ONE fixed program (for fixed machine constants `a`, `b`, `Δ`). -/
def qProg := BitMachineRawSequence.program (s21 a b Δ) P23 (.inr false) k21 powCtl
end prog

def qCtl := (k21, powCtl)
def labelOfP {L σ : Type*} {K : Type*} (_P : L → TM2.Stmt (fun _ : K => Bool) L σ)
    (l : L) : L := l
def qStart (a b Δ : ℕ) := labelOfP (qProg a b Δ) (leftLabel (leftLabel (leftLabel (leftLabel
  (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel
  (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel
  (leftLabel (leftLabel ()))))))))))))))))))))))

/-- Start bank: unary `n`, `m`, `L`, `s`, `w` in cells 0-4; everything else (the log region
included) blank. -/
def Q0 (n m L s w : ℕ) : QK → List Bool :=
  Function.update (Function.update (Function.update (Function.update (Function.update
    (fun _ => []) (.inl 0) (u n)) (.inl 1) (u m)) (.inl 2) (u L)) (.inl 3) (u s)) (.inl 4) (u w)

end

end Paper2.QProducer
