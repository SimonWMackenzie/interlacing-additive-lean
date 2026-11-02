import EthInapproximability.CurrentPaper.PrimeSampler
import EthInapproximability.CurrentPaper.SourceClauseFixedBatch
import EthInapproximability.CurrentPaper.MatrixStage4ScalarPreparationOps
import EthInapproximability.CurrentPaper.ETHParameterScaleMachineMax
import EthInapproximability.CurrentPaper.BitMachineRawSequence
import EthInapproximability.CurrentPaper.BitMachineClearBank
import EthInapproximability.CurrentPaper.SourceClauseClearExcept

/-!
Physical unary computation of the weighted-prime search threshold.
The only initial words are q,t,m.  In particular, neither the threshold nor
the constants 1000 and 2 occur in the initial bank.
-/

namespace Paper2.WeightedThresholdArithmetic

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

open Turing EthInapproximability.CurrentPaper
open MatrixStage4ScalarPreparationOps BitMachineEncoding

abbrev Stack := Fin 15

def unary (n : ℕ) : List Bool := List.replicate n true

def initial (q t m : ℕ) : Stack → List Bool :=
  fun j => if j = 0 then unary q else if j = 1 then unary t else
    if j = 2 then unary m else []

-- 0=q, 1=t, 2=m; 3=m*t, 4=m*t*t, 5=1000*m*t*t;
-- 6=max(q,scaled), 7=2, 8=threshold, 9=1000;
-- 10,11,12 are multiplier work, 13,14 are maximum work.
def constTargets : Fin 2 → Stack := ![9,7]
def constSizes : Fin 2 → ℕ := ![1000,2]
def constProgram := SourceClauseFixedBatch.program constTargets constSizes
def constBank (q t m : ℕ) : Stack → List Bool :=
  SourceClauseFixedBatch.bankPrefix constTargets constSizes (initial q t m) 2

theorem const_run (q t m : ℕ) :
    ((advance constProgram)^[SourceClauseFixedBatch.costPrefix constSizes 2 + 1])
      (⟨some (SourceClauseFixedBatch.labelAt constSizes 0), (), initial q t m⟩ :
        TM2.Cfg (fun _ : Stack => Bool) _ Unit) =
      ⟨none, (), constBank q t m⟩ :=
  SourceClauseFixedBatch.run constTargets constSizes (initial q t m)

theorem const_at (q t m : ℕ) :
    (constBank q t m) 0 = unary q ∧
    (constBank q t m) 1 = unary t ∧
    (constBank q t m) 2 = unary m ∧
    (constBank q t m) 7 = unary 2 ∧
    (constBank q t m) 9 = unary 1000 ∧
    (∀ j : Stack, j ≠ 0 → j ≠ 1 → j ≠ 2 → j ≠ 7 → j ≠ 9 →
      constBank q t m j = []) := by
  have hinj : Function.Injective constTargets := by decide
  have ht (i : Fin 2) := SourceClauseFixedBatch.result_target
    constTargets constSizes (initial q t m) hinj i
  have ho (j : Stack) (hj : ∀ i : Fin 2, constTargets i ≠ j) :=
    SourceClauseFixedBatch.result_outside constTargets constSizes
      (initial q t m) j hj
  constructor
  · simpa [constBank, constTargets, initial, unary] using ho 0 (by decide)
  constructor
  · simpa [constBank, constTargets, initial, unary] using ho 1 (by decide)
  constructor
  · simpa [constBank, constTargets, initial, unary] using ho 2 (by decide)
  constructor
  · simpa [constBank, constTargets, constSizes, initial, unary] using ht 1
  constructor
  · simpa only [constBank, constTargets, constSizes, initial,
      Matrix.cons_val_zero, List.append_nil] using ht 0
  · intro j h0 h1 h2 h7 h9
    have hj : ∀ i : Fin 2, constTargets i ≠ j := by
      intro i
      fin_cases i
      · exact Ne.symm h9
      · exact Ne.symm h7
    simpa [constBank, initial, h0, h1, h2] using ho j hj

def mul1Slots : Fin 6 ↪ Stack := ⟨![2,1,10,11,12,3], by decide⟩
def mul2Slots : Fin 6 ↪ Stack := ⟨![3,1,10,11,12,4], by decide⟩
def mul3Slots : Fin 6 ↪ Stack := ⟨![4,9,10,11,12,5], by decide⟩
def mul1Program := multiplyProgram mul1Slots
def mul2Program := multiplyProgram mul2Slots
def mul3Program := multiplyProgram mul3Slots

def bank1 (q t m : ℕ) : Stack → List Bool :=
  Function.update (constBank q t m) 3 (unary (m*t))
def bank2 (q t m : ℕ) : Stack → List Bool :=
  Function.update (bank1 q t m) 4 (unary (m*t*t))
def bank3 (q t m : ℕ) : Stack → List Bool :=
  Function.update (bank2 q t m) 5 (unary (1000*m*t^2))

theorem mul1_run (q t m : ℕ) :
    ((advance mul1Program)^[MatrixAddressMachine.exactTime m t 0])
      (⟨some .outer, false, constBank q t m⟩ :
        TM2.Cfg (fun _ : Stack => Bool) _ Bool) =
      ⟨none, false, bank1 q t m⟩ := by
  obtain ⟨_, ht, hm, _, _, hw⟩ := const_at q t m
  have he : (constBank q t m) 3 = [] :=
    hw 3 (by decide) (by decide) (by decide) (by decide) (by decide)
  have h := multiply_run mul1Slots (constBank q t m) m t
      (by simpa [mul1Slots] using hm) (by simpa [mul1Slots] using ht)
      (hw 10 (by decide) (by decide) (by decide) (by decide) (by decide))
      (hw 11 (by decide) (by decide) (by decide) (by decide) (by decide))
      (hw 12 (by decide) (by decide) (by decide) (by decide) (by decide))
  simpa [mul1Program, mul1Slots, bank1, unary, he] using h

theorem mul2_run (q t m : ℕ) :
    ((advance mul2Program)^[MatrixAddressMachine.exactTime (m*t) t 0])
      (⟨some .outer, false, bank1 q t m⟩ :
        TM2.Cfg (fun _ : Stack => Bool) _ Bool) =
      ⟨none, false, bank2 q t m⟩ := by
  obtain ⟨_, ht, _, _, _, hw⟩ := const_at q t m
  have he : (bank1 q t m) 4 = [] := by
    simpa [bank1] using hw 4 (by decide) (by decide) (by decide) (by decide) (by decide)
  have h := multiply_run mul2Slots (bank1 q t m) (m*t) t
      (by simp [mul2Slots, bank1, unary])
      (by simpa [mul2Slots, bank1] using ht)
      (by simpa [bank1, Function.update_of_ne] using
        hw 10 (by decide) (by decide) (by decide) (by decide) (by decide))
      (by simpa [bank1, Function.update_of_ne] using
        hw 11 (by decide) (by decide) (by decide) (by decide) (by decide))
      (by simpa [bank1, Function.update_of_ne] using
        hw 12 (by decide) (by decide) (by decide) (by decide) (by decide))
  simpa [mul2Program, mul2Slots, bank2, unary, he] using h

theorem mul3_run (q t m : ℕ) :
    ((advance mul3Program)^[MatrixAddressMachine.exactTime (m*t*t) 1000 0])
      (⟨some .outer, false, bank2 q t m⟩ :
        TM2.Cfg (fun _ : Stack => Bool) _ Bool) =
      ⟨none, false, bank3 q t m⟩ := by
  obtain ⟨_, _, _, _, hc, hw⟩ := const_at q t m
  have hmtt : (bank2 q t m) 4 = unary (m*t*t) := by simp [bank2]
  have hc' : (bank2 q t m) 9 = unary 1000 := by
    simpa [bank2, bank1, Function.update_of_ne] using hc
  have he (i : Stack) (hi : i = 10 ∨ i = 11 ∨ i = 12) :
      (bank2 q t m) i = [] := by
    rcases hi with rfl | rfl | rfl
    · simpa [bank2, bank1] using
        hw 10 (by decide) (by decide) (by decide) (by decide) (by decide)
    · simpa [bank2, bank1] using
        hw 11 (by decide) (by decide) (by decide) (by decide) (by decide)
    · simpa [bank2, bank1] using
        hw 12 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hout : (bank2 q t m) 5 = [] := by
    simpa [bank2, bank1] using
      hw 5 (by decide) (by decide) (by decide) (by decide) (by decide)
  have h := multiply_run mul3Slots (bank2 q t m) (m*t*t) 1000
    (by simpa [mul3Slots] using hmtt) (by simpa [mul3Slots] using hc')
    (he 10 (Or.inl rfl)) (he 11 (Or.inr (Or.inl rfl)))
    (he 12 (Or.inr (Or.inr rfl)))
  simpa [mul3Program, mul3Slots, bank3, unary, hout,
    Nat.pow_two, Nat.mul_assoc, Nat.mul_comm,
    Nat.mul_left_comm] using h

def maxProgram (ι : Fin 5 ↪ Stack) :
    ETHParameterScaleMachineMax.Label →
      TM2.Stmt (fun _ : Stack => Bool)
        ETHParameterScaleMachineMax.Label ETHParameterScaleMachineMax.Control :=
  fun l => BitMachineStackEmbedding.stackStmt ι (ETHParameterScaleMachineMax.program l)

theorem max_run (ι : Fin 5 ↪ Stack) (S : Stack → List Bool)
    (a b : List Bool)
    (ha : S (ι 0) = a) (hb : S (ι 1) = b)
    (h2 : S (ι 2) = []) (h3 : S (ι 3) = [])
    (h4 : S (ι 4) = []) :
    ((advance (maxProgram ι))^[max a.length b.length + a.length + b.length + 3])
      (⟨some .scan, (none,none), S⟩ :
        TM2.Cfg (fun _ : Stack => Bool)
          ETHParameterScaleMachineMax.Label ETHParameterScaleMachineMax.Control) =
      ⟨none, (none,none),
        Function.update S (ι 4) (unary (max a.length b.length))⟩ := by
  let c := ETHParameterScaleMachineMax.cfg (some .scan)
    (none,none) a b [] [] []
  have hstart : BitMachineStackEmbedding.stackCfg ι S c =
      (⟨some .scan, (none,none), S⟩ :
        TM2.Cfg (fun _ : Stack => Bool)
          ETHParameterScaleMachineMax.Label ETHParameterScaleMachineMax.Control) := by
    dsimp [BitMachineStackEmbedding.stackCfg, c,
      ETHParameterScaleMachineMax.cfg]
    congr 1
    apply BitMachineStackEmbedding.bank_eq_self
    intro k
    fin_cases k <;> simp [ha, hb, h2, h3, h4]
  have hr := BitMachineStackRun.run ι S ETHParameterScaleMachineMax.program c
    (max a.length b.length + a.length + b.length + 3)
  rw [hstart] at hr
  change _ = BitMachineStackEmbedding.stackCfg ι S
    (ETHParameterScaleMachineMax.run
      (max a.length b.length + a.length + b.length + 3) c) at hr
  rw [show c = ETHParameterScaleMachineMax.cfg (some .scan)
      (none,none) a b [] [] [] from rfl,
    ETHParameterScaleMachineMax.max_run] at hr
  refine hr.trans ?_
  dsimp [BitMachineStackEmbedding.stackCfg,
    ETHParameterScaleMachineMax.cfg]
  congr 1
  have hloc : (![a,b,([] : List Bool),[],unary (max a.length b.length)] :
      Fin 5 → List Bool) =
      Function.update (fun k : Fin 5 => S (ι k)) 4
        (unary (max a.length b.length)) := by
    funext k
    fin_cases k <;> simp [ha, hb, h2, h3]
  change BitMachineStackEmbedding.bank ι S
    (![a,b,([] : List Bool),[],unary (max a.length b.length)] :
      Fin 5 → List Bool) = _
  rw [hloc, BitMachineStackEmbedding.bank_update,
    BitMachineStackEmbedding.bank_restrict]

def max1Slots : Fin 5 ↪ Stack := ⟨![0,5,13,14,6], by decide⟩
def max2Slots : Fin 5 ↪ Stack := ⟨![6,7,13,14,8], by decide⟩
def max1Program := maxProgram max1Slots
def max2Program := maxProgram max2Slots

def bank4 (q t m : ℕ) : Stack → List Bool :=
  Function.update (bank3 q t m) 6 (unary (max q (1000*m*t^2)))
def bank5 (q t m : ℕ) : Stack → List Bool :=
  Function.update (bank4 q t m) 8 (unary (PrimeSampler.threshold q t m))

theorem max1_run (q t m : ℕ) :
    ((advance max1Program)^[max q (1000*m*t^2) + q + 1000*m*t^2 + 3])
      (⟨some .scan, (none,none), bank3 q t m⟩ :
        TM2.Cfg (fun _ : Stack => Bool) _ _) =
      ⟨none, (none,none), bank4 q t m⟩ := by
  obtain ⟨hq, _, _, _, _, hw⟩ := const_at q t m
  have he (i : Stack) (hi : i = 6 ∨ i = 13 ∨ i = 14) :
      (bank3 q t m) i = [] := by
    rcases hi with rfl | rfl | rfl
    · simpa [bank3, bank2, bank1] using
        hw 6 (by decide) (by decide) (by decide) (by decide) (by decide)
    · simpa [bank3, bank2, bank1] using
        hw 13 (by decide) (by decide) (by decide) (by decide) (by decide)
    · simpa [bank3, bank2, bank1] using
        hw 14 (by decide) (by decide) (by decide) (by decide) (by decide)
  have h := max_run max1Slots (bank3 q t m)
    (unary q) (unary (1000*m*t^2))
    (by simpa [max1Slots, bank3, bank2, bank1] using hq)
    (by simp [max1Slots, bank3])
    (he 13 (Or.inr (Or.inl rfl)))
    (he 14 (Or.inr (Or.inr rfl)))
    (he 6 (Or.inl rfl))
  simpa [max1Program, max1Slots, bank4, unary, he 6 (Or.inl rfl)] using h

theorem max2_run (q t m : ℕ) :
    let x := max q (1000*m*t^2)
    ((advance max2Program)^[max x 2 + x + 2 + 3])
      (⟨some .scan, (none,none), bank4 q t m⟩ :
        TM2.Cfg (fun _ : Stack => Bool) _ _) =
      ⟨none, (none,none), bank5 q t m⟩ := by
  obtain ⟨_, _, _, htwo, _, hw⟩ := const_at q t m
  have he : (bank4 q t m) 8 = [] := by
    simpa [bank4, bank3, bank2, bank1] using
      hw 8 (by decide) (by decide) (by decide) (by decide) (by decide)
  have h := max_run max2Slots (bank4 q t m)
    (unary (max q (1000*m*t^2))) (unary 2)
    (by simp [max2Slots, bank4])
    (by simpa [max2Slots, bank4, bank3, bank2, bank1] using htwo)
    (by simpa [max2Slots, bank4, bank3, bank2, bank1] using
      hw 13 (by decide) (by decide) (by decide) (by decide) (by decide))
    (by simpa [max2Slots, bank4, bank3, bank2, bank1] using
      hw 14 (by decide) (by decide) (by decide) (by decide) (by decide))
    (by simpa [max2Slots] using he)
  simpa [max2Program, max2Slots, bank5, unary, PrimeSampler.threshold,
    he] using h

def constStart := SourceClauseFixedBatch.labelAt constSizes 0
def constTime := SourceClauseFixedBatch.costPrefix constSizes 2 + 1
def mul1Time (t m : ℕ) := MatrixAddressMachine.exactTime m t 0
def mul2Time (t m : ℕ) := MatrixAddressMachine.exactTime (m*t) t 0
def mul3Time (t m : ℕ) := MatrixAddressMachine.exactTime (m*t*t) 1000 0
def max1Time (q t m : ℕ) :=
  max q (1000*m*t^2) + q + 1000*m*t^2 + 3
def max2Time (q t m : ℕ) :=
  max (max q (1000*m*t^2)) 2 + max q (1000*m*t^2) + 2 + 3

def program1 := BitMachineRawSequence.program constProgram mul1Program
  MatrixAddressMachine.Label.outer () false
def program2 := BitMachineRawSequence.program program1 mul2Program
  MatrixAddressMachine.Label.outer ((),false) false
def program3 := BitMachineRawSequence.program program2 mul3Program
  MatrixAddressMachine.Label.outer (((),false),false) false
def program4 := BitMachineRawSequence.program program3 max1Program
  ETHParameterScaleMachineMax.Label.scan ((((),false),false),false) (none,none)
def program5 := BitMachineRawSequence.program program4 max2Program
  ETHParameterScaleMachineMax.Label.scan
  (((((),false),false),false),(none,none)) (none,none)

abbrev Label1 := BitMachineRawSequence.Label
  (SourceClauseFixedBatch.Label constSizes) MatrixAddressMachine.Label
abbrev Label2 := BitMachineRawSequence.Label Label1 MatrixAddressMachine.Label
abbrev Label3 := BitMachineRawSequence.Label Label2 MatrixAddressMachine.Label
abbrev Label4 := BitMachineRawSequence.Label Label3 ETHParameterScaleMachineMax.Label
abbrev Label5 := BitMachineRawSequence.Label Label4 ETHParameterScaleMachineMax.Label
def start1 : Label1 := .inl constStart
def start2 : Label2 := .inl start1
def start3 : Label3 := .inl start2
def start4 : Label4 := .inl start3
def start5 : Label5 := .inl start4

def control1 := ((),false)
def control2 := (control1,false)
def control3 := (control2,false)
def maxInitial : ETHParameterScaleMachineMax.Control := (none,none)
def control4 := (control3,maxInitial)
def control5 := (control4,maxInitial)

def time1 (t m : ℕ) := constTime + mul1Time t m + 1
def time2 (t m : ℕ) := time1 t m + mul2Time t m + 1
def time3 (t m : ℕ) := time2 t m + mul3Time t m + 1
def time4 (q t m : ℕ) := time3 t m + max1Time q t m + 1
def time5 (q t m : ℕ) := time4 q t m + max2Time q t m + 1

theorem run1 (q t m : ℕ) :
    ∃ u ≤ time1 t m,
      ((advance program1)^[u])
        (⟨some start1, control1, initial q t m⟩ :
          TM2.Cfg (fun _ : Stack => Bool) _ _) =
        ⟨none, control1, bank1 q t m⟩ := by
  simpa only [program1, start1, control1, time1, constTime,
    mul1Time, constStart] using
    BitMachineRawSequence.runs constProgram mul1Program
      constStart .outer () () false false
      (initial q t m) (constBank q t m) (bank1 q t m)
      constTime (mul1Time t m)
      (by simpa [constStart, constTime] using const_run q t m)
      (by simpa [mul1Time] using mul1_run q t m)

theorem run2 (q t m : ℕ) :
    ∃ u ≤ time2 t m,
      ((advance program2)^[u])
        (⟨some start2, control2, initial q t m⟩ :
          TM2.Cfg (fun _ : Stack => Bool) _ _) =
        ⟨none, control2, bank2 q t m⟩ := by
  obtain ⟨u, hu, hr⟩ := run1 q t m
  obtain ⟨v, hv, hs⟩ := BitMachineRawSequence.runs
    program1 mul2Program start1 .outer control1 control1 false false
    (initial q t m) (bank1 q t m) (bank2 q t m)
    u (mul2Time t m) hr (by simpa [mul2Time] using mul2_run q t m)
  exact ⟨v, by dsimp [time2]; omega, by simpa [program2, start2,
    control2] using hs⟩

theorem run3 (q t m : ℕ) :
    ∃ u ≤ time3 t m,
      ((advance program3)^[u])
        (⟨some start3, control3, initial q t m⟩ :
          TM2.Cfg (fun _ : Stack => Bool) _ _) =
        ⟨none, control3, bank3 q t m⟩ := by
  obtain ⟨u, hu, hr⟩ := run2 q t m
  obtain ⟨v, hv, hs⟩ := BitMachineRawSequence.runs
    program2 mul3Program start2 .outer control2 control2 false false
    (initial q t m) (bank2 q t m) (bank3 q t m)
    u (mul3Time t m) hr (by simpa [mul3Time] using mul3_run q t m)
  exact ⟨v, by dsimp [time3]; omega, by simpa [program3, start3,
    control3] using hs⟩

theorem run4 (q t m : ℕ) :
    ∃ u ≤ time4 q t m,
      ((advance program4)^[u])
        (⟨some start4, control4, initial q t m⟩ :
          TM2.Cfg (fun _ : Stack => Bool) _ _) =
        ⟨none, control4, bank4 q t m⟩ := by
  obtain ⟨u, hu, hr⟩ := run3 q t m
  obtain ⟨v, hv, hs⟩ := BitMachineRawSequence.runs
    program3 max1Program start3 .scan control3 control3
    (none,none) (none,none)
    (initial q t m) (bank3 q t m) (bank4 q t m)
    u (max1Time q t m) hr (by simpa [max1Time] using max1_run q t m)
  exact ⟨v, by dsimp [time4]; omega, by simpa [program4, start4,
    control4] using hs⟩

theorem run5 (q t m : ℕ) :
    ∃ u ≤ time5 q t m,
      ((advance program5)^[u])
        (⟨some start5, control5, initial q t m⟩ :
          TM2.Cfg (fun _ : Stack => Bool) _ _) =
        ⟨none, control5, bank5 q t m⟩ := by
  obtain ⟨u, hu, hr⟩ := run4 q t m
  obtain ⟨v, hv, hs⟩ := BitMachineRawSequence.runs
    program4 max2Program start4 .scan control4 control4
    (none,none) (none,none)
    (initial q t m) (bank4 q t m) (bank5 q t m)
    u (max2Time q t m) hr (by simpa [max2Time] using max2_run q t m)
  exact ⟨v, by dsimp [time5]; omega, by simpa [program5, start5,
    control5] using hs⟩

def keep : Finset Stack := {0,1,2,8}
noncomputable def clearProgram := SourceClauseClearExcept.program keep
def clearStart : SourceClauseClearExcept.Label
    (SourceClauseClearExcept.workCount keep) := .clear 0
noncomputable def clearBank (q t m : ℕ) : Stack → List Bool :=
  SourceClauseClearExcept.result keep (bank5 q t m)
noncomputable def clearTime (q t m : ℕ) : ℕ :=
  (∑ i : Fin (SourceClauseClearExcept.workCount keep),
    ((bank5 q t m) (SourceClauseClearExcept.workBank keep i)).length) +
    SourceClauseClearExcept.workCount keep + 2

theorem clear_run (q t m : ℕ) :
    ((advance clearProgram)^[clearTime q t m])
      (⟨some clearStart, ((),none), bank5 q t m⟩ :
        TM2.Cfg (fun _ : Stack => Bool) _ _) =
      ⟨none, ((),none), clearBank q t m⟩ := by
  simpa only [clearProgram, clearTime, clearStart, clearBank] using
    SourceClauseClearExcept.run keep (bank5 q t m)

def finalBank (q t m : ℕ) : Stack → List Bool :=
  fun j => if j = 0 then unary q else if j = 1 then unary t else
    if j = 2 then unary m else if j = 8 then
      unary (PrimeSampler.threshold q t m) else []

theorem clearBank_eq_final (q t m : ℕ) :
    clearBank q t m = finalBank q t m := by
  obtain ⟨hq, ht, hm, _, _, _⟩ := const_at q t m
  funext j
  by_cases h0 : j = 0
  · subst j
    simpa [clearBank, SourceClauseClearExcept.result, keep, finalBank,
      bank5, bank4, bank3, bank2, bank1] using hq
  by_cases h1 : j = 1
  · subst j
    simpa [clearBank, SourceClauseClearExcept.result, keep, finalBank,
      bank5, bank4, bank3, bank2, bank1] using ht
  by_cases h2 : j = 2
  · subst j
    simpa [clearBank, SourceClauseClearExcept.result, keep, finalBank,
      bank5, bank4, bank3, bank2, bank1] using hm
  by_cases h8 : j = 8
  · subst j
    simp [clearBank, SourceClauseClearExcept.result, keep, finalBank, bank5]
  have hk : j ∉ keep := by simp [keep, h0, h1, h2, h8]
  simp [clearBank, SourceClauseClearExcept.result, finalBank,
    hk, h0, h1, h2, h8]

noncomputable def program := BitMachineRawSequence.program
  program5 clearProgram clearStart control5 ((),none)
def start : BitMachineRawSequence.Label Label5
    (SourceClauseClearExcept.Label (SourceClauseClearExcept.workCount keep)) :=
  .inl start5
def controlFinal := (control5,((),(none : Option Bool)))
noncomputable def totalTime (q t m : ℕ) := time5 q t m + clearTime q t m + 1

theorem threshold_run (q t m : ℕ) :
    ∃ u ≤ totalTime q t m,
      ((advance program)^[u])
        (⟨some start, controlFinal, initial q t m⟩ :
          TM2.Cfg (fun _ : Stack => Bool) _ _) =
        ⟨none, controlFinal, finalBank q t m⟩ := by
  obtain ⟨u, hu, hr⟩ := run5 q t m
  obtain ⟨v, hv, hs⟩ := BitMachineRawSequence.runs
    program5 clearProgram start5 clearStart control5 control5
    ((),none) ((),none)
    (initial q t m) (bank5 q t m) (clearBank q t m)
    u (clearTime q t m) hr (clear_run q t m)
  refine ⟨v, by dsimp [totalTime]; omega, ?_⟩
  simpa only [program, start, controlFinal, clearBank_eq_final] using hs

def size (q t m : ℕ) : ℕ :=
  q + t + m + PrimeSampler.threshold q t m + 1002

private theorem product_bounds (q t m : ℕ) :
    m*t ≤ (size q t m)^2 ∧
    m*t*t ≤ (size q t m)^3 ∧
    1000*m*t^2 ≤ 1000*(size q t m)^3 := by
  let n := size q t m
  have hm : m ≤ n := by dsimp [n, size]; omega
  have ht : t ≤ n := by dsimp [n, size]; omega
  have hn : 1 ≤ n := by dsimp [n, size]; omega
  have hmt : m*t ≤ n^2 := by
    calc m*t ≤ n*n := Nat.mul_le_mul hm ht
      _ = n^2 := by ring
  have hmt2 : m*t*t ≤ n^3 := by
    calc m*t*t ≤ n^2*n := Nat.mul_le_mul hmt ht
      _ = n^3 := by ring
  have hscaled : 1000*m*t^2 ≤ 1000*n^3 := by
    have hh := Nat.mul_le_mul_left 1000 hmt2
    nlinarith [hh]
  exact ⟨hmt,hmt2,hscaled⟩

private theorem update_length_le (S : Stack → List Bool) (k : Stack)
    (w : List Bool) (B : ℕ)
    (hS : ∀ j, (S j).length ≤ B) (hw : w.length ≤ B) :
    ∀ j, ((Function.update S k w) j).length ≤ B := by
  intro j
  by_cases hj : j = k
  · subst j; simpa using hw
  · simpa [Function.update_of_ne hj] using hS j

private theorem const_length_le (q t m : ℕ) (j : Stack) :
    ((constBank q t m) j).length ≤
      1000*(size q t m)^3 + size q t m + 1000 := by
  obtain ⟨hq, ht, hm, htwo, hthousand, hw⟩ := const_at q t m
  by_cases h0 : j = 0
  · subst j; rw [hq]; simp [unary]; dsimp [size]; omega
  by_cases h1 : j = 1
  · subst j; rw [ht]; simp [unary]; dsimp [size]; omega
  by_cases h2 : j = 2
  · subst j; rw [hm]; simp [unary]; dsimp [size]; omega
  by_cases h7 : j = 7
  · subst j; rw [htwo]; simp [unary]
  by_cases h9 : j = 9
  · subst j; rw [hthousand]; simp [unary]
  rw [hw j h0 h1 h2 h7 h9]
  simp

private theorem bank5_length_le (q t m : ℕ) (j : Stack) :
    ((bank5 q t m) j).length ≤
      1000*(size q t m)^3 + size q t m + 1000 := by
  let n := size q t m
  let B := 1000*n^3+n+1000
  obtain ⟨hmt,hmt2,hscaled⟩ := product_bounds q t m
  change m*t ≤ n^2 at hmt
  change m*t*t ≤ n^3 at hmt2
  change 1000*m*t^2 ≤ 1000*n^3 at hscaled
  have hn2 : n^2 ≤ n^3 := by
    have hn : 1 ≤ n := by dsimp [n, size]; omega
    calc n^2 = n^2*1 := by omega
      _ ≤ n^2*n := Nat.mul_le_mul_left _ hn
      _ = n^3 := by ring
  have h1 : ∀ j, ((bank1 q t m) j).length ≤ B := by
    apply update_length_le
    · intro k
      simpa only [B,n] using const_length_le q t m k
    · simp [unary, B]
      omega
  have h2 : ∀ j, ((bank2 q t m) j).length ≤ B := by
    apply update_length_le (bank1 q t m) 4 (unary (m*t*t)) B h1
    simp [unary, B]
    omega
  have h3 : ∀ j, ((bank3 q t m) j).length ≤ B := by
    apply update_length_le (bank2 q t m) 5 (unary (1000*m*t^2)) B h2
    simp [unary, B]
    omega
  have hmax : max q (1000*m*t^2) ≤ PrimeSampler.threshold q t m := by
    unfold PrimeSampler.threshold
    exact Nat.le_max_left _ _
  have hx : PrimeSampler.threshold q t m ≤ n := by
    dsimp [n, size]; omega
  have h4 : ∀ j, ((bank4 q t m) j).length ≤ B := by
    apply update_length_le (bank3 q t m) 6
      (unary (max q (1000*m*t^2))) B h3
    simp [unary, B]
    omega
  have h5 : ∀ j, ((bank5 q t m) j).length ≤ B := by
    apply update_length_le (bank4 q t m) 8
      (unary (PrimeSampler.threshold q t m)) B h4
    simp [unary, B]
    omega
  simpa only [B,n] using h5 j

theorem clearTime_le (q t m : ℕ) :
    clearTime q t m ≤
      15 * (1000*(size q t m)^3 + size q t m + 1000) + 17 := by
  let B := 1000*(size q t m)^3 + size q t m + 1000
  have hc : SourceClauseClearExcept.workCount keep ≤ 15 := by decide
  have hs : (∑ i : Fin (SourceClauseClearExcept.workCount keep),
      ((bank5 q t m) (SourceClauseClearExcept.workBank keep i)).length) ≤
      SourceClauseClearExcept.workCount keep * B := by
    calc
      _ ≤ ∑ _i : Fin (SourceClauseClearExcept.workCount keep), B := by
        apply Finset.sum_le_sum
        intro i _
        exact bank5_length_le q t m _
      _ = SourceClauseClearExcept.workCount keep * B := by simp
  have hh := Nat.mul_le_mul_right B hc
  dsimp [clearTime]
  omega

theorem totalTime_polynomial (q t m : ℕ) :
    totalTime q t m ≤ 20000 * (size q t m)^3 +
      100 * size q t m + 20000 := by
  let n := size q t m
  obtain ⟨hmt,hmt2,hscaled⟩ := product_bounds q t m
  change m*t ≤ n^2 at hmt
  change m*t*t ≤ n^3 at hmt2
  change 1000*m*t^2 ≤ 1000*n^3 at hscaled
  have hq : q ≤ n := by dsimp [n, size]; omega
  have hm : m ≤ n := by dsimp [n, size]; omega
  have hx : PrimeSampler.threshold q t m ≤ n := by
    dsimp [n, size]; omega
  have hmx : max q (1000*m*t^2) ≤ PrimeSampler.threshold q t m := by
    unfold PrimeSampler.threshold
    exact Nat.le_max_left _ _
  have hscaledN : 1000*m*t^2 ≤ n := by
    exact (Nat.le_max_right q (1000*m*t^2)).trans (hmx.trans hx)
  have hcm := clearTime_le q t m
  have hconst : constTime = 1005 := by decide
  have hn2 : n^2 ≤ n^3 := by
    have hn : 1 ≤ n := by dsimp [n, size]; omega
    calc n^2 = n^2*1 := by omega
      _ ≤ n^2*n := Nat.mul_le_mul_left _ hn
      _ = n^3 := by ring
  have hmul1 : MatrixAddressMachine.exactTime m t 0 =
      2*(m*t)+4*m+4 := by simp [MatrixAddressMachine.exactTime]; ring
  have hmul2 : MatrixAddressMachine.exactTime (m*t) t 0 =
      2*(m*t*t)+4*(m*t)+4 := by simp [MatrixAddressMachine.exactTime]; ring
  have hmul3 : MatrixAddressMachine.exactTime (m*t*t) 1000 0 =
      2004*(m*t*t)+4 := by simp [MatrixAddressMachine.exactTime]; ring
  unfold totalTime time5 time4 time3 time2 time1
    max2Time max1Time mul3Time mul2Time mul1Time
  rw [hconst]
  rw [hmul1, hmul2, hmul3]
  dsimp only [n] at *
  omega

theorem threshold_run_polynomial (q t m : ℕ) :
    ∃ u ≤ 20000 * (size q t m)^3 +
        100 * size q t m + 20000,
      ((advance program)^[u])
        (⟨some start, controlFinal, initial q t m⟩ :
          TM2.Cfg (fun _ : Stack => Bool) _ _) =
        ⟨none, controlFinal, finalBank q t m⟩ := by
  obtain ⟨u, hu, hr⟩ := threshold_run q t m
  exact ⟨u, hu.trans (totalTime_polynomial q t m), hr⟩

theorem final_slots (q t m : ℕ) :
    (finalBank q t m) 0 = unary q ∧
    (finalBank q t m) 1 = unary t ∧
    (finalBank q t m) 2 = unary m ∧
    (finalBank q t m) 8 = unary (PrimeSampler.threshold q t m) ∧
    (∀ j : Stack, j ≠ 0 → j ≠ 1 → j ≠ 2 → j ≠ 8 →
      finalBank q t m j = []) := by
  simp [finalBank]
  intro j h0 h1 h2 h8
  simp [finalBank, h0, h1, h2, h8]

#print axioms threshold_run_polynomial

end Paper2.WeightedThresholdArithmetic
