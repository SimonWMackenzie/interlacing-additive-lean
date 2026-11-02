import EthInapproximability.CurrentPaper.ETHParameterBinsCoefficient
import EthInapproximability.CurrentPaper.MatrixStage4ScalarPreparationOps
import EthInapproximability.CurrentPaper.BitMachineRawSequence

/-! Physical arithmetic for `2^(100000000*s^4)` from one retained scale word. -/

namespace EthInapproximability.CurrentPaper.BalanceOrderArithmetic

open Turing BitMachineEncoding BitMachineStackEmbedding
open MatrixStage4ScalarPreparationOps

abbrev Stack := Fin 13
abbrev unary (n : ℕ) : List Bool := List.replicate n true

def initial (s : ℕ) : Stack → List Bool :=
  ![unary s, [], [], [], [], [], [], [], [], [], [], [], []]

def coeffSlots : Fin 6 ↪ Stack := ⟨![0,2,3,4,5,6], by decide⟩
def mult1Slots : Fin 6 ↪ Stack := ⟨![0,6,3,4,5,7], by decide⟩
def copySlots : Fin 3 ↪ Stack := ⟨![7,8,9], by decide⟩
def mult2Slots : Fin 6 ↪ Stack := ⟨![7,8,3,4,5,10], by decide⟩
def powerSlots : MatrixUnaryPower.Stack ↪ Stack :=
  ⟨fun k => match k with
    | .inl 0 => 1
    | .inl 1 => 11
    | .inl 2 => 12
    | .inr 0 => 10,
    by decide⟩

def coeffProgram := fun l => stackStmt coeffSlots (ETHBinsCoefficientScratch.program l)
def mult1Program := multiplyProgram mult1Slots
def copyProgram := MatrixStage4ScalarPreparationOps.copyProgram copySlots
def mult2Program := multiplyProgram mult2Slots
def powerProgram := unaryPowerProgram powerSlots

def afterCoeff (s : ℕ) : Stack → List Bool :=
  ![unary s, [], unary 10000, [], [], [], unary (10000*s), [], [], [], [], [], []]
def afterMult1 (s : ℕ) : Stack → List Bool :=
  ![unary s, [], unary 10000, [], [], [], unary (10000*s),
    unary (10000*s^2), [], [], [], [], []]
def afterCopy (s : ℕ) : Stack → List Bool :=
  ![unary s, [], unary 10000, [], [], [], unary (10000*s),
    unary (10000*s^2), unary (10000*s^2), [], [], [], []]
def exponent (s : ℕ) : ℕ := 100000000*s^4
def afterMult2 (s : ℕ) : Stack → List Bool :=
  ![unary s, [], unary 10000, [], [], [], unary (10000*s),
    unary (10000*s^2), unary (10000*s^2), [], unary (exponent s), [], []]
def afterPower (s : ℕ) : Stack → List Bool :=
  Function.update (afterMult2 s) 1 (unary (2^(exponent s)))

theorem arithmetic_identity (s : ℕ) :
    (10000*s^2)*(10000*s^2) = exponent s := by
  unfold exponent
  ring

theorem coeff_run (s : ℕ) :
    ∃ u ≤ ETHBinsCoefficientScratch.time s,
      ((advance coeffProgram)^[u])
        (⟨some .constant,false,initial s⟩ :
          TM2.Cfg (fun _ : Stack => Bool)
            ETHBinsCoefficientScratch.Label Bool) =
        ⟨none,false,afterCoeff s⟩ := by
  obtain ⟨u,hu,hr⟩ := ETHBinsCoefficientScratch.coefficient_run s
  have he := BitMachineStackRun.run coeffSlots (initial s)
    ETHBinsCoefficientScratch.program
    (ETHBinsCoefficientScratch.cfg (some .constant) false
      (ETHBinsCoefficientScratch.inputBank s)) u
  unfold ETHBinsCoefficientScratch.run at hr
  rw [hr] at he
  refine ⟨u,hu,?_⟩
  have hin : bank coeffSlots (initial s)
      (ETHBinsCoefficientScratch.inputBank s) = initial s := by
    apply bank_eq_self
    intro k
    fin_cases k <;> rfl
  have hout : bank coeffSlots (initial s)
      (ETHBinsCoefficientScratch.outputBank s) = afterCoeff s := by
    have hlocal : ETHBinsCoefficientScratch.outputBank s =
        Function.update
          (Function.update (ETHBinsCoefficientScratch.inputBank s)
            1 (unary 10000)) 5 (unary (10000*s)) := by
      funext k
      fin_cases k <;> rfl
    rw [hlocal, bank_update, bank_update, hin]
    funext k
    fin_cases k <;> rfl
  simpa only [coeffProgram, stackCfg,
    ETHBinsCoefficientScratch.cfg, hin, hout] using he

theorem mult1_run (s : ℕ) :
    ((advance mult1Program)^[MatrixAddressMachine.exactTime s (10000*s) 0])
      (⟨some .outer,false,afterCoeff s⟩ :
        TM2.Cfg (fun _ : Stack => Bool) MatrixAddressMachine.Label Bool) =
      ⟨none,false,afterMult1 s⟩ := by
  have hr := multiply_run mult1Slots (afterCoeff s) s (10000*s)
    (by simp [mult1Slots, afterCoeff])
    (by simp [mult1Slots, afterCoeff])
    (by simp [mult1Slots, afterCoeff])
    (by simp [mult1Slots, afterCoeff])
    (by simp [mult1Slots, afterCoeff])
  have hid : s*(10000*s) = 10000*s^2 := by ring
  have hblank : afterCoeff s (mult1Slots 5) = [] := rfl
  rw [hid, hblank, List.append_nil] at hr
  have hout : Function.update (afterCoeff s) 7
      (unary (10000*s^2)) = afterMult1 s := by
    funext k; fin_cases k <;> rfl
  simpa only [mult1Program, show mult1Slots 5 = (7 : Stack) from rfl,
    hout] using hr

theorem copy_run (s : ℕ) :
    ((advance copyProgram)^[2*(10000*s^2)+2])
      (⟨some .scan,none,afterMult1 s⟩ :
        TM2.Cfg (fun _ : Stack => Bool) BitMachineCopy.Label (Option Bool)) =
      ⟨none,none,afterCopy s⟩ := by
  have hr := MatrixStage4ScalarPreparationOps.copy_run
    copySlots (afterMult1 s) (by simp [copySlots, afterMult1])
  have hsrc : afterMult1 s (copySlots 0) = unary (10000*s^2) := rfl
  have hdst : afterMult1 s (copySlots 1) = [] := rfl
  rw [hsrc, hdst, List.append_nil] at hr
  have hout : Function.update (afterMult1 s) 8
      (unary (10000*s^2)) = afterCopy s := by
    funext k; fin_cases k <;> rfl
  simpa only [copyProgram, show copySlots 1 = (8 : Stack) from rfl,
    List.length_replicate,
    Function.iterate_add_apply, hout] using hr

theorem mult2_run (s : ℕ) :
    ((advance mult2Program)^[MatrixAddressMachine.exactTime
      (10000*s^2) (10000*s^2) 0])
      (⟨some .outer,false,afterCopy s⟩ :
        TM2.Cfg (fun _ : Stack => Bool) MatrixAddressMachine.Label Bool) =
      ⟨none,false,afterMult2 s⟩ := by
  have hr := multiply_run mult2Slots (afterCopy s)
    (10000*s^2) (10000*s^2)
    (by simp [mult2Slots, afterCopy])
    (by simp [mult2Slots, afterCopy])
    (by simp [mult2Slots, afterCopy])
    (by simp [mult2Slots, afterCopy])
    (by simp [mult2Slots, afterCopy])
  have hblank : afterCopy s (mult2Slots 5) = [] := rfl
  rw [arithmetic_identity, hblank, List.append_nil] at hr
  have hout : Function.update (afterCopy s) 10
      (unary (exponent s)) = afterMult2 s := by
    funext k; fin_cases k <;> rfl
  simpa only [mult2Program, show mult2Slots 5 = (10 : Stack) from rfl,
    hout] using hr

theorem power_run (s : ℕ) :
    ∃ u ≤ 4*2^(exponent s)+5*(exponent s)+7,
      ((advance powerProgram)^[u])
        (⟨some (.inr false),((false,false),none),afterMult2 s⟩ :
          TM2.Cfg (fun _ : Stack => Bool)
            MatrixUnaryPower.Label MatrixUnaryPower.Control) =
        ⟨none,((false,false),none),afterPower s⟩ := by
  obtain ⟨u,hu,hr⟩ := unary_power_run powerSlots (afterMult2 s)
    (exponent s)
    (by simp [powerSlots, afterMult2])
    (by simp [powerSlots, afterMult2])
    (by simp [powerSlots, afterMult2])
    (by simp [powerSlots, afterMult2])
  exact ⟨u,hu,by simpa [powerProgram, powerSlots, afterPower] using hr⟩

def prog01 := BitMachineRawSequence.program coeffProgram mult1Program
  MatrixAddressMachine.Label.outer false false
def prog012 := BitMachineRawSequence.program prog01 copyProgram
  BitMachineCopy.Label.scan (false,false) none
def prog0123 := BitMachineRawSequence.program prog012 mult2Program
  MatrixAddressMachine.Label.outer ((false,false),none) false
def prog01234 := BitMachineRawSequence.program prog0123 powerProgram
  (.inr false) (((false,false),none),false) ((false,false),none)

def start01 : BitMachineRawSequence.Label ETHBinsCoefficientScratch.Label
    MatrixAddressMachine.Label :=
  BitMachineRawSequence.leftLabel .constant
def start012 : BitMachineRawSequence.Label
    (BitMachineRawSequence.Label ETHBinsCoefficientScratch.Label
      MatrixAddressMachine.Label) BitMachineCopy.Label :=
  BitMachineRawSequence.leftLabel start01
def start0123 : BitMachineRawSequence.Label
    (BitMachineRawSequence.Label
      (BitMachineRawSequence.Label ETHBinsCoefficientScratch.Label
        MatrixAddressMachine.Label) BitMachineCopy.Label)
    MatrixAddressMachine.Label :=
  BitMachineRawSequence.leftLabel start012
def start01234 : BitMachineRawSequence.Label
    (BitMachineRawSequence.Label
      (BitMachineRawSequence.Label
        (BitMachineRawSequence.Label ETHBinsCoefficientScratch.Label
          MatrixAddressMachine.Label) BitMachineCopy.Label)
      MatrixAddressMachine.Label) MatrixUnaryPower.Label :=
  BitMachineRawSequence.leftLabel start0123

def arithmeticTime (s : ℕ) : ℕ :=
  ETHBinsCoefficientScratch.time s +
  MatrixAddressMachine.exactTime s (10000*s) 0 +
  (2*(10000*s^2)+2) +
  MatrixAddressMachine.exactTime (10000*s^2) (10000*s^2) 0 +
  (4*2^(exponent s)+5*(exponent s)+7) + 4

theorem joined_run (s : ℕ) :
    ∃ u ≤ arithmeticTime s,
      ((advance prog01234)^[u])
        (⟨some start01234,
          ((((false,false),none),false),((false,false),none)),initial s⟩ :
          TM2.Cfg (fun _ : Stack => Bool) _ _) =
        ⟨none,((((false,false),none),false),((false,false),none)),afterPower s⟩ := by
  obtain ⟨u0,hu0,h0⟩ := coeff_run s
  have h1 := mult1_run s
  have h2 := copy_run s
  have h3 := mult2_run s
  obtain ⟨u4,hu4,h4⟩ := power_run s
  obtain ⟨u01,hu01,h01⟩ := BitMachineRawSequence.runs
    coeffProgram mult1Program .constant .outer false false false false
    (initial s) (afterCoeff s) (afterMult1 s)
    u0 (MatrixAddressMachine.exactTime s (10000*s) 0) h0 h1
  obtain ⟨u012,hu012,h012⟩ := BitMachineRawSequence.runs
    prog01 copyProgram start01 .scan (false,false) (false,false) none none
    (initial s) (afterMult1 s) (afterCopy s)
    u01 (2*(10000*s^2)+2)
    (by simpa only [prog01, start01] using h01) h2
  obtain ⟨u0123,hu0123,h0123⟩ := BitMachineRawSequence.runs
    prog012 mult2Program start012 .outer
    ((false,false),none) ((false,false),none) false false
    (initial s) (afterCopy s) (afterMult2 s)
    u012 (MatrixAddressMachine.exactTime (10000*s^2) (10000*s^2) 0)
    (by simpa only [prog012, start012] using h012) h3
  obtain ⟨u,hu,hr⟩ := BitMachineRawSequence.runs
    prog0123 powerProgram start0123 (.inr false)
    (((false,false),none),false) (((false,false),none),false)
    ((false,false),none) ((false,false),none)
    (initial s) (afterMult2 s) (afterPower s)
    u0123 u4
    (by simpa only [prog0123, start0123] using h0123) h4
  exact ⟨u, by unfold arithmeticTime; omega,
    by simpa only [prog01234, start01234] using hr⟩

#print axioms coeff_run
#print axioms mult1_run
#print axioms copy_run
#print axioms mult2_run
#print axioms power_run
#print axioms joined_run

end EthInapproximability.CurrentPaper.BalanceOrderArithmetic
