import EthInapproximability.CurrentPaper.BalanceOrderCleanup
import EthInapproximability.CurrentPaper.ETHParameterScaleActual
import EthInapproximability.CurrentPaper.BitMachineStackRun

/-! The actual raw parameter scale, physically copied to the balance-order
arithmetic bank; all source stacks remain intact. -/

namespace EthInapproximability.CurrentPaper.BalanceOrderActualScale

open Turing BitMachineEncoding BitMachineStackEmbedding
open BalanceOrderArithmetic (unary exponent initial afterPower)
open BalanceOrderCleanup (finalBank fullProgram)

noncomputable section

abbrev Stack := ETHScaleActualComplete.Stack ⊕ BalanceOrderArithmetic.Stack
def scaleSlots : ETHScaleActualComplete.Stack ↪ Stack :=
  ⟨Sum.inl, by intro a b h; exact Sum.inl_injective h⟩
def arithmeticSlots : BalanceOrderArithmetic.Stack ↪ Stack :=
  ⟨Sum.inr, by intro a b h; exact Sum.inr_injective h⟩
def copySlots : Fin 3 ↪ Stack :=
  ⟨![.inl (.inr ScaleFinalScratch.answerKey),.inr 0,.inr 2], by decide⟩

def foreignBank : Stack → List Bool := fun _ => []
def initialBank (i : Parameters.Input) : Stack → List Bool :=
  bank scaleSlots foreignBank (ETHScaleActualComplete.initialBank i)

def scaleProgram := fun l => stackStmt scaleSlots (ETHScaleActualComplete.program l)
def copyProgram := MatrixStage4ScalarPreparationOps.copyProgram copySlots
def arithmeticProgram := fun l => stackStmt arithmeticSlots (fullProgram l)

def scaleStart : ETHScaleActualComplete.Label :=
  BitMachineRawSequence.leftLabel ETHScaleActualComplete.oldStart
def scaleControl : ETHScaleActualComplete.Control :=
  (ETHScaleActualComplete.oldControl,ETHScaleActualComplete.finalControl)
abbrev ArithmeticLabel := BitMachineRawSequence.Label
  (BitMachineRawSequence.Label
    (BitMachineRawSequence.Label
      (BitMachineRawSequence.Label
        (BitMachineRawSequence.Label ETHBinsCoefficientScratch.Label
          MatrixAddressMachine.Label) BitMachineCopy.Label)
      MatrixAddressMachine.Label) MatrixUnaryPower.Label)
  BalanceOrderCleanup.Label
abbrev ArithmeticControl := BitMachineRawSequence.Control
  (BitMachineRawSequence.Control
    (BitMachineRawSequence.Control
      (BitMachineRawSequence.Control
        (BitMachineRawSequence.Control Bool Bool) (Option Bool))
      Bool) MatrixUnaryPower.Control)
  (Unit × Option Bool)
def arithmeticControl : ArithmeticControl :=
  (((((false,false),none),false),((false,false),none)),((),none))

def scaleCopyProgram := BitMachineRawSequence.program scaleProgram copyProgram
  BitMachineCopy.Label.scan scaleControl none
def scaleCopyStart := BitMachineRawSequence.leftLabel (LB := BitMachineCopy.Label)
  scaleStart
def program := BitMachineRawSequence.program scaleCopyProgram arithmeticProgram
  BalanceOrderCleanup.start (scaleControl,none) arithmeticControl
def start := BitMachineRawSequence.leftLabel
  (LB := ArithmeticLabel) scaleCopyStart

def totalBound (i : Parameters.Input) : ℕ :=
  ETHScaleActualComplete.totalBound i +
  (2*Parameters.scale i+2) +
  BalanceOrderCleanup.fullTime (Parameters.scale i) + 2

private theorem copy_restrict (F : ETHScaleActualComplete.Stack → List Bool)
    (s : ℕ) (hs : F (.inr ScaleFinalScratch.answerKey) = unary s) :
    (bank scaleSlots foreignBank F) (copySlots 0) = unary s ∧
    (bank scaleSlots foreignBank F) (copySlots 1) = [] ∧
    (bank scaleSlots foreignBank F) (copySlots 2) = [] := by
  constructor
  · change bank scaleSlots foreignBank F
      (scaleSlots (.inr ScaleFinalScratch.answerKey)) = _
    rw [bank_at]; exact hs
  constructor <;> simp [copySlots, bank_outside, scaleSlots, foreignBank]

private theorem arithmetic_restrict (F : ETHScaleActualComplete.Stack → List Bool)
    (s : ℕ) :
    (fun k => (Function.update (bank scaleSlots foreignBank F) (.inr 0)
      (unary s)) (arithmeticSlots k)) = initial s := by
  funext k
  fin_cases k <;> simp [arithmeticSlots, initial, bank_outside,
    scaleSlots, foreignBank]

private theorem final_update (F : ETHScaleActualComplete.Stack → List Bool)
    (s : ℕ) :
    bank arithmeticSlots
      (Function.update (bank scaleSlots foreignBank F) (.inr 0) (unary s))
      (finalBank s) =
    Function.update
      (Function.update (bank scaleSlots foreignBank F) (.inr 0) (unary s))
      (.inr 1) (unary (2^(exponent s))) := by
  have hlocal : finalBank s = Function.update (initial s) 1
      (unary (2^(exponent s))) := by
    funext k; fin_cases k <;> rfl
  rw [hlocal, bank_update]
  exact congrArg (fun B : Stack → List Bool =>
    Function.update B (.inr 1) (unary (2^(exponent s))))
    (bank_eq_self arithmeticSlots _ _
      (fun k => (congrFun (arithmetic_restrict F s) k).symm))

/-- Actual six-word parameter input, not a supplied scale or balance word.
The full scale bank (including raw words) is retained; the disjoint output
bank contains exactly the copied scale and computed balance order. -/
theorem actual_balance_order_run (i : Parameters.Input) :
    ∃ u ≤ totalBound i, ∃ F : ETHScaleActualComplete.Stack → List Bool,
      ((advance program)^[u])
        (⟨some start,((scaleControl,none),arithmeticControl),initialBank i⟩ :
          TM2.Cfg (fun _ : Stack => Bool) _ _) =
        ⟨none,((scaleControl,none),arithmeticControl),
          Function.update
            (Function.update (bank scaleSlots foreignBank F) (.inr 0)
              (unary (Parameters.scale i)))
            (.inr 1) (unary (Parameters.balanceOrder i))⟩ ∧
      F (.inr ScaleFinalScratch.answerKey) = unary (Parameters.scale i) ∧
      (∀ j : Fin 6, F (.inl (ETHScaleGlobalLog.raw j)) =
        ETHParameterScaleMachineInput.words i j) := by
  obtain ⟨ts,hts,F,hs,hscale,_,hraw⟩ := ETHScaleActualComplete.actual_scale_run i
  let s := Parameters.scale i
  let S := bank scaleSlots foreignBank F
  have hs' : ((advance scaleProgram)^[ts])
      (⟨some scaleStart,scaleControl,initialBank i⟩ :
        TM2.Cfg (fun _ : Stack => Bool) _ _) =
      ⟨none,(ETHScaleActualComplete.oldControl,ScaleFinalScratch.base,none),S⟩ := by
    have he := BitMachineStackRun.run scaleSlots foreignBank
      ETHScaleActualComplete.program
      (⟨some scaleStart,scaleControl,ETHScaleActualComplete.initialBank i⟩ :
        TM2.Cfg (fun _ : ETHScaleActualComplete.Stack => Bool) _ _) ts
    have hs0 : ((advance ETHScaleActualComplete.program)^[ts])
      (⟨some scaleStart,scaleControl,ETHScaleActualComplete.initialBank i⟩ :
        TM2.Cfg (fun _ : ETHScaleActualComplete.Stack => Bool) _ _) =
      ⟨none,(ETHScaleActualComplete.oldControl,ScaleFinalScratch.base,none),F⟩ := by
      simpa only [scaleStart, scaleControl] using hs
    rw [hs0] at he
    simpa only [scaleProgram, initialBank, S, stackCfg] using he
  obtain ⟨hsrc,hdst,hscr⟩ := copy_restrict F s hscale
  have hc := MatrixStage4ScalarPreparationOps.copy_run copySlots S hscr
  change S (copySlots 0) = unary s at hsrc
  change S (copySlots 1) = [] at hdst
  rw [hsrc, hdst, List.append_nil] at hc
  have hc' : ((advance copyProgram)^[2*s+2])
      (⟨some .scan,none,S⟩ : TM2.Cfg (fun _ : Stack => Bool) _ _) =
      ⟨none,none,Function.update S (.inr 0) (unary s)⟩ := by
    simpa only [copyProgram, S, List.length_replicate,
      show copySlots 1 = (.inr 0 : Stack) from rfl] using hc
  obtain ⟨u01,hu01,h01⟩ := BitMachineRawSequence.runs
    scaleProgram copyProgram scaleStart .scan scaleControl
    (ETHScaleActualComplete.oldControl,ScaleFinalScratch.base,none)
    none none (initialBank i) S
    (Function.update S (.inr 0) (unary s)) ts (2*s+2) hs' hc'
  obtain ⟨ua,hua,ha⟩ := BalanceOrderCleanup.balance_order_run s
  let T := Function.update S (.inr 0) (unary s)
  have hbase : bank arithmeticSlots T (initial s) = T :=
    bank_eq_self arithmeticSlots T _
      (fun k => (congrFun (arithmetic_restrict F s) k).symm)
  have ha' : ((advance arithmeticProgram)^[ua])
      (⟨some BalanceOrderCleanup.start,arithmeticControl,T⟩ :
        TM2.Cfg (fun _ : Stack => Bool) _ _) =
      ⟨none,arithmeticControl,
        Function.update T (.inr 1) (unary (2^(exponent s)))⟩ := by
    have he := BitMachineStackRun.run arithmeticSlots T fullProgram
      (⟨some BalanceOrderCleanup.start,arithmeticControl,initial s⟩ :
        TM2.Cfg (fun _ : BalanceOrderArithmetic.Stack => Bool) _ _) ua
    change ((advance fullProgram)^[ua])
      (⟨some BalanceOrderCleanup.start,arithmeticControl,initial s⟩ :
        TM2.Cfg (fun _ : BalanceOrderArithmetic.Stack => Bool) _ _) =
      ⟨none,arithmeticControl,finalBank s⟩ at ha
    rw [ha] at he
    have hfinal : bank arithmeticSlots T (finalBank s) =
        Function.update T (.inr 1) (unary (2^(exponent s))) :=
      final_update F s
    dsimp only [stackCfg] at he
    rw [hfinal] at he
    simpa only [arithmeticProgram, stackCfg, hbase] using he
  obtain ⟨u,hu,hr⟩ := BitMachineRawSequence.runs
    scaleCopyProgram arithmeticProgram scaleCopyStart BalanceOrderCleanup.start
    (scaleControl,none) (scaleControl,none)
    arithmeticControl arithmeticControl
    (initialBank i) T
    (Function.update T (.inr 1) (unary (2^(exponent s))))
    u01 ua (by simpa only [scaleCopyProgram, scaleCopyStart, T] using h01) ha'
  refine ⟨u, by unfold totalBound; dsimp [s] at hu01 hua; omega,
    F, ?_, hscale, hraw⟩
  have hbalance : 2^(exponent s) = Parameters.balanceOrder i := by
    simp [s, exponent, Parameters.balanceOrder, Parameters.balanceExponent]
  simpa only [program, start, T, S, s, hbalance] using hr

#print axioms actual_balance_order_run

end
end EthInapproximability.CurrentPaper.BalanceOrderActualScale
