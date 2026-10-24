import EthInapproximability.CurrentPaper.FirstExponentArithmetic
import EthInapproximability.CurrentPaper.ColumnInputStaging
import EthInapproximability.CurrentPaper.ETHParameterScaleActual
import EthInapproximability.CurrentPaper.BitMachineStackRun
import Mathlib.Data.Fin.VecNotation

/-! The actual six-field scale producer, physical squaring, and writer cell 54. -/

namespace EthInapproximability.CurrentPaper.FirstExponentWriterTransfer

open Turing BitMachineEncoding BitMachineStackEmbedding

noncomputable section

abbrev Stack := ETHScaleActualComplete.Stack ⊕ (Fin 64 ⊕ Fin 2)

def scaleSlots : ETHScaleActualComplete.Stack ↪ Stack :=
  ⟨Sum.inl, by intro a b h; exact Sum.inl_injective h⟩

def arithmeticSlots : Fin 4 ↪ Stack :=
  ⟨![.inl (.inr ScaleFinalScratch.answerKey),
     .inr (.inr 0), .inr (.inl 54), .inr (.inr 1)], by decide⟩

def foreignBank (d : MatrixWeightedEntryController.Input) (q L : ℕ) :
    Stack → List Bool
  | .inl _ => []
  | .inr (.inl k) => ColumnInputStaging.partialBank d 0 q L k
  | .inr (.inr _) => []

noncomputable def initialBank (i : Parameters.Input)
    (d : MatrixWeightedEntryController.Input) (q L : ℕ) : Stack → List Bool :=
  bank scaleSlots (foreignBank d q L) (ETHScaleActualComplete.initialBank i)

def scaleProgram := fun l =>
  stackStmt scaleSlots (ETHScaleActualComplete.program l)
def arithmeticProgram := fun l =>
  stackStmt arithmeticSlots (FirstExponentArithmetic.program l)

abbrev ScaleLabel := ETHScaleActualComplete.Label
abbrev ArithmeticLabel := FirstExponentArithmetic.Label
abbrev Label := BitMachineRawSequence.Label ScaleLabel ArithmeticLabel
abbrev Control := ETHScaleActualComplete.Control × FirstExponentArithmetic.Control

def scaleStart : ScaleLabel :=
  BitMachineRawSequence.leftLabel ETHScaleActualComplete.oldStart
def scaleControl : ETHScaleActualComplete.Control :=
  (ETHScaleActualComplete.oldControl, ETHScaleActualComplete.finalControl)
def arithmeticStart : ArithmeticLabel :=
  BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan
def arithmeticControl : FirstExponentArithmetic.Control := (none,false)

def program := BitMachineRawSequence.program scaleProgram arithmeticProgram
  arithmeticStart scaleControl arithmeticControl

def totalBound (i : Parameters.Input) :=
  ETHScaleActualComplete.totalBound i +
    FirstExponentArithmetic.bound (Parameters.scale i) + 1

private theorem partial_zero (d : MatrixWeightedEntryController.Input) (q L : ℕ) :
    ColumnInputStaging.partialBank d 0 q L 54 = [] := by
  simp [ColumnInputStaging.partialBank, ColumnInputStaging.partialLocalBank,
    show (54 : Fin 64) = ColumnWriterJoin.slots 0 from rfl,
    bank_at]

private theorem partial_update (d : MatrixWeightedEntryController.Input)
    (a q L : ℕ) :
    ColumnInputStaging.partialBank d a q L =
      Function.update (ColumnInputStaging.partialBank d 0 q L) 54
        (List.replicate a true) := by
  have hlocal : ColumnInputStaging.partialLocalBank a q L =
      Function.update (ColumnInputStaging.partialLocalBank 0 q L) 0
        (List.replicate a true) := by
    funext k
    fin_cases k <;> simp [ColumnInputStaging.partialLocalBank]
  rw [ColumnInputStaging.partialBank, hlocal,
    bank_update, ColumnInputStaging.partialBank]
  rfl

private theorem arith_restrict (d : MatrixWeightedEntryController.Input)
    (q L : ℕ) (i : Parameters.Input)
    (F : ETHScaleActualComplete.Stack → List Bool)
    (hscale : F (.inr ScaleFinalScratch.answerKey) =
      List.replicate (Parameters.scale i) true) :
    (fun k => (bank scaleSlots (foreignBank d q L) F) (arithmeticSlots k)) =
      FirstExponentArithmetic.initialBank (Parameters.scale i) := by
  funext k
  fin_cases k
  · change bank scaleSlots (foreignBank d q L) F
      (scaleSlots (.inr ScaleFinalScratch.answerKey)) = _
    rw [bank_at]
    exact hscale
  · simp [arithmeticSlots, FirstExponentArithmetic.initialBank,
      scaleSlots, bank_outside, foreignBank]
  · simp [arithmeticSlots, FirstExponentArithmetic.initialBank,
      scaleSlots, bank_outside, foreignBank, partial_zero]
  · simp [arithmeticSlots, FirstExponentArithmetic.initialBank,
      scaleSlots, bank_outside, foreignBank]

private theorem arith_final_update (d : MatrixWeightedEntryController.Input)
    (q L : ℕ) (i : Parameters.Input)
    (F : ETHScaleActualComplete.Stack → List Bool)
    (hscale : F (.inr ScaleFinalScratch.answerKey) =
      List.replicate (Parameters.scale i) true) :
    bank arithmeticSlots (bank scaleSlots (foreignBank d q L) F)
      (FirstExponentArithmetic.finalBank (Parameters.scale i)) =
    Function.update (bank scaleSlots (foreignBank d q L) F)
      (.inr (.inl 54)) (List.replicate (Parameters.firstExponent i) true) := by
  let S := bank scaleSlots (foreignBank d q L) F
  have hlocal : FirstExponentArithmetic.finalBank (Parameters.scale i) =
      Function.update (fun k => S (arithmeticSlots k)) 2
        (List.replicate (Parameters.firstExponent i) true) := by
    rw [arith_restrict d q L i F hscale]
    funext k
    fin_cases k <;> simp [FirstExponentArithmetic.initialBank,
      FirstExponentArithmetic.finalBank, Parameters.firstExponent]
  rw [hlocal, bank_update, bank_restrict]
  rfl

private theorem writer_projection (d : MatrixWeightedEntryController.Input)
    (q L a : ℕ) (F : ETHScaleActualComplete.Stack → List Bool) :
    (fun k : Fin 64 =>
      (Function.update (bank scaleSlots (foreignBank d q L) F)
        (.inr (.inl 54)) (List.replicate a true)) (.inr (.inl k))) =
      ColumnInputStaging.partialBank d a q L := by
  rw [partial_update]
  funext k
  by_cases hk : k = 54
  · subst k
    simp
  · have hout : ¬ ∃ j : ETHScaleActualComplete.Stack,
        scaleSlots j = (.inr (.inl k) : Stack) := by
      rintro ⟨j,h⟩; cases h
    simp [Function.update_of_ne, hk,
      bank_outside scaleSlots (foreignBank d q L) F _ hout,
      foreignBank]

/-- The initial bank has the six actual raw scale inputs, an independently
staged q/L writer bank with cell 54 blank, and two blank arithmetic work
cells. The result retains the scale machine's whole bank, physically writes
the exact source firstExponent into cell 54, and leaves the complete writer
projection at ColumnInputStaging's input boundary. -/
theorem actual_firstExponent_to_writer (i : Parameters.Input)
    (d : MatrixWeightedEntryController.Input) (q L : ℕ) :
    ∃ t ≤ totalBound i, ∃ F : ETHScaleActualComplete.Stack → List Bool,
      ((advance program)^[t])
        (⟨some (BitMachineRawSequence.leftLabel scaleStart),
          (scaleControl,arithmeticControl), initialBank i d q L⟩ :
          TM2.Cfg (fun _ : Stack => Bool) Label Control) =
        ⟨none,(scaleControl,arithmeticControl),
          Function.update (bank scaleSlots (foreignBank d q L) F)
            (.inr (.inl 54))
            (List.replicate (Parameters.firstExponent i) true)⟩ ∧
      F (.inr ScaleFinalScratch.answerKey) =
        List.replicate (Parameters.scale i) true ∧
      (∀ j : Fin 6, F (.inl (ETHScaleGlobalLog.raw j)) =
        ETHParameterScaleMachineInput.words i j) ∧
      (fun k : Fin 64 =>
        (Function.update (bank scaleSlots (foreignBank d q L) F)
          (.inr (.inl 54))
          (List.replicate (Parameters.firstExponent i) true)) (.inr (.inl k))) =
        ColumnInputStaging.partialBank d (Parameters.firstExponent i) q L := by
  obtain ⟨ts,hts,F,hs,hscale,_,hraw⟩ := ETHScaleActualComplete.actual_scale_run i
  let S := bank scaleSlots (foreignBank d q L) F
  have hs' : ((advance scaleProgram)^[ts])
      (⟨some scaleStart,scaleControl,initialBank i d q L⟩ :
        TM2.Cfg (fun _ : Stack => Bool) ScaleLabel ETHScaleActualComplete.Control) =
      ⟨none,(ETHScaleActualComplete.oldControl,ScaleFinalScratch.base,none),S⟩ := by
    have he := BitMachineStackRun.run scaleSlots (foreignBank d q L)
      ETHScaleActualComplete.program
      (⟨some scaleStart,scaleControl,ETHScaleActualComplete.initialBank i⟩ :
        TM2.Cfg (fun _ : ETHScaleActualComplete.Stack => Bool)
          ScaleLabel ETHScaleActualComplete.Control) ts
    have hs0 : ((advance ETHScaleActualComplete.program)^[ts])
        (⟨some scaleStart,scaleControl,ETHScaleActualComplete.initialBank i⟩ :
          TM2.Cfg (fun _ : ETHScaleActualComplete.Stack => Bool)
            ScaleLabel ETHScaleActualComplete.Control) =
        ⟨none,(ETHScaleActualComplete.oldControl,ScaleFinalScratch.base,none),F⟩ := by
      simpa only [scaleStart, scaleControl] using hs
    rw [hs0] at he
    simpa only [scaleProgram, initialBank, S, scaleStart, scaleControl,
      stackCfg] using he
  have hlocal := arith_restrict d q L i F hscale
  obtain ⟨ta,hta,ha⟩ := FirstExponentArithmetic.exact_run (Parameters.scale i)
  have hbase : bank arithmeticSlots S
      (FirstExponentArithmetic.initialBank (Parameters.scale i)) = S :=
    bank_eq_self arithmeticSlots S _ (fun k => (congrFun hlocal k).symm)
  have ha' : ((advance arithmeticProgram)^[ta])
      (⟨some arithmeticStart,arithmeticControl,S⟩ :
        TM2.Cfg (fun _ : Stack => Bool) ArithmeticLabel FirstExponentArithmetic.Control) =
      ⟨none,arithmeticControl,
        Function.update S (.inr (.inl 54))
          (List.replicate (Parameters.firstExponent i) true)⟩ := by
    have he := BitMachineStackRun.run arithmeticSlots S
      FirstExponentArithmetic.program
      (⟨some arithmeticStart,arithmeticControl,
        FirstExponentArithmetic.initialBank (Parameters.scale i)⟩ :
        TM2.Cfg (fun _ : Fin 4 => Bool)
          ArithmeticLabel FirstExponentArithmetic.Control) ta
    have ha0 : ((advance FirstExponentArithmetic.program)^[ta])
        (⟨some arithmeticStart,arithmeticControl,
          FirstExponentArithmetic.initialBank (Parameters.scale i)⟩ :
          TM2.Cfg (fun _ : Fin 4 => Bool)
            ArithmeticLabel FirstExponentArithmetic.Control) =
        ⟨none,arithmeticControl,
          FirstExponentArithmetic.finalBank (Parameters.scale i)⟩ := by
      simpa only [arithmeticStart, arithmeticControl] using ha
    rw [ha0] at he
    simpa only [arithmeticProgram, arithmeticStart, arithmeticControl,
      stackCfg, hbase, S, arith_final_update d q L i F hscale] using he
  obtain ⟨t,ht,hr⟩ := BitMachineRawSequence.runs
    scaleProgram arithmeticProgram scaleStart arithmeticStart
    scaleControl (ETHScaleActualComplete.oldControl,ScaleFinalScratch.base,none)
    arithmeticControl arithmeticControl
    (initialBank i d q L) S
    (Function.update S (.inr (.inl 54))
      (List.replicate (Parameters.firstExponent i) true))
    ts ta hs' ha'
  refine ⟨t, by unfold totalBound; omega, F, ?_, hscale, hraw, ?_⟩
  · simpa only [program, S] using hr
  · exact writer_projection d q L (Parameters.firstExponent i) F

#print axioms actual_firstExponent_to_writer

end
end EthInapproximability.CurrentPaper.FirstExponentWriterTransfer
