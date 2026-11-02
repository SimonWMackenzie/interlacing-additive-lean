import CurrentAdditive.MinimumRatioCleanupEq

namespace CurrentAdditive.MinimumRatioCallbackPhysical

open Turing EthInapproximability.CurrentPaper BitMachineEncoding
open CurrentAdditive.MinimumRatioCallbackLayout

noncomputable def postCompareBank (S : Bank) (word best : List Bool) : Bank :=
  let pos := MinimumRatioPositiveMachine.result word
  let q := RationalCanonicalCallback.quotientResult word
  let pair := RawRatPairAssembler.pairWord q best.tail
  let S2 := Function.update
    (Function.update
      (Function.update S (low 15) pos) (low 16) q)
    (low 20) best.tail
  Function.update
    (Function.update S2 (low 26) pair)
    (low 18) (RationalLess.result pair)

noncomputable def postItemBank (S : Bank) (word best : List Bool) : Bank :=
  Function.update
    (CurrentAdditive.MinimumRatioBestUpdate.readBank
      (postCompareBank S word best))
    (low 9)
    (CurrentAdditive.MinimumRatioBestUpdate.chosenBest
      (postCompareBank S word best))

noncomputable def itemClock (S : Bank) (word best : List Bool) : Nat :=
  let q := RationalCanonicalCallback.quotientResult word
  let pair := RawRatPairAssembler.pairWord q best.tail
  ((CurrentAdditive.MinimumRatioContext.MachineInvokeFull.uniformBound
      MinimumRatioPositiveMachine.machine word (50*(word.length+1)) +
    CurrentAdditive.MinimumRatioContext.MachineInvokeFull.uniformBound
      RationalCanonicalCallback.quotientMachine word
      (CurrentAdditive.MinimumRatioCallbackCalls.quotientCoefficient *
        (word.length+1)^96) + 1 +
    (2*best.length+4) + 1) +
    (CurrentAdditive.MinimumRatioContext.RawRatPairFull.linearBound
      extraCount q best.tail +
    CurrentAdditive.MinimumRatioContext.MachineInvokeFull.uniformBound
      RationalLess.machine pair
      (RationalLess.coefficient*(pair.length+1)^RationalLess.exponent) + 1)
    + 1) +
  (3 + ((postCompareBank S word best) (low 9)).length + 1 +
    (2*((postCompareBank S word best) (low 16)).length+2) + 1) + 1

abbrev PosLabel :=
  CurrentAdditive.MinimumRatioContext.MachineInvokeFull.LabelFull
    MinimumRatioPositiveMachine.machine
abbrev QuotLabel :=
  CurrentAdditive.MinimumRatioContext.MachineInvokeFull.LabelFull
    RationalCanonicalCallback.quotientMachine
abbrev LessLabel :=
  CurrentAdditive.MinimumRatioContext.MachineInvokeFull.LabelFull
    RationalLess.machine
abbrev FirstTwoLabel := BitMachineRawSequence.Label PosLabel QuotLabel
abbrev CopyTailLabel := BitMachineRawSequence.Label BitMachineCopy.Label Unit
abbrev FirstHalfLabel := BitMachineRawSequence.Label FirstTwoLabel CopyTailLabel
abbrev PairLessLabel := BitMachineRawSequence.Label
  CurrentAdditive.MinimumRatioContext.RawRatPairFull.Label LessLabel
abbrev PreUpdateLabel := BitMachineRawSequence.Label FirstHalfLabel PairLessLabel
abbrev ItemLabel := BitMachineRawSequence.Label PreUpdateLabel
  CurrentAdditive.MinimumRatioBestUpdate.Label

abbrev PosControl :=
  CurrentAdditive.MinimumRatioContext.MachineInvokeFull.ControlFull
    MinimumRatioPositiveMachine.machine
abbrev QuotControl :=
  CurrentAdditive.MinimumRatioContext.MachineInvokeFull.ControlFull
    RationalCanonicalCallback.quotientMachine
abbrev LessControl :=
  CurrentAdditive.MinimumRatioContext.MachineInvokeFull.ControlFull
    RationalLess.machine
abbrev FirstHalfControl := ((PosControl × QuotControl) ×
  (Option Bool × Option Bool))
abbrev PairLessControl :=
  CurrentAdditive.MinimumRatioContext.RawRatPairFull.Control × LessControl
abbrev ItemControl := (FirstHalfControl × PairLessControl) ×
  CurrentAdditive.MinimumRatioBestUpdate.Control

noncomputable def itemStart : ItemLabel :=
  BitMachineRawSequence.leftLabel
    (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel
        (BitMachineRawSequence.leftLabel
          (CurrentAdditive.MinimumRatioContext.MachineInvokeFull.start
            positiveSlots))))

noncomputable def itemControl : ItemControl :=
  ((((CurrentAdditive.MinimumRatioContext.MachineInvokeFull.control
        positiveSlots,
      CurrentAdditive.MinimumRatioContext.MachineInvokeFull.control
        quotientSlots), (none,none)),
    (CurrentAdditive.MinimumRatioContext.RawRatPairFull.control,
      CurrentAdditive.MinimumRatioContext.MachineInvokeFull.control lessSlots)),
    CurrentAdditive.MinimumRatioBestUpdate.initial)

noncomputable def itemFinalControl (S : Bank) (word best : List Bool) :
    ItemControl :=
  ((((CurrentAdditive.MinimumRatioContext.MachineInvokeFull.control
        positiveSlots,
      CurrentAdditive.MinimumRatioContext.MachineInvokeFull.control
        quotientSlots), (none,none)),
    (CurrentAdditive.MinimumRatioContext.RawRatPairFull.control,
      CurrentAdditive.MinimumRatioContext.MachineInvokeFull.control lessSlots)),
    if CurrentAdditive.MinimumRatioBestUpdate.shouldReplace
        (postCompareBank S word best) then
      CurrentAdditive.MinimumRatioBestUpdate.initial else
      ((((postCompareBank S word best) (low 15)).head?,
        ((postCompareBank S word best) (low 9)).head?,
        ((postCompareBank S word best) (low 18)).head?), none))

theorem item_run_api (S : Bank) (word best : List Bool)
    (h6 : S (low 6) = word) (h9 : S (low 9) = best)
    (hscratch : CurrentAdditive.MinimumRatioCallbackFull.ScratchEmpty S) :
    ∃ u ≤ itemClock S word best,
      ((advance CurrentAdditive.MinimumRatioCallbackFull.itemProgram)^[u])
        (⟨some itemStart, itemControl, S⟩ :
          TM2.Cfg (fun _ : Stack => Bool) _ _) =
        ⟨none, itemFinalControl S word best,
          postItemBank S word best⟩ := by
  simpa [itemClock, itemStart, itemControl, itemFinalControl,
    postItemBank, postCompareBank] using
    (CurrentAdditive.MinimumRatioCallbackFull.item_run
      S word best h6 h9 hscratch)

noncomputable def program :=
  BitMachineRawSequence.program
    CurrentAdditive.MinimumRatioCallbackFull.itemProgram
    CurrentAdditive.MinimumRatioExtraClear.program
    (.inl 0) itemControl ((),none)

noncomputable def start :
    BitMachineRawSequence.Label ItemLabel
      CurrentAdditive.MinimumRatioExtraClear.Label :=
  BitMachineRawSequence.leftLabel itemStart
noncomputable def control :
    BitMachineRawSequence.Control ItemControl
      CurrentAdditive.MinimumRatioExtraClear.Control :=
  (itemControl, ((),none))

theorem callback_run (S : Bank) (word best : List Bool)
    (h6 : S (low 6) = word) (h9 : S (low 9) = best)
    (hscratch : CurrentAdditive.MinimumRatioCallbackFull.ScratchEmpty S) :
    ∃ u ≤ itemClock S word best +
        (∑ j : Fin 17,
          ((postItemBank S word best)
            (CurrentAdditive.MinimumRatioExtraClear.extraBank j)).length) + 20,
      ((advance program)^[u])
        (⟨some start, control, S⟩ :
          TM2.Cfg (fun _ : Stack => Bool) _ _) =
        ⟨none, control,
          Function.update S (low 9)
            (CurrentAdditive.MinimumRatioStepSpec.step best word)⟩ := by
  let U := postItemBank S word best
  obtain ⟨a,ha,hrA⟩ := item_run_api S word best h6 h9 hscratch
  have hclean : BitMachineClearBank.cleared
      CurrentAdditive.MinimumRatioExtraClear.extraBank U =
      Function.update S (low 9)
        (CurrentAdditive.MinimumRatioStepSpec.step best word) := by
    simpa [U, postItemBank, postCompareBank] using
      (CurrentAdditive.MinimumRatioCleanupEq.item_cleanup_eq
        S word best h9 hscratch)
  have hrB := CurrentAdditive.MinimumRatioExtraClear.run U
  rw [hclean] at hrB
  obtain ⟨u,hu,hr⟩ := BitMachineRawSequence.runs
    CurrentAdditive.MinimumRatioCallbackFull.itemProgram
    CurrentAdditive.MinimumRatioExtraClear.program
    itemStart (.inl 0) itemControl
    (itemFinalControl S word best) ((),none) ((),none)
    S U (Function.update S (low 9)
      (CurrentAdditive.MinimumRatioStepSpec.step best word))
    a ((∑ j : Fin 17,
      (U (CurrentAdditive.MinimumRatioExtraClear.extraBank j)).length)+19)
    (by simpa [U] using hrA) hrB
  refine ⟨u, ?_, ?_⟩
  · dsimp [U] at hu
    omega
  · simpa [program, start, control, U] using hr

end CurrentAdditive.MinimumRatioCallbackPhysical
