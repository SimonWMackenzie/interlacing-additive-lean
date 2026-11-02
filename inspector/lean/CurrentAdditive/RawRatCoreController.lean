import CurrentAdditive.RawRatSecondQuotientController
import Mathlib.Tactic

/-! Fixed 13-bank physical rational-normalization core. -/
namespace CurrentAdditive.RawRatCoreController

open Turing EthInapproximability.CurrentPaper BitMachineEncoding
open CurrentAdditive.CodeDCodec

abbrev FirstControl :=
  (RawRatPreGCD.PrepControl × RawRatPreGCD.GCDControl) ×
    (((Unit × Option Bool) × Option Bool) ×
      (BitMachineBinaryDivision.Control × Option Bool))

abbrev SecondControl :=
  ((((Unit × Option Bool) × Option Bool) ×
      (BitMachineBinaryDivision.Control × Option Bool)) ×
    (Option Bool × RawRatSignCleanup.Control))

def firstInitial : FirstControl :=
  ((((none, none), (none, none)),
      (((), none), BinaryGCDCore.initial)),
    ((((), none), none), (BitMachineBinaryDivision.initial, none)))

def secondInitial : SecondControl :=
  (((((), none), none), (BitMachineBinaryDivision.initial, none)),
    (none, ((), none)))

def program := BitMachineRawSequence.program
  RawRatFirstQuotientController.program
  RawRatSecondQuotientController.program
  (BitMachineRawSequence.leftLabel
    (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel (0 : Fin 8))))
  firstInitial secondInitial

noncomputable def result (r : RawRat) : RawRatPreparation.Bank :=
  RawRatSecondQuotientController.result r

noncomputable def clock (r : RawRat) : Nat :=
  RawRatFirstQuotientController.clock r +
    RawRatSecondQuotientController.clock r + 1

theorem run (r : RawRat) :
    ∃ (t : Nat) (v : RawRatSignCleanup.Control), t ≤ clock r ∧
      ((advance program)^[t])
        (⟨some (BitMachineRawSequence.leftLabel
            (BitMachineRawSequence.leftLabel
              (BitMachineRawSequence.leftLabel
                (BitMachineRawSequence.leftLabel
                  (BitMachineRawSequence.leftLabel
                    BitMachineCopy.Label.scan))))),
          (firstInitial, secondInitial),
          RawRatPreparation.inputBank r⟩ :
          TM2.Cfg (fun _ : Fin 13 => Bool) _ _) =
        ⟨none, (firstInitial,
          (((((), none), none), (BitMachineBinaryDivision.initial, none)),
            (none, v))), result r⟩ := by
  obtain ⟨ta, hta, ha⟩ := RawRatFirstQuotientController.run r
  obtain ⟨tb, v, htb, hb⟩ := RawRatSecondQuotientController.run r
  obtain ⟨t, ht, h⟩ := BitMachineRawSequence.runs
    RawRatFirstQuotientController.program
    RawRatSecondQuotientController.program
    (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel
        (BitMachineRawSequence.leftLabel
          (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan))))
    (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel
        (BitMachineRawSequence.leftLabel (0 : Fin 8))))
    firstInitial firstInitial secondInitial
    (((((), none), none), (BitMachineBinaryDivision.initial, none)),
      (none, v))
    (RawRatPreparation.inputBank r)
    (RawRatNumeratorCanonical.result r) (result r) ta tb ha hb
  exact ⟨t, v, by unfold clock; omega, h⟩

end CurrentAdditive.RawRatCoreController
