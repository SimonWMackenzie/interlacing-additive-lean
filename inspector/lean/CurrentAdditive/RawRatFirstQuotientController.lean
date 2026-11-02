import CurrentAdditive.RawRatPreGCD
import CurrentAdditive.RawRatNumeratorCanonical
import Mathlib.Tactic

/-! One fixed controller for the GCD and canonical numerator quotient. -/
namespace CurrentAdditive.RawRatFirstQuotientController

open Turing EthInapproximability.CurrentPaper BitMachineEncoding
open CurrentAdditive.CodeDCodec

def clearMove := BitMachineRawSequence.program
  RawRatClearArithmetic.program
  (RawRatReverseTransfer.program (5 : Fin 13) 3)
  RawRatReverseTransfer.Label.move
  (((), none) : Unit × Option Bool) (none : Option Bool)

def divideCanon := BitMachineRawSequence.program
  RawRatDivisionEmbedded.program
  (RawRatCanonEmbedded.program RawRatNumeratorCanonical.location)
  BG34Canon.Label.rev
  BitMachineBinaryDivision.initial (none : Option Bool)

def quotient := BitMachineRawSequence.program clearMove divideCanon
  (BitMachineRawSequence.leftLabel BitMachineBinaryDivision.Label.outer)
  ((((), none), none) : (Unit × Option Bool) × Option Bool)
  ((BitMachineBinaryDivision.initial, none) :
    BitMachineBinaryDivision.Control × Option Bool)

def program := BitMachineRawSequence.program RawRatPreGCD.program quotient
  (BitMachineRawSequence.leftLabel
    (BitMachineRawSequence.leftLabel (0 : Fin 8)))
  (((none, none), (none, none)), (((), none), BinaryGCDCore.initial))
  (((((), none), none), (BitMachineBinaryDivision.initial, none)) :
    ((Unit × Option Bool) × Option Bool) ×
      (BitMachineBinaryDivision.Control × Option Bool))

theorem clearMove_run (r : RawRat) :
    ∃ t ≤ RawRatClearArithmetic.clock (RawRatGCDStage.result r) +
      r.numerator.length + 2,
      ((advance clearMove)^[t])
        (⟨some (BitMachineRawSequence.leftLabel (0 : Fin 8)),
          (((), none), none), RawRatGCDStage.result r⟩ :
          TM2.Cfg (fun _ : Fin 13 => Bool) _ _) =
        ⟨none, (((), none), none), RawRatNumeratorDivision.dividendReady r⟩ := by
  obtain ⟨tc, htc, hc⟩ := RawRatNumeratorDivision.clear_run r
  obtain ⟨t, ht, h⟩ := BitMachineRawSequence.runs
    RawRatClearArithmetic.program
    (RawRatReverseTransfer.program (5 : Fin 13) 3)
    (0 : Fin 8) RawRatReverseTransfer.Label.move
    (((), none) : Unit × Option Bool) (((), none) : Unit × Option Bool)
    (none : Option Bool) none
    (RawRatGCDStage.result r) (RawRatNumeratorDivision.cleared r)
    (RawRatNumeratorDivision.dividendReady r)
    tc (r.numerator.length + 1) hc (RawRatNumeratorDivision.move_run r)
  exact ⟨t, by omega, h⟩

theorem divideCanon_run (r : RawRat) :
    ∃ t ≤ RawRatDivisionEmbedded.clock
        (RawRatNumeratorDivision.dividendReady r) +
      RawRatCanonEmbedded.clock RawRatNumeratorCanonical.location
        (RawRatNumeratorDivision.divided r) + 1,
      ((advance divideCanon)^[t])
        (⟨some (BitMachineRawSequence.leftLabel
            BitMachineBinaryDivision.Label.outer),
          (BitMachineBinaryDivision.initial, none),
          RawRatNumeratorDivision.dividendReady r⟩ :
          TM2.Cfg (fun _ : Fin 13 => Bool) _ _) =
        ⟨none, (BitMachineBinaryDivision.initial, none),
          RawRatNumeratorCanonical.result r⟩ := by
  obtain ⟨t, ht, h⟩ := BitMachineRawSequence.runs
    RawRatDivisionEmbedded.program
    (RawRatCanonEmbedded.program RawRatNumeratorCanonical.location)
    BitMachineBinaryDivision.Label.outer BG34Canon.Label.rev
    BitMachineBinaryDivision.initial BitMachineBinaryDivision.initial
    (none : Option Bool) none
    (RawRatNumeratorDivision.dividendReady r)
    (RawRatNumeratorDivision.divided r)
    (RawRatNumeratorCanonical.result r)
    (RawRatDivisionEmbedded.clock (RawRatNumeratorDivision.dividendReady r))
    (RawRatCanonEmbedded.clock RawRatNumeratorCanonical.location
      (RawRatNumeratorDivision.divided r))
    (RawRatNumeratorDivision.divide_run r)
    (RawRatNumeratorCanonical.physical_run r)
  exact ⟨t, ht, h⟩

theorem quotient_run (r : RawRat) :
    ∃ t ≤ RawRatClearArithmetic.clock (RawRatGCDStage.result r) +
      r.numerator.length + 2 +
      (RawRatDivisionEmbedded.clock (RawRatNumeratorDivision.dividendReady r) +
       RawRatCanonEmbedded.clock RawRatNumeratorCanonical.location
         (RawRatNumeratorDivision.divided r) + 1) + 1,
      ((advance quotient)^[t])
        (⟨some (BitMachineRawSequence.leftLabel
            (BitMachineRawSequence.leftLabel (0 : Fin 8))),
          ((((), none), none),
            (BitMachineBinaryDivision.initial, none)),
          RawRatGCDStage.result r⟩ : TM2.Cfg (fun _ : Fin 13 => Bool) _ _) =
        ⟨none, ((((), none), none),
          (BitMachineBinaryDivision.initial, none)),
          RawRatNumeratorCanonical.result r⟩ := by
  obtain ⟨ta, hta, ha⟩ := clearMove_run r
  obtain ⟨tb, htb, hb⟩ := divideCanon_run r
  obtain ⟨t, ht, h⟩ := BitMachineRawSequence.runs clearMove divideCanon
    (BitMachineRawSequence.leftLabel (0 : Fin 8))
    (BitMachineRawSequence.leftLabel BitMachineBinaryDivision.Label.outer)
    ((((), none), none) : (Unit × Option Bool) × Option Bool)
    ((((), none), none) : (Unit × Option Bool) × Option Bool)
    (BitMachineBinaryDivision.initial, none)
    (BitMachineBinaryDivision.initial, none)
    (RawRatGCDStage.result r) (RawRatNumeratorDivision.dividendReady r)
    (RawRatNumeratorCanonical.result r) ta tb ha hb
  exact ⟨t, by omega, h⟩

noncomputable def clock (r : RawRat) : Nat :=
  RawRatPreGCD.clock r +
    RawRatClearArithmetic.clock (RawRatGCDStage.result r) +
    r.numerator.length + 2 +
    RawRatDivisionEmbedded.clock (RawRatNumeratorDivision.dividendReady r) +
    RawRatCanonEmbedded.clock RawRatNumeratorCanonical.location
      (RawRatNumeratorDivision.divided r) + 3

theorem run (r : RawRat) :
    ∃ (t : Nat), t ≤ clock r ∧
      ((advance program)^[t])
        (⟨some (BitMachineRawSequence.leftLabel
            (BitMachineRawSequence.leftLabel
              (BitMachineRawSequence.leftLabel
                (BitMachineRawSequence.leftLabel
                  BitMachineCopy.Label.scan)))),
          ((((none, none), (none, none)),
              (((), none), BinaryGCDCore.initial)),
            ((((), none), none),
              (BitMachineBinaryDivision.initial, none))),
          RawRatPreparation.inputBank r⟩ :
          TM2.Cfg (fun _ : Fin 13 => Bool) _ _) =
        ⟨none,
          ((((none, none), (none, none)),
              (((), none), BinaryGCDCore.initial)),
            ((((), none), none),
              (BitMachineBinaryDivision.initial, none))),
          RawRatNumeratorCanonical.result r⟩ := by
  obtain ⟨ta, v, hta, ha⟩ := RawRatPreGCD.run r
  obtain ⟨tb, htb, hb⟩ := quotient_run r
  obtain ⟨t, ht, h⟩ := BitMachineRawSequence.runs
    RawRatPreGCD.program quotient
    (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel
        (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan)))
    (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel (0 : Fin 8)))
    ((((none, none), (none, none)),
      (((), none), BinaryGCDCore.initial)))
    ((((none, none), (none, none)), v))
    (((((), none), none),
      (BitMachineBinaryDivision.initial, none)))
    (((((), none), none),
      (BitMachineBinaryDivision.initial, none)))
    (RawRatPreparation.inputBank r) (RawRatGCDStage.result r)
    (RawRatNumeratorCanonical.result r) ta tb ha hb
  exact ⟨t, by unfold clock; omega, h⟩

end CurrentAdditive.RawRatFirstQuotientController
