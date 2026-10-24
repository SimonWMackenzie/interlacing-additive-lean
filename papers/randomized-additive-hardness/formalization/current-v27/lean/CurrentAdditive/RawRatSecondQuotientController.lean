import CurrentAdditive.RawRatFirstQuotientController
import CurrentAdditive.RawRatSignCleanup
import Mathlib.Tactic

/-! One fixed controller for the canonical denominator and zero-sign rule. -/
namespace CurrentAdditive.RawRatSecondQuotientController

open Turing EthInapproximability.CurrentPaper BitMachineEncoding
open CurrentAdditive.CodeDCodec

def clearCopy := BitMachineRawSequence.program
  RawRatClearArithmetic.program
  (RawRatCopyEmbedded.program RawRatDenominatorDivision.copyLocation)
  BitMachineCopy.Label.scan
  (((), none) : Unit × Option Bool) (none : Option Bool)

def divideCanon := BitMachineRawSequence.program
  RawRatDivisionEmbedded.program
  (RawRatCanonEmbedded.program RawRatDenominatorCanonical.location)
  BG34Canon.Label.rev
  BitMachineBinaryDivision.initial (none : Option Bool)

def reverseSign := BitMachineRawSequence.program
  (RawRatReverseTransfer.program (2 : Fin 13) 11)
  RawRatSignCleanup.program
  RawRatSignCleanup.Label.check
  (none : Option Bool) (((), none) : RawRatSignCleanup.Control)

def quotients := BitMachineRawSequence.program clearCopy divideCanon
  (BitMachineRawSequence.leftLabel BitMachineBinaryDivision.Label.outer)
  ((((), none), none) : (Unit × Option Bool) × Option Bool)
  ((BitMachineBinaryDivision.initial, none) :
    BitMachineBinaryDivision.Control × Option Bool)

def program := BitMachineRawSequence.program quotients reverseSign
  (BitMachineRawSequence.leftLabel RawRatReverseTransfer.Label.move)
  (((((), none), none), (BitMachineBinaryDivision.initial, none)) :
    ((Unit × Option Bool) × Option Bool) ×
      (BitMachineBinaryDivision.Control × Option Bool))
  ((none, ((), none)) : Option Bool × RawRatSignCleanup.Control)

noncomputable def result (r : RawRat) : RawRatPreparation.Bank :=
  RawRatSignCleanup.result (RawRatDenominatorCanonical.result r)

theorem clearCopy_run (r : RawRat) :
    ∃ t ≤ RawRatClearArithmetic.clock (RawRatNumeratorCanonical.result r) +
      2 * r.denominator.length + 3,
      ((advance clearCopy)^[t])
        (⟨some (BitMachineRawSequence.leftLabel (0 : Fin 8)),
          (((), none), none), RawRatNumeratorCanonical.result r⟩ :
          TM2.Cfg (fun _ : Fin 13 => Bool) _ _) =
        ⟨none, (((), none), none), RawRatDenominatorDivision.dividendReady r⟩ := by
  obtain ⟨tc, htc, hc⟩ := RawRatDenominatorDivision.clear_run r
  obtain ⟨t, ht, h⟩ := BitMachineRawSequence.runs
    RawRatClearArithmetic.program
    (RawRatCopyEmbedded.program RawRatDenominatorDivision.copyLocation)
    (0 : Fin 8) BitMachineCopy.Label.scan
    (((), none) : Unit × Option Bool) (((), none) : Unit × Option Bool)
    (none : Option Bool) none
    (RawRatNumeratorCanonical.result r) (RawRatDenominatorDivision.cleared r)
    (RawRatDenominatorDivision.dividendReady r)
    tc (2 * r.denominator.length + 2) hc
    (RawRatDenominatorDivision.copy_run r)
  exact ⟨t, by omega, h⟩

theorem divideCanon_run (r : RawRat) :
    ∃ t ≤ RawRatDivisionEmbedded.clock
        (RawRatDenominatorDivision.dividendReady r) +
      RawRatCanonEmbedded.clock RawRatDenominatorCanonical.location
        (RawRatDenominatorDivision.divided r) + 1,
      ((advance divideCanon)^[t])
        (⟨some (BitMachineRawSequence.leftLabel
            BitMachineBinaryDivision.Label.outer),
          (BitMachineBinaryDivision.initial, none),
          RawRatDenominatorDivision.dividendReady r⟩ :
          TM2.Cfg (fun _ : Fin 13 => Bool) _ _) =
        ⟨none, (BitMachineBinaryDivision.initial, none),
          RawRatDenominatorCanonical.canonicalLE r⟩ := by
  obtain ⟨t, ht, h⟩ := BitMachineRawSequence.runs
    RawRatDivisionEmbedded.program
    (RawRatCanonEmbedded.program RawRatDenominatorCanonical.location)
    BitMachineBinaryDivision.Label.outer BG34Canon.Label.rev
    BitMachineBinaryDivision.initial BitMachineBinaryDivision.initial
    (none : Option Bool) none
    (RawRatDenominatorDivision.dividendReady r)
    (RawRatDenominatorDivision.divided r)
    (RawRatDenominatorCanonical.canonicalLE r)
    (RawRatDivisionEmbedded.clock (RawRatDenominatorDivision.dividendReady r))
    (RawRatCanonEmbedded.clock RawRatDenominatorCanonical.location
      (RawRatDenominatorDivision.divided r))
    (RawRatDenominatorDivision.divide_run r)
    (RawRatDenominatorCanonical.canonical_run r)
  exact ⟨t, ht, h⟩

theorem reverseSign_run (r : RawRat) :
    ∃ (t : Nat) (v : RawRatSignCleanup.Control),
      t ≤ (RawRatDenominatorCanonical.canonicalLE r 2).length + 1 +
      (RawRatDenominatorCanonical.result r 0).length + 4 ∧
      ((advance reverseSign)^[t])
        (⟨some (BitMachineRawSequence.leftLabel
            RawRatReverseTransfer.Label.move),
          (none, ((), none)), RawRatDenominatorCanonical.canonicalLE r⟩ :
          TM2.Cfg (fun _ : Fin 13 => Bool) _ _) =
        ⟨none, (none, v), result r⟩ := by
  obtain ⟨ts, hts, vs, hs⟩ := RawRatSignCleanup.total_run
    (RawRatDenominatorCanonical.result r)
  obtain ⟨t, ht, h⟩ := BitMachineRawSequence.runs
    (RawRatReverseTransfer.program (2 : Fin 13) 11)
    RawRatSignCleanup.program
    RawRatReverseTransfer.Label.move RawRatSignCleanup.Label.check
    (none : Option Bool) none (((), none) : RawRatSignCleanup.Control) vs
    (RawRatDenominatorCanonical.canonicalLE r)
    (RawRatDenominatorCanonical.result r) (result r)
    ((RawRatDenominatorCanonical.canonicalLE r 2).length + 1) ts
    (RawRatDenominatorCanonical.reverse_run r) hs
  exact ⟨t, vs, by omega, h⟩

theorem quotients_run (r : RawRat) :
    ∃ t ≤ RawRatClearArithmetic.clock (RawRatNumeratorCanonical.result r) +
      2 * r.denominator.length + 3 +
      (RawRatDivisionEmbedded.clock (RawRatDenominatorDivision.dividendReady r) +
       RawRatCanonEmbedded.clock RawRatDenominatorCanonical.location
         (RawRatDenominatorDivision.divided r) + 1) + 1,
      ((advance quotients)^[t])
        (⟨some (BitMachineRawSequence.leftLabel
            (BitMachineRawSequence.leftLabel (0 : Fin 8))),
          ((((), none), none),
            (BitMachineBinaryDivision.initial, none)),
          RawRatNumeratorCanonical.result r⟩ :
          TM2.Cfg (fun _ : Fin 13 => Bool) _ _) =
        ⟨none, ((((), none), none),
          (BitMachineBinaryDivision.initial, none)),
          RawRatDenominatorCanonical.canonicalLE r⟩ := by
  obtain ⟨ta, hta, ha⟩ := clearCopy_run r
  obtain ⟨tb, htb, hb⟩ := divideCanon_run r
  obtain ⟨t, ht, h⟩ := BitMachineRawSequence.runs clearCopy divideCanon
    (BitMachineRawSequence.leftLabel (0 : Fin 8))
    (BitMachineRawSequence.leftLabel BitMachineBinaryDivision.Label.outer)
    ((((), none), none) : (Unit × Option Bool) × Option Bool)
    ((((), none), none) : (Unit × Option Bool) × Option Bool)
    (BitMachineBinaryDivision.initial, none)
    (BitMachineBinaryDivision.initial, none)
    (RawRatNumeratorCanonical.result r)
    (RawRatDenominatorDivision.dividendReady r)
    (RawRatDenominatorCanonical.canonicalLE r) ta tb ha hb
  exact ⟨t, by omega, h⟩

noncomputable def clock (r : RawRat) : Nat :=
  RawRatClearArithmetic.clock (RawRatNumeratorCanonical.result r) +
    2 * r.denominator.length + 3 +
    RawRatDivisionEmbedded.clock (RawRatDenominatorDivision.dividendReady r) +
    RawRatCanonEmbedded.clock RawRatDenominatorCanonical.location
      (RawRatDenominatorDivision.divided r) +
    (RawRatDenominatorCanonical.canonicalLE r 2).length + 1 +
    (RawRatDenominatorCanonical.result r 0).length + 11

theorem run (r : RawRat) :
    ∃ (t : Nat) (v : RawRatSignCleanup.Control), t ≤ clock r ∧
      ((advance program)^[t])
        (⟨some (BitMachineRawSequence.leftLabel
            (BitMachineRawSequence.leftLabel
              (BitMachineRawSequence.leftLabel (0 : Fin 8)))),
          (((((), none), none),
              (BitMachineBinaryDivision.initial, none)),
            (none, ((), none))),
          RawRatNumeratorCanonical.result r⟩ :
          TM2.Cfg (fun _ : Fin 13 => Bool) _ _) =
        ⟨none, (((((), none), none),
              (BitMachineBinaryDivision.initial, none)),
            (none, v)), result r⟩ := by
  obtain ⟨ta, hta, ha⟩ := quotients_run r
  obtain ⟨tb, v, htb, hb⟩ := reverseSign_run r
  obtain ⟨t, ht, h⟩ := BitMachineRawSequence.runs quotients reverseSign
    (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel (0 : Fin 8)))
    (BitMachineRawSequence.leftLabel RawRatReverseTransfer.Label.move)
    (((((), none), none), (BitMachineBinaryDivision.initial, none)))
    (((((), none), none), (BitMachineBinaryDivision.initial, none)))
    ((none, ((), none)) : Option Bool × RawRatSignCleanup.Control)
    ((none, v) : Option Bool × RawRatSignCleanup.Control)
    (RawRatNumeratorCanonical.result r)
    (RawRatDenominatorCanonical.canonicalLE r) (result r)
    ta tb ha hb
  exact ⟨t, v, by unfold clock; omega, h⟩

end CurrentAdditive.RawRatSecondQuotientController
