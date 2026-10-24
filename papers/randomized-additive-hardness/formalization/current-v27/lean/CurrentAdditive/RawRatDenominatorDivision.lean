import CurrentAdditive.RawRatNumeratorCanonical
import Mathlib.Tactic

/-! Physical second quotient: original denominator divided by the same GCD. -/
namespace CurrentAdditive.RawRatDenominatorDivision

open Turing
open EthInapproximability.CurrentPaper
open BitMachineEncoding
open CurrentAdditive.CodeDCodec

def copyLocation : Fin 3 ↪ Fin 13 where
  toFun i := if i = 0 then 6 else if i = 1 then 3 else 10
  inj' := by
    intro a b h
    fin_cases a <;> fin_cases b <;> simp_all

noncomputable def cleared (r : RawRat) : RawRatPreparation.Bank :=
  RawRatClearArithmetic.result (RawRatNumeratorCanonical.result r)

noncomputable def dividendReady (r : RawRat) : RawRatPreparation.Bank :=
  Function.update (cleared r) 3 r.denominator

noncomputable def divided (r : RawRat) : RawRatPreparation.Bank :=
  RawRatDivisionEmbedded.result (dividendReady r)

theorem clear_run (r : RawRat) :
    ∃ t ≤ RawRatClearArithmetic.clock (RawRatNumeratorCanonical.result r),
      ((advance RawRatClearArithmetic.program)^[t])
        (⟨some (0 : Fin 8), ((), none), RawRatNumeratorCanonical.result r⟩ :
          TM2.Cfg (fun _ : Fin 13 => Bool) _ _) =
        ⟨none, ((), none), cleared r⟩ :=
  RawRatClearArithmetic.run _

theorem copy_run (r : RawRat) :
    ((advance (RawRatCopyEmbedded.program copyLocation))^[
      2 * r.denominator.length + 2])
      (⟨some BitMachineCopy.Label.scan, none, cleared r⟩ :
        TM2.Cfg (fun _ : Fin 13 => Bool) _ _) =
      ⟨none, none, dividendReady r⟩ := by
  have hsource : cleared r 6 = r.denominator := by
    rw [cleared, RawRatClearArithmetic.denominator_preserved,
      RawRatNumeratorCanonical.denominator_saved]
  have htarget : cleared r 3 = [] := by
    simpa [cleared, RawRatClearArithmetic.location] using
      RawRatClearArithmetic.cleared (RawRatNumeratorCanonical.result r) (0 : Fin 6)
  have htemp : cleared r 10 = [] := by
    simpa [cleared, RawRatClearArithmetic.location] using
      RawRatClearArithmetic.cleared (RawRatNumeratorCanonical.result r) (3 : Fin 6)
  have h := RawRatCopyEmbedded.run_correct copyLocation (cleared r)
    (by simpa [copyLocation] using htarget)
    (by simpa [copyLocation] using htemp)
  simpa [copyLocation, dividendReady, hsource] using h

theorem ready_input (r : RawRat) : dividendReady r 3 = r.denominator := by
  simp [dividendReady]

theorem ready_divisor (r : RawRat) :
    dividendReady r 4 = RawRatGCDStage.result r 4 := by
  simp [dividendReady, cleared, RawRatClearArithmetic.gcd_preserved,
    RawRatNumeratorCanonical.gcd_preserved]

theorem ready_scratch (r : RawRat) :
    dividendReady r 8 = [] ∧ dividendReady r 9 = [] ∧
      dividendReady r 10 = [] ∧ dividendReady r 11 = [] ∧
        dividendReady r 12 = [] := by
  constructor
  · simpa [dividendReady, cleared, RawRatClearArithmetic.location] using
      RawRatClearArithmetic.cleared (RawRatNumeratorCanonical.result r) (1 : Fin 6)
  constructor
  · simpa [dividendReady, cleared, RawRatClearArithmetic.location] using
      RawRatClearArithmetic.cleared (RawRatNumeratorCanonical.result r) (2 : Fin 6)
  constructor
  · simpa [dividendReady, cleared, RawRatClearArithmetic.location] using
      RawRatClearArithmetic.cleared (RawRatNumeratorCanonical.result r) (3 : Fin 6)
  constructor
  · simpa [dividendReady, cleared, RawRatClearArithmetic.location] using
      RawRatClearArithmetic.cleared (RawRatNumeratorCanonical.result r) (4 : Fin 6)
  · simpa [dividendReady, cleared, RawRatClearArithmetic.location] using
      RawRatClearArithmetic.cleared (RawRatNumeratorCanonical.result r) (5 : Fin 6)

theorem divide_run (r : RawRat) :
    ((advance RawRatDivisionEmbedded.program)^[RawRatDivisionEmbedded.clock
        (dividendReady r)])
      (⟨some BitMachineBinaryDivision.Label.outer,
        BitMachineBinaryDivision.initial, dividendReady r⟩ :
        TM2.Cfg (fun _ : Fin 13 => Bool) _ _) =
      ⟨none, BitMachineBinaryDivision.initial, divided r⟩ := by
  obtain ⟨h8,h9,h10,h11,h12⟩ := ready_scratch r
  exact RawRatDivisionEmbedded.run (dividendReady r) h8 h9 h10 h11 h12

theorem quotient_value (r : RawRat) (hr : r.Valid) :
    EncodedCommunication.bitsValue (divided r 9) =
      CurrentAdditive.BinaryGCDNormalization.denominatorValue r /
        CurrentAdditive.BinaryGCDNormalization.commonDivisor r := by
  have hg := RawRatGCDStage.result_divisor_value r hr
  have hp := CurrentAdditive.BinaryGCDNormalization.commonDivisor_pos r hr
  have hd : 0 < EncodedCommunication.bitsValue (dividendReady r 4) := by
    rw [ready_divisor, hg]
    exact hp
  have hv := RawRatDivisionEmbedded.quotient_value (dividendReady r) hd
  change EncodedCommunication.bitsValue (divided r 9) = _
  rw [ready_input, ready_divisor, hg] at hv
  simpa [CurrentAdditive.BinaryGCDNormalization.denominatorValue] using hv

end CurrentAdditive.RawRatDenominatorDivision
