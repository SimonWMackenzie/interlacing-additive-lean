import CurrentAdditive.RawRatClearArithmetic
import CurrentAdditive.RawRatQuotientCanonical
import Mathlib.Tactic

/-! Physical first quotient: original numerator divided by the retained GCD. -/
namespace CurrentAdditive.RawRatNumeratorDivision

open Turing
open EthInapproximability.CurrentPaper
open BitMachineEncoding
open CurrentAdditive.CodeDCodec

noncomputable def cleared (r : RawRat) : RawRatPreparation.Bank :=
  RawRatClearArithmetic.result (RawRatGCDStage.result r)

noncomputable def dividendReady (r : RawRat) : RawRatPreparation.Bank :=
  Function.update (Function.update (cleared r) 5 []) 3 r.numerator.reverse

noncomputable def divided (r : RawRat) : RawRatPreparation.Bank :=
  RawRatDivisionEmbedded.result (dividendReady r)

theorem clear_run (r : RawRat) :
    ∃ t ≤ RawRatClearArithmetic.clock (RawRatGCDStage.result r),
      ((advance RawRatClearArithmetic.program)^[t])
        (⟨some (0 : Fin 8), ((), none), RawRatGCDStage.result r⟩ :
          TM2.Cfg (fun _ : Fin 13 => Bool) _ _) =
        ⟨none, ((), none), cleared r⟩ :=
  RawRatClearArithmetic.run _

theorem move_run (r : RawRat) :
    RawRatReverseTransfer.run (5 : Fin 13) 3 (r.numerator.length + 1)
      (RawRatReverseTransfer.cfg (some .move) none (cleared r)) =
      RawRatReverseTransfer.cfg none none (dividendReady r) := by
  have h := RawRatReverseTransfer.run_correct (5 : Fin 13) 3 (by decide)
    (cleared r) none
  have hnum : cleared r 5 = r.numerator := by
    rw [cleared, RawRatClearArithmetic.numerator_preserved,
      RawRatGCDStage.saved_numerator]
  have htarget : cleared r 3 = [] := by
    simpa [cleared, RawRatClearArithmetic.location] using
      RawRatClearArithmetic.cleared (RawRatGCDStage.result r) (0 : Fin 6)
  simpa [dividendReady, hnum, htarget] using h

theorem ready_input (r : RawRat) : dividendReady r 3 = r.numerator.reverse := by
  simp [dividendReady]

theorem ready_divisor (r : RawRat) : dividendReady r 4 = RawRatGCDStage.result r 4 := by
  simp [dividendReady, cleared, RawRatClearArithmetic.gcd_preserved]

theorem ready_scratch (r : RawRat) :
    dividendReady r 8 = [] ∧ dividendReady r 9 = [] ∧
      dividendReady r 10 = [] ∧ dividendReady r 11 = [] ∧
        dividendReady r 12 = [] := by
  constructor
  · simpa [dividendReady, cleared, RawRatClearArithmetic.location] using
      RawRatClearArithmetic.cleared (RawRatGCDStage.result r) (1 : Fin 6)
  constructor
  · simpa [dividendReady, cleared, RawRatClearArithmetic.location] using
      RawRatClearArithmetic.cleared (RawRatGCDStage.result r) (2 : Fin 6)
  constructor
  · simpa [dividendReady, cleared, RawRatClearArithmetic.location] using
      RawRatClearArithmetic.cleared (RawRatGCDStage.result r) (3 : Fin 6)
  constructor
  · simpa [dividendReady, cleared, RawRatClearArithmetic.location] using
      RawRatClearArithmetic.cleared (RawRatGCDStage.result r) (4 : Fin 6)
  · simpa [dividendReady, cleared, RawRatClearArithmetic.location] using
      RawRatClearArithmetic.cleared (RawRatGCDStage.result r) (5 : Fin 6)

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
      CurrentAdditive.BinaryGCDNormalization.numeratorValue r /
        CurrentAdditive.BinaryGCDNormalization.commonDivisor r := by
  have hg := RawRatGCDStage.result_divisor_value r hr
  have hp : 0 < CurrentAdditive.BinaryGCDNormalization.commonDivisor r :=
    CurrentAdditive.BinaryGCDNormalization.commonDivisor_pos r hr
  have hd : 0 < EncodedCommunication.bitsValue (dividendReady r 4) := by
    rw [ready_divisor, hg]
    exact hp
  have hv := RawRatDivisionEmbedded.quotient_value (dividendReady r) hd
  change EncodedCommunication.bitsValue (divided r 9) = _
  rw [ready_input, ready_divisor, hg] at hv
  change EncodedCommunication.bitsValue (divided r 9) =
    BitMachineBinaryMultiply.msbValue r.numerator.reverse /
      CurrentAdditive.BinaryGCDNormalization.commonDivisor r at hv
  rw [CurrentAdditive.CodeDCanonicalSource.msbValue_reverse] at hv
  exact hv

end CurrentAdditive.RawRatNumeratorDivision
