import CurrentAdditive.RawRatCanonEmbedded
import Mathlib.Tactic

/-! Physical canonicalization of the first quotient into numerator bank 1. -/
namespace CurrentAdditive.RawRatNumeratorCanonical

open EthInapproximability.CurrentPaper
open CurrentAdditive.CodeDCodec

def location : Fin 3 ↪ Fin 13 where
  toFun i := if i = 0 then 9 else if i = 1 then 10 else 1
  inj' := by
    intro a b h
    fin_cases a <;> fin_cases b <;> simp_all

noncomputable def result (r : RawRat) : RawRatPreparation.Bank :=
  RawRatCanonEmbedded.result location (RawRatNumeratorDivision.divided r)

theorem work_empty (r : RawRat) : RawRatNumeratorDivision.divided r 10 = [] := by
  change BitMachineStackEmbedding.bank RawRatGCDStage.location
      (RawRatNumeratorDivision.dividendReady r)
      (BitMachineBinaryDivision.finalBank
        (RawRatNumeratorDivision.dividendReady r 3)
        (RawRatNumeratorDivision.dividendReady r 4))
      (RawRatGCDStage.location 4) = []
  rw [BitMachineStackEmbedding.bank_at]
  rfl

theorem output_empty (r : RawRat) : RawRatNumeratorDivision.divided r 1 = [] := by
  have houtside : ¬ ∃ j : Fin 7, RawRatGCDStage.location j = (1 : Fin 13) := by
    rintro ⟨j,h⟩; fin_cases j <;> simp [RawRatGCDStage.location] at h
  rw [RawRatNumeratorDivision.divided,
    RawRatDivisionEmbedded.result,
    BitMachineStackEmbedding.bank_outside _ _ _ 1 houtside]
  have hclear : RawRatNumeratorDivision.cleared r 1 =
      RawRatGCDStage.result r 1 := by
    rw [RawRatNumeratorDivision.cleared,
      RawRatClearArithmetic.result]
    apply BitMachineClearBank.cleared_foreign
    intro j
    fin_cases j <;> simp [RawRatClearArithmetic.location]
  have hprep : RawRatGCDStage.result r 1 =
      RawRatPreparation.prepared r 1 := by
    rw [RawRatGCDStage.result]
    apply BitMachineStackEmbedding.bank_outside
    rintro ⟨j,h⟩; fin_cases j <;> simp [RawRatGCDStage.location] at h
  simp [RawRatNumeratorDivision.dividendReady, hclear, hprep,
    RawRatPreparation.prepared, RawRatPreparation.afterNumReverse,
    RawRatPreparation.afterDenCopy, RawRatPreparation.afterNumCopy,
    RawRatPreparation.inputBank]

theorem physical_run (r : RawRat) :
    ((BitMachineEncoding.advance (RawRatCanonEmbedded.program location))^[
      RawRatCanonEmbedded.clock location (RawRatNumeratorDivision.divided r)])
      (⟨some BG34Canon.Label.rev, none, RawRatNumeratorDivision.divided r⟩ :
        Turing.TM2.Cfg (fun _ : Fin 13 => Bool) _ _) =
      ⟨none, none, result r⟩ :=
  RawRatCanonEmbedded.run location _ (work_empty r) (output_empty r)

theorem numerator_bytes (r : RawRat) (hr : r.Valid) :
    result r 1 =
      (CurrentAdditive.BinaryGCDNormalization.numeratorValue r /
        CurrentAdditive.BinaryGCDNormalization.commonDivisor r).bits := by
  have h := RawRatCanonEmbedded.result_output location
    (RawRatNumeratorDivision.divided r)
  simpa [result, location, RawRatNumeratorDivision.quotient_value r hr] using h

theorem gcd_preserved (r : RawRat) : result r 4 = RawRatGCDStage.result r 4 := by
  have houtside : ¬ ∃ j : Fin 3, location j = (4 : Fin 13) := by
    rintro ⟨j,h⟩; fin_cases j <;> simp [location] at h
  rw [result, RawRatCanonEmbedded.result_foreign _ _ _ houtside,
    RawRatNumeratorDivision.divided, RawRatDivisionEmbedded.result]
  change BitMachineStackEmbedding.bank RawRatGCDStage.location
      (RawRatNumeratorDivision.dividendReady r)
      (BitMachineBinaryDivision.finalBank
        (RawRatNumeratorDivision.dividendReady r 3)
        (RawRatNumeratorDivision.dividendReady r 4))
      (RawRatGCDStage.location 1) = _
  rw [BitMachineStackEmbedding.bank_at]
  simp [BitMachineBinaryDivision.finalBank, BitMachineBinaryDivision.bank,
    RawRatNumeratorDivision.ready_divisor]

theorem denominator_saved (r : RawRat) : result r 6 = r.denominator := by
  have houtside : ¬ ∃ j : Fin 3, location j = (6 : Fin 13) := by
    rintro ⟨j,h⟩; fin_cases j <;> simp [location] at h
  rw [result, RawRatCanonEmbedded.result_foreign _ _ _ houtside,
    RawRatNumeratorDivision.divided, RawRatDivisionEmbedded.result]
  have hforeign : ¬ ∃ j : Fin 7, RawRatGCDStage.location j = (6 : Fin 13) := by
    rintro ⟨j,h⟩; fin_cases j <;> simp [RawRatGCDStage.location] at h
  rw [BitMachineStackEmbedding.bank_outside _ _ _ 6 hforeign]
  simp [RawRatNumeratorDivision.dividendReady, RawRatNumeratorDivision.cleared,
    RawRatClearArithmetic.denominator_preserved,
    RawRatGCDStage.saved_denominator]

end CurrentAdditive.RawRatNumeratorCanonical
