import CurrentAdditive.RawRatDenominatorDivision
import Mathlib.Tactic

/-! Physical canonical denominator, reversed into its Code D MSB field. -/
namespace CurrentAdditive.RawRatDenominatorCanonical

open Turing
open EthInapproximability.CurrentPaper
open BitMachineEncoding
open CurrentAdditive.CodeDCodec

def location : Fin 3 ↪ Fin 13 where
  toFun i := if i = 0 then 9 else if i = 1 then 10 else 2
  inj' := by
    intro a b h
    fin_cases a <;> fin_cases b <;> simp_all

noncomputable def canonicalLE (r : RawRat) : RawRatPreparation.Bank :=
  RawRatCanonEmbedded.result location (RawRatDenominatorDivision.divided r)

noncomputable def result (r : RawRat) : RawRatPreparation.Bank :=
  Function.update (Function.update (canonicalLE r) 2 []) 11
    (canonicalLE r 2).reverse

theorem work_empty (r : RawRat) : RawRatDenominatorDivision.divided r 10 = [] := by
  change BitMachineStackEmbedding.bank RawRatGCDStage.location
      (RawRatDenominatorDivision.dividendReady r)
      (BitMachineBinaryDivision.finalBank
        (RawRatDenominatorDivision.dividendReady r 3)
        (RawRatDenominatorDivision.dividendReady r 4))
      (RawRatGCDStage.location 4) = []
  rw [BitMachineStackEmbedding.bank_at]
  rfl

private theorem bank2_after_gcd (r : RawRat) : RawRatGCDStage.result r 2 = [] := by
  have houtside : ¬ ∃ j : Fin 7, RawRatGCDStage.location j = (2 : Fin 13) := by
    rintro ⟨j,h⟩; fin_cases j <;> simp [RawRatGCDStage.location] at h
  rw [RawRatGCDStage.result,
    BitMachineStackEmbedding.bank_outside _ _ _ 2 houtside]
  simp [RawRatPreparation.prepared, RawRatPreparation.afterNumReverse,
    RawRatPreparation.afterDenCopy, RawRatPreparation.afterNumCopy,
    RawRatPreparation.inputBank]

private theorem bank2_after_num (r : RawRat) :
    RawRatNumeratorCanonical.result r 2 = [] := by
  have hcanon : ¬ ∃ j : Fin 3,
      RawRatNumeratorCanonical.location j = (2 : Fin 13) := by
    rintro ⟨j,h⟩; fin_cases j <;>
      simp [RawRatNumeratorCanonical.location] at h
  rw [RawRatNumeratorCanonical.result,
    RawRatCanonEmbedded.result_foreign _ _ _ hcanon,
    RawRatNumeratorDivision.divided, RawRatDivisionEmbedded.result]
  have hdiv : ¬ ∃ j : Fin 7, RawRatGCDStage.location j = (2 : Fin 13) := by
    rintro ⟨j,h⟩; fin_cases j <;> simp [RawRatGCDStage.location] at h
  rw [BitMachineStackEmbedding.bank_outside _ _ _ 2 hdiv]
  have hclear : RawRatNumeratorDivision.cleared r 2 =
      RawRatGCDStage.result r 2 := by
    rw [RawRatNumeratorDivision.cleared,
      RawRatClearArithmetic.result]
    apply BitMachineClearBank.cleared_foreign
    intro j
    fin_cases j <;> simp [RawRatClearArithmetic.location]
  simpa [RawRatNumeratorDivision.dividendReady,
    hclear, bank2_after_gcd]

theorem output_empty (r : RawRat) : RawRatDenominatorDivision.divided r 2 = [] := by
  have hdiv : ¬ ∃ j : Fin 7, RawRatGCDStage.location j = (2 : Fin 13) := by
    rintro ⟨j,h⟩; fin_cases j <;> simp [RawRatGCDStage.location] at h
  rw [RawRatDenominatorDivision.divided, RawRatDivisionEmbedded.result,
    BitMachineStackEmbedding.bank_outside _ _ _ 2 hdiv]
  have hclear : RawRatDenominatorDivision.cleared r 2 =
      RawRatNumeratorCanonical.result r 2 := by
    rw [RawRatDenominatorDivision.cleared,
      RawRatClearArithmetic.result]
    apply BitMachineClearBank.cleared_foreign
    intro j
    fin_cases j <;> simp [RawRatClearArithmetic.location]
  simpa [RawRatDenominatorDivision.dividendReady,
    hclear, bank2_after_num]

theorem canonical_run (r : RawRat) :
    ((advance (RawRatCanonEmbedded.program location))^[
      RawRatCanonEmbedded.clock location (RawRatDenominatorDivision.divided r)])
      (⟨some BG34Canon.Label.rev, none, RawRatDenominatorDivision.divided r⟩ :
        TM2.Cfg (fun _ : Fin 13 => Bool) _ _) =
      ⟨none, none, canonicalLE r⟩ :=
  RawRatCanonEmbedded.run location _ (work_empty r) (output_empty r)

theorem denominator_LE (r : RawRat) (hr : r.Valid) :
    canonicalLE r 2 =
      (CurrentAdditive.BinaryGCDNormalization.denominatorValue r /
        CurrentAdditive.BinaryGCDNormalization.commonDivisor r).bits := by
  have h := RawRatCanonEmbedded.result_output location
    (RawRatDenominatorDivision.divided r)
  simpa [canonicalLE, location, RawRatDenominatorDivision.quotient_value r hr] using h

theorem output_empty_11 (r : RawRat) : canonicalLE r 11 = [] := by
  have hcanon : ¬ ∃ j : Fin 3, location j = (11 : Fin 13) := by
    rintro ⟨j,h⟩; fin_cases j <;> simp [location] at h
  rw [canonicalLE, RawRatCanonEmbedded.result_foreign _ _ _ hcanon,
    RawRatDenominatorDivision.divided, RawRatDivisionEmbedded.result]
  change BitMachineStackEmbedding.bank RawRatGCDStage.location
      (RawRatDenominatorDivision.dividendReady r)
      (BitMachineBinaryDivision.finalBank
        (RawRatDenominatorDivision.dividendReady r 3)
        (RawRatDenominatorDivision.dividendReady r 4))
      (RawRatGCDStage.location 5) = []
  rw [BitMachineStackEmbedding.bank_at]
  rfl

theorem reverse_run (r : RawRat) :
    RawRatReverseTransfer.run (2 : Fin 13) 11
      ((canonicalLE r 2).length + 1)
      (RawRatReverseTransfer.cfg (some .move) none (canonicalLE r)) =
      RawRatReverseTransfer.cfg none none (result r) := by
  have h := RawRatReverseTransfer.run_correct (2 : Fin 13) 11
    (by decide) (canonicalLE r) none
  simpa [result, output_empty_11] using h

theorem denominator_bytes (r : RawRat) (hr : r.Valid) :
    result r 11 =
      (CurrentAdditive.BinaryGCDNormalization.denominatorValue r /
        CurrentAdditive.BinaryGCDNormalization.commonDivisor r).bits.reverse := by
  simp [result, denominator_LE r hr]

end CurrentAdditive.RawRatDenominatorCanonical
