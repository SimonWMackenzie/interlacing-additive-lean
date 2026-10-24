import CurrentAdditive.RawRatCoreController
import CurrentAdditive.RationalCanonical
import Mathlib.Tactic

/-! Exact output-byte contract for the checked physical core. -/
namespace CurrentAdditive.RawRatCoreBytes

open EthInapproximability.CurrentPaper
open CurrentAdditive.CodeDCodec

private theorem outsideGCD (k : Fin 13) (hk : k = 0 ∨ k = 1) :
    ¬ ∃ i : Fin 7, RawRatGCDStage.location i = k := by
  rcases hk with rfl | rfl <;>
    rintro ⟨i, h⟩ <;> fin_cases i <;> simp [RawRatGCDStage.location] at h

private theorem outsideClear (k : Fin 13) (hk : k = 0 ∨ k = 1) :
    ∀ i : Fin 6, RawRatClearArithmetic.location i ≠ k := by
  rcases hk with rfl | rfl <;>
    intro i <;> fin_cases i <;> simp [RawRatClearArithmetic.location]

private theorem outsideCanonN (k : Fin 13) (hk : k = 0 ∨ k = 6) :
    ¬ ∃ i : Fin 3, RawRatNumeratorCanonical.location i = k := by
  rcases hk with rfl | rfl <;>
    rintro ⟨i, h⟩ <;> fin_cases i <;> simp [RawRatNumeratorCanonical.location] at h

private theorem outsideCanonD (k : Fin 13) (hk : k = 0 ∨ k = 1) :
    ¬ ∃ i : Fin 3, RawRatDenominatorCanonical.location i = k := by
  rcases hk with rfl | rfl <;>
    rintro ⟨i, h⟩ <;> fin_cases i <;> simp [RawRatDenominatorCanonical.location] at h

private theorem gcd_sign (r : RawRat) :
    RawRatGCDStage.result r 0 = if r.negative then [true] else [] := by
  rw [RawRatGCDStage.result,
    BitMachineStackEmbedding.bank_outside _ _ _ 0 (outsideGCD 0 (Or.inl rfl))]
  simp [RawRatPreparation.prepared, RawRatPreparation.afterNumReverse,
    RawRatPreparation.afterDenCopy, RawRatPreparation.afterNumCopy,
    RawRatPreparation.inputBank]

private theorem numerator_sign (r : RawRat) :
    RawRatNumeratorCanonical.result r 0 =
      if r.negative then [true] else [] := by
  rw [RawRatNumeratorCanonical.result,
    RawRatCanonEmbedded.result_foreign _ _ _ (outsideCanonN 0 (Or.inl rfl)),
    RawRatNumeratorDivision.divided, RawRatDivisionEmbedded.result,
    BitMachineStackEmbedding.bank_outside _ _ _ 0 (outsideGCD 0 (Or.inl rfl))]
  simp [RawRatNumeratorDivision.dividendReady,
    RawRatNumeratorDivision.cleared,
    RawRatClearArithmetic.result,
    BitMachineClearBank.cleared_foreign _ _ _ (outsideClear 0 (Or.inl rfl)),
    gcd_sign]

theorem denominator_sign (r : RawRat) :
    RawRatDenominatorCanonical.result r 0 =
      if r.negative then [true] else [] := by
  rw [RawRatDenominatorCanonical.result]
  simp only [Function.update_of_ne (by decide : (0 : Fin 13) ≠ 11),
    Function.update_of_ne (by decide : (0 : Fin 13) ≠ 2)]
  rw [RawRatDenominatorCanonical.canonicalLE,
    RawRatCanonEmbedded.result_foreign _ _ _ (outsideCanonD 0 (Or.inl rfl)),
    RawRatDenominatorDivision.divided, RawRatDivisionEmbedded.result,
    BitMachineStackEmbedding.bank_outside _ _ _ 0 (outsideGCD 0 (Or.inl rfl))]
  simp [RawRatDenominatorDivision.dividendReady,
    RawRatDenominatorDivision.cleared,
    RawRatClearArithmetic.result,
    BitMachineClearBank.cleared_foreign _ _ _ (outsideClear 0 (Or.inl rfl)),
    numerator_sign]

private theorem denominator_numerator (r : RawRat) :
    RawRatDenominatorCanonical.result r 1 =
      RawRatNumeratorCanonical.result r 1 := by
  rw [RawRatDenominatorCanonical.result]
  simp only [Function.update_of_ne (by decide : (1 : Fin 13) ≠ 11),
    Function.update_of_ne (by decide : (1 : Fin 13) ≠ 2)]
  rw [RawRatDenominatorCanonical.canonicalLE,
    RawRatCanonEmbedded.result_foreign _ _ _ (outsideCanonD 1 (Or.inr rfl)),
    RawRatDenominatorDivision.divided, RawRatDivisionEmbedded.result,
    BitMachineStackEmbedding.bank_outside _ _ _ 1 (outsideGCD 1 (Or.inr rfl))]
  simp [RawRatDenominatorDivision.dividendReady,
    RawRatDenominatorDivision.cleared,
    RawRatClearArithmetic.result,
    BitMachineClearBank.cleared_foreign _ _ _ (outsideClear 1 (Or.inr rfl))]

theorem numerator_bytes (r : RawRat) (hr : r.Valid) :
    RawRatCoreController.result r 1 =
      (CurrentAdditive.BinaryGCDNormalization.normalize r).numerator := by
  rw [RawRatCoreController.result,
    RawRatSecondQuotientController.result,
    RawRatSignCleanup.numerator_preserved,
    denominator_numerator,
    RawRatNumeratorCanonical.numerator_bytes r hr]
  rfl

theorem denominator_bytes (r : RawRat) (hr : r.Valid) :
    RawRatCoreController.result r 11 =
      (CurrentAdditive.BinaryGCDNormalization.normalize r).denominator := by
  rw [RawRatCoreController.result,
    RawRatSecondQuotientController.result,
    RawRatSignCleanup.denominator_preserved,
    RawRatDenominatorCanonical.denominator_bytes r hr]
  rfl

theorem sign_bytes (r : RawRat) (hr : r.Valid) :
    RawRatCoreController.result r 0 =
      if (CurrentAdditive.BinaryGCDNormalization.normalize r).negative
      then [true] else [] := by
  rw [RawRatCoreController.result, RawRatSecondQuotientController.result,
    RawRatSignCleanup.sign_correct]
  rw [denominator_numerator, RawRatNumeratorCanonical.numerator_bytes r hr,
    denominator_sign]
  have hzero :
      (CurrentAdditive.BinaryGCDNormalization.numeratorValue r /
        CurrentAdditive.BinaryGCDNormalization.commonDivisor r).bits = [] ↔
        CurrentAdditive.BinaryGCDNormalization.numeratorValue r = 0 := by
    constructor
    · intro h
      by_contra hn
      have hp : 0 < CurrentAdditive.BinaryGCDNormalization.numeratorValue r :=
        Nat.pos_of_ne_zero hn
      have hq : 0 < CurrentAdditive.BinaryGCDNormalization.numeratorValue r /
          CurrentAdditive.BinaryGCDNormalization.commonDivisor r :=
        Nat.div_pos (Nat.gcd_le_left _ hp)
          (CurrentAdditive.BinaryGCDNormalization.commonDivisor_pos r hr)
      have hv := EncodedCommunication.bitsValue_bits
        (CurrentAdditive.BinaryGCDNormalization.numeratorValue r /
          CurrentAdditive.BinaryGCDNormalization.commonDivisor r)
      rw [h] at hv
      simp [EncodedCommunication.bitsValue] at hv
      omega
    · intro h
      simp [h]
  cases hsign : r.negative <;>
    simp [CurrentAdditive.BinaryGCDNormalization.normalize, hsign, hzero]

theorem selected_exact (r : RawRat) (hr : r.Valid) :
    (fun i : Fin 3 => if i = 0 then RawRatCoreController.result r 0 else
      if i = 1 then RawRatCoreController.result r 1 else
        RawRatCoreController.result r 11) =
      rawRatBank (CurrentAdditive.CodeDCanonicalSource.rawOfRat r.value) := by
  rw [← CurrentAdditive.BinaryGCDNormalization.normalize_is_rawOfRat r hr]
  funext i
  fin_cases i
  · simpa [rawRatBank] using sign_bytes r hr
  · simpa [rawRatBank] using numerator_bytes r hr
  · simpa [rawRatBank] using denominator_bytes r hr

end CurrentAdditive.RawRatCoreBytes
