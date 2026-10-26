import CurrentAdditive.RawRatPreparation
import CurrentAdditive.BinaryGCDPolytime
import EthInapproximability.CurrentPaper.BitMachineStackRun
import Mathlib.Tactic

/-! The seven-stack Euclidean controller embedded in the rational work bank. -/
namespace CurrentAdditive.RawRatGCDStage

open Turing
open EthInapproximability.CurrentPaper
open BitMachineEncoding
open CurrentAdditive.CodeDCodec

def location : Fin 7 ↪ Fin 13 where
  toFun i := if i = 0 then 3 else if i = 1 then 4 else ⟨i.val + 6, by omega⟩
  inj' := by
    intro a b h
    fin_cases a <;> fin_cases b <;> simp_all [Fin.ext_iff]

def localBank (r : RawRat) : Fin 7 → List Bool :=
  fun i => RawRatPreparation.prepared r (location i)

def localClock (r : RawRat) : Nat :=
  BinaryGCDAllInput.clock (BitMachineBankCodec.encode (localBank r)).length

noncomputable def result (r : RawRat) : RawRatPreparation.Bank :=
  BitMachineStackEmbedding.bank location (RawRatPreparation.prepared r)
    (BinaryGCDPolytime.resultBank (localBank r))

def program := fun l => BitMachineStackEmbedding.stackStmt location
  (BinaryGCDAllInput.program l)

theorem run (r : RawRat) :
    ∃ v,
      ((advance program)^[localClock r])
        (⟨some (BitMachineRawSequence.leftLabel (0 : Fin 7)),
          (((), none), BinaryGCDCore.initial), RawRatPreparation.prepared r⟩ :
          TM2.Cfg (fun _ : Fin 13 => Bool) _ _) =
        ⟨none, v, result r⟩ := by
  let S := localBank r
  let c := ((advance BinaryGCDAllInput.program)^[localClock r])
    (BinaryGCDPolytime.initialBank S)
  have hs := BitMachineStackRun.run location (RawRatPreparation.prepared r)
    BinaryGCDAllInput.program (BinaryGCDPolytime.initialBank S) (localClock r)
  have hbank : BitMachineStackEmbedding.bank location
      (RawRatPreparation.prepared r) S = RawRatPreparation.prepared r := by
    exact BitMachineStackEmbedding.bank_restrict location _
  have hc : c.l = none := (BinaryGCDPolytime.result_correct S).1
  have hresult : c.stk = BinaryGCDPolytime.resultBank S := rfl
  refine ⟨c.var, ?_⟩
  change ((advance program)^[localClock r])
      ⟨some (BitMachineRawSequence.leftLabel (0 : Fin 7)),
        (((), none), BinaryGCDCore.initial),
        BitMachineStackEmbedding.bank location (RawRatPreparation.prepared r) S⟩ =
      ⟨c.l, c.var,
        BitMachineStackEmbedding.bank location (RawRatPreparation.prepared r) c.stk⟩ at hs
  rw [hbank] at hs
  simpa only [hc, hresult, S, result] using hs

theorem result_divisor_value (r : RawRat) (hr : r.Valid) :
    EncodedCommunication.bitsValue (result r 4) =
      CurrentAdditive.BinaryGCDNormalization.commonDivisor r := by
  have hlocal := (BinaryGCDPolytime.result_correct (localBank r)).2
  have hd : 0 < EncodedCommunication.bitsValue (localBank r 1) := by
    have hrev : EncodedCommunication.bitsValue r.denominator.reverse =
        BitMachineBinaryMultiply.msbValue r.denominator := by
      simpa only [List.reverse_reverse] using
        (CurrentAdditive.CodeDCanonicalSource.msbValue_reverse
          r.denominator.reverse).symm
    simpa [localBank, location, RawRatPreparation.prepared,
      RawRatPreparation.afterNumReverse, RawRatPreparation.afterDenCopy,
      RawRatPreparation.afterNumCopy, RawRatPreparation.inputBank,
      CurrentAdditive.CodeDCodec.RawRat.Valid,
      CurrentAdditive.BinaryGCDNormalization.denominatorValue,
      hrev] using hr
  have hv := hlocal hd
  change EncodedCommunication.bitsValue
      (BitMachineStackEmbedding.bank location (RawRatPreparation.prepared r)
        (BinaryGCDPolytime.resultBank (localBank r)) (location 1)) = _
  rw [BitMachineStackEmbedding.bank_at]
  have hnum : BitMachineBinaryDivision.msbValue r.numerator.reverse =
      EncodedCommunication.bitsValue r.numerator :=
    CurrentAdditive.CodeDCanonicalSource.msbValue_reverse r.numerator
  have hden : EncodedCommunication.bitsValue r.denominator.reverse =
      BitMachineBinaryMultiply.msbValue r.denominator := by
    simpa only [List.reverse_reverse] using
      (CurrentAdditive.CodeDCanonicalSource.msbValue_reverse
        r.denominator.reverse).symm
  simpa [localBank, location, RawRatPreparation.prepared,
    RawRatPreparation.afterNumReverse, RawRatPreparation.afterDenCopy,
    RawRatPreparation.afterNumCopy, RawRatPreparation.inputBank,
    CurrentAdditive.BinaryGCDNormalization.commonDivisor,
    CurrentAdditive.BinaryGCDNormalization.numeratorValue,
    CurrentAdditive.BinaryGCDNormalization.denominatorValue,
    hnum, hden] using hv

theorem saved_numerator (r : RawRat) : result r 5 = r.numerator := by
  have houtside : ¬ ∃ i : Fin 7, location i = (5 : Fin 13) := by
    rintro ⟨i, hi⟩
    fin_cases i <;> simp [location] at hi
  rw [result, BitMachineStackEmbedding.bank_outside location _ _ 5 houtside]
  simp [RawRatPreparation.prepared, RawRatPreparation.afterNumReverse,
    RawRatPreparation.afterDenCopy, RawRatPreparation.afterNumCopy]

theorem saved_denominator (r : RawRat) : result r 6 = r.denominator := by
  have houtside : ¬ ∃ i : Fin 7, location i = (6 : Fin 13) := by
    rintro ⟨i, hi⟩
    fin_cases i <;> simp [location] at hi
  rw [result, BitMachineStackEmbedding.bank_outside location _ _ 6 houtside]
  simp [RawRatPreparation.prepared, RawRatPreparation.afterNumReverse,
    RawRatPreparation.afterDenCopy, RawRatPreparation.afterNumCopy]

end CurrentAdditive.RawRatGCDStage
