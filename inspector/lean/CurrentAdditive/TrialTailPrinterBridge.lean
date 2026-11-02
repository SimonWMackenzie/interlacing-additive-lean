import CurrentAdditive.TrialSearchCombinedCallback
import CurrentAdditive.CounterBitEncoding
import CurrentAdditive.HornerNatBridge

/-!
The selected low-first candidate counter is already the exact lower-modulus
word expected by the seed printer. No physical reversal or copy is needed if
the shared machine hands stack 0 to that consumer.
-/

namespace CurrentAdditive.FieldMachineHelper.TrialTailPrinterBridge

open EthInapproximability.CurrentPaper
open ExecutableSmallBiasSampler
open CurrentAdditive.FieldMachineHelper.TrialCounterMachine (counterWord counterWord_length)
open CurrentAdditive.FieldMachineHelper.CounterBitEncoding (counterWord_eq_natBits)
open CurrentAdditive.FiniteFieldConstructor.TrialSearch (monicBits)
open CurrentAdditive.FiniteFieldMachine.HornerNatBridge (lowerWord)

theorem counterWord_eq_printer_modulus (d tail : Nat)
    (htail : tail < 2 ^ d) :
    counterWord d tail =
      SamplerMachine.encodeWord (lowerWord d (monicBits d tail)) := by
  rw [counterWord_eq_natBits d tail htail]
  apply List.ext_getElem
  · simp [SamplerMachine.encodeWord]
  · intro i hi hj
    simp only [List.getElem_map, List.getElem_range,
      SamplerMachine.encodeWord, List.getElem_ofFn,
      lowerWord, SamplerMachine.encodeBit,
      CurrentAdditive.FiniteFieldConstructor.BitPolynomialBridge.boolCoeff]
    have hi' : i < d := by simpa using hi
    have hbit : (monicBits d tail).testBit i = tail.testBit i := by
      simpa [monicBits] using Nat.testBit_two_pow_add_gt hi' tail
    cases h : tail.testBit i <;> simp [hbit, h]

#print axioms counterWord_eq_printer_modulus

end CurrentAdditive.FieldMachineHelper.TrialTailPrinterBridge
