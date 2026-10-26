import CurrentAdditive.TrialDividerTotal
import CurrentAdditive.ZeroWordTest

/-!
The physical zero scan after a completed trial division yields the exact
Boolean used by the frozen `TrialSearch.trialIrreducible` predicate for one
candidate/divisor pair. The whole nested search controller is not asserted.
-/

namespace CurrentAdditive.FieldMachineHelper.TrialDivisorTest

open CurrentAdditive.FieldMachineHelper.DivisionBitStep (bitsBE bitsBE_length)
open CurrentAdditive.FieldMachineHelper.ZeroWordTest
open CurrentAdditive.FiniteFieldConstructor.TrialSearch (monicBits remainder)
open CurrentAdditive.FiniteFieldConstructor.BitPolynomialBridge (remainder_lt)

theorem physical_remainder_nonzero_test
    (d e tailDivisor tailDividend : Nat)
    (he : e ≤ d) (hdivisor : tailDivisor < 2 ^ e)
    (hdividend : tailDividend < 2 ^ d) :
    ZeroWordTest.run (e + 1)
      (ZeroWordTest.cfg (some .scan) (false, none)
        (bitsBE e (remainder d e (monicBits e tailDivisor)
          (monicBits d tailDividend)))) =
    ZeroWordTest.cfg none
      ((remainder d e (monicBits e tailDivisor)
        (monicBits d tailDividend) != 0), none) [] := by
  let rem := remainder d e (monicBits e tailDivisor)
    (monicBits d tailDividend)
  have hsize : rem < 2 ^ e :=
    remainder_lt d e tailDivisor tailDividend he hdivisor hdividend
  have hseen : (bitsBE e rem).any id = (rem != 0) := by
    by_cases hz : rem = 0
    · simp [hz, bitsBE]
    · have hn : (bitsBE e rem).any id ≠ false := by
        intro hfalse
        exact hz ((bitsBE_any_false_iff_zero e rem hsize).mp hfalse)
      cases hb : (bitsBE e rem).any id <;> simp_all
  simpa [rem, hseen, bitsBE_length] using
    ZeroWordTest.run_correct false none (bitsBE e rem)

#print axioms physical_remainder_nonzero_test

end CurrentAdditive.FieldMachineHelper.TrialDivisorTest
