import CurrentAdditive.TrialSearchGlobalTransitions
import CurrentAdditive.TrialSearchCorrectedEnvelope

/-! Every branch of the literal combined search machine fits the corrected
per-divisor budget, including the physical cleanup of the divisor word. -/

namespace CurrentAdditive.FieldSearchCompletion

open CurrentAdditive.FieldMachineHelper.TrialSearchCorrectedEnvelope
open CurrentAdditive.FieldMachineHelper.TrialSearchEnvelope
open CurrentAdditive.FieldMachineHelper.TrialScheduleCost
open CurrentAdditive.FieldMachineHelper.TrialDividerTotal (divisionClock)

theorem nonlast_divisor_budget (d e : Nat) (he : e ≤ d) :
    1 + 4 * d + 6 +
      (divisionClock e (d - e + 1) + 2 * e + 3) + (2 * e + 3) ≤
        correctedPairEnvelope d e := by
  unfold correctedPairEnvelope physicalPairEnvelope pairClock
  omega

theorem last_divisor_budget (d e : Nat) (he : e < d / 2) :
    callbackClock d e + (4 * e + 8) ≤
      correctedPairEnvelope d e := by
  unfold callbackClock correctedPairEnvelope physicalPairEnvelope pairClock
  omega

theorem last_degree_budget (d e : Nat) (he : e = d / 2) (hd : 0 < e) :
    callbackClock d e + (2 * e + 5) ≤
      correctedPairEnvelope d e := by
  unfold callbackClock correctedPairEnvelope physicalPairEnvelope pairClock
  omega

theorem fail_nonlast_budget (d e : Nat) (he : e ≤ d / 2) :
    callbackClock d e + (2 * d + 3 * e + 4) ≤
      correctedPairEnvelope d e := by
  unfold callbackClock correctedPairEnvelope physicalPairEnvelope pairClock
  omega

theorem fail_last_budget (d e : Nat) (he : e ≤ d / 2) :
    callbackClock d e + (2 * d + 3) ≤
      correctedPairEnvelope d e := by
  unfold callbackClock correctedPairEnvelope physicalPairEnvelope pairClock
  omega

#print axioms nonlast_divisor_budget
#print axioms last_divisor_budget
#print axioms last_degree_budget
#print axioms fail_nonlast_budget
#print axioms fail_last_budget

end CurrentAdditive.FieldSearchCompletion
