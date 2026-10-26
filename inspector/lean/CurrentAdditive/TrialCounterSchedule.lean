import CurrentAdditive.TrialCounterMachine
import CurrentAdditive.TrialLoopCount

/-!
The physical fixed-width incrementer enumerates exactly the candidate tails
and the divisor tails inspected by the frozen executable trial search. This
is a schedule/representation bridge, not a whole-program TM composition.
-/

namespace CurrentAdditive.FieldMachineHelper.TrialCounterSchedule

open CurrentAdditive.FieldMachineHelper.TrialCounterMachine
open CurrentAdditive.FiniteFieldConstructor.TrialSearch

def counterCandidates (d : Nat) : List Nat :=
  (List.range (2 ^ d)).map fun k => monicBits d (bitsValue (counterWord d k))

theorem counterCandidates_eq (d : Nat) :
    counterCandidates d = (List.range (2 ^ d)).map (monicBits d) := by
  simpa [counterCandidates, List.map_map] using
    congrArg (List.map (monicBits d)) (candidate_values_are_range d)

theorem firstPassing_eq_counterCandidates (d : Nat) :
    firstPassing d =
      (counterCandidates d).find?
        (fun candidate => trialIrreducible d (candidate - 2 ^ d)) := by
  rw [firstPassing, counterCandidates_eq]

def counterDivisorSchedule (d : Nat) : List (Nat × Nat) :=
  (List.range (d / 2)).flatMap fun e0 =>
    (List.range (2 ^ (e0 + 1))).map fun k =>
      (e0 + 1, bitsValue (counterWord (e0 + 1) k))

theorem counterDivisorSchedule_eq (d : Nat) :
    counterDivisorSchedule d = divisorSchedule d := by
  unfold counterDivisorSchedule divisorSchedule
  apply List.flatMap_congr
  intro e0 he0
  simpa [List.map_map] using
    congrArg (List.map (fun tail => (e0 + 1, tail)))
      (candidate_values_are_range (e0 + 1))

#print axioms counterCandidates_eq
#print axioms firstPassing_eq_counterCandidates
#print axioms counterDivisorSchedule_eq

end CurrentAdditive.FieldMachineHelper.TrialCounterSchedule
