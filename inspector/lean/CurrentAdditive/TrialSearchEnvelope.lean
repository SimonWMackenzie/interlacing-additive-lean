import CurrentAdditive.TrialSearchControllerBridge
import CurrentAdditive.TrialScheduleCost

/-!
An arithmetic envelope for the exact full candidate/divisor schedule. Each
pair is charged its checked physical divider and zero-scan clock, the checked
`4*d+6` preparation clock, and `5*d+8` for the checked controller branches.
It is a sum of component clocks. A single composed program and proof of its
callback wiring are still required before this is an end-to-end machine clock.
-/

namespace CurrentAdditive.FieldMachineHelper.TrialSearchEnvelope

open CurrentAdditive.FieldMachineHelper.TrialScheduleCost
open CurrentAdditive.FiniteFieldConstructor.TrialSearch
open CurrentAdditive.FiniteFieldMachine.RuntimeArithmetic

def physicalPairEnvelope (d e : Nat) : Nat :=
  pairClock d e + (4 * d + 6) + (5 * d + 8)

def fullSearchEnvelope (d : Nat) : Nat :=
  ((fullTrialSchedule d).map fun p => physicalPairEnvelope d p.2.1).sum + 1

def uniformPhysicalPairEnvelope (d : Nat) : Nat :=
  uniformPairBudget d + 9 * d + 14

theorem pairEnvelope_le (d e : Nat) (he : e ≤ d) :
    physicalPairEnvelope d e ≤ uniformPhysicalPairEnvelope d := by
  have h := pairClock_le d e he
  unfold physicalPairEnvelope uniformPhysicalPairEnvelope
  omega

theorem fullSearchEnvelope_le (d : Nat) :
    fullSearchEnvelope d ≤ pairCount d * uniformPhysicalPairEnvelope d + 1 := by
  have hsum (l : List (Nat × Nat × Nat))
      (h : ∀ p ∈ l, p.2.1 ≤ d) :
      ((l.map fun p => physicalPairEnvelope d p.2.1).sum) ≤
        l.length * uniformPhysicalPairEnvelope d := by
    induction l with
    | nil => simp
    | cons p rest ih =>
      have hp : p.2.1 ≤ d := h p (by simp)
      have hr : ∀ q ∈ rest, q.2.1 ≤ d := by
        intro q hq
        exact h q (by simp [hq])
      have htail := ih hr
      have hhead := pairEnvelope_le d p.2.1 hp
      simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.succ_mul]
      omega
  have h := hsum (fullTrialSchedule d) (scheduled_degree_le d)
  simpa [fullSearchEnvelope, fullTrialSchedule_length] using Nat.add_le_add_right h 1

theorem uniformPhysicalPairEnvelope_quadratic (d : Nat) :
    uniformPhysicalPairEnvelope d ≤ 26 * (d + 1) ^ 2 := by
  have h := uniformPairBudget_quadratic d
  unfold uniformPhysicalPairEnvelope
  nlinarith [sq_nonneg (d : ℤ)]

/-- Component-clock sum, including input preparation and controller work. -/
theorem fullSearchEnvelope_lt_three_halves (d : Nat) :
    fullSearchEnvelope d <
      53 * 2 ^ d * 2 ^ (d / 2) * (d + 1) ^ 2 := by
  have hcount := pairCount_lt_three_halves_envelope d
  have hpair := uniformPhysicalPairEnvelope_quadratic d
  have hsum := fullSearchEnvelope_le d
  have hpositive : 0 < 26 * (d + 1) ^ 2 := by positivity
  have htotal : 0 < 2 ^ d * 2 ^ (d / 2) * (d + 1) ^ 2 := by positivity
  have hmult : pairCount d * (26 * (d + 1) ^ 2) <
      (2 * 2 ^ d * 2 ^ (d / 2)) * (26 * (d + 1) ^ 2) :=
    Nat.mul_lt_mul_of_pos_right hcount hpositive
  have hbound : fullSearchEnvelope d ≤
      pairCount d * (26 * (d + 1) ^ 2) + 1 := by
    calc
      fullSearchEnvelope d ≤ pairCount d * uniformPhysicalPairEnvelope d + 1 := hsum
      _ ≤ pairCount d * (26 * (d + 1) ^ 2) + 1 :=
        Nat.add_le_add_right (Nat.mul_le_mul_left _ hpair) 1
  nlinarith

#print axioms fullSearchEnvelope_lt_three_halves

end CurrentAdditive.FieldMachineHelper.TrialSearchEnvelope
