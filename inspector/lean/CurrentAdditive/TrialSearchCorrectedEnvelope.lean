import CurrentAdditive.TrialSearchEnvelope

/-!
The combined physical machine clears the residual divisor word after the
remainder's zero scan. This adds `e+1` real TM2 steps per tested divisor to
the earlier component envelope. The theorem below charges those steps; it
remains a schedule sum, not a proof that the global machine follows the
schedule.
-/

namespace CurrentAdditive.FieldMachineHelper.TrialSearchCorrectedEnvelope

open CurrentAdditive.FieldMachineHelper.TrialSearchEnvelope
open CurrentAdditive.FiniteFieldConstructor.TrialSearch
open CurrentAdditive.FiniteFieldMachine.RuntimeArithmetic
open CurrentAdditive.FieldMachineHelper.TrialScheduleCost

def correctedPairEnvelope (d e : Nat) : Nat :=
  physicalPairEnvelope d e + e + 1

def correctedSearchEnvelope (d : Nat) : Nat :=
  ((fullTrialSchedule d).map fun p => correctedPairEnvelope d p.2.1).sum + 1

def correctedUniformPairEnvelope (d : Nat) : Nat :=
  uniformPhysicalPairEnvelope d + d + 1

theorem correctedPairEnvelope_le (d e : Nat) (he : e ≤ d) :
    correctedPairEnvelope d e ≤ correctedUniformPairEnvelope d := by
  have h := pairEnvelope_le d e he
  unfold correctedPairEnvelope correctedUniformPairEnvelope
  omega

theorem correctedSearchEnvelope_le (d : Nat) :
    correctedSearchEnvelope d ≤
      pairCount d * correctedUniformPairEnvelope d + 1 := by
  have hsum (l : List (Nat × Nat × Nat))
      (h : ∀ p ∈ l, p.2.1 ≤ d) :
      ((l.map fun p => correctedPairEnvelope d p.2.1).sum) ≤
        l.length * correctedUniformPairEnvelope d := by
    induction l with
    | nil => simp
    | cons p rest ih =>
      have hp : p.2.1 ≤ d := h p (by simp)
      have hr : ∀ q ∈ rest, q.2.1 ≤ d := by
        intro q hq
        exact h q (by simp [hq])
      have htail := ih hr
      have hhead := correctedPairEnvelope_le d p.2.1 hp
      simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.succ_mul]
      omega
  have h := hsum (fullTrialSchedule d) (scheduled_degree_le d)
  simpa [correctedSearchEnvelope, fullTrialSchedule_length] using
    Nat.add_le_add_right h 1

theorem correctedUniformPairEnvelope_quadratic (d : Nat) :
    correctedUniformPairEnvelope d ≤ 27 * (d + 1) ^ 2 := by
  have h := uniformPhysicalPairEnvelope_quadratic d
  unfold correctedUniformPairEnvelope
  nlinarith [sq_nonneg (d : ℤ)]

theorem correctedSearchEnvelope_lt_three_halves (d : Nat) :
    correctedSearchEnvelope d <
      55 * 2 ^ d * 2 ^ (d / 2) * (d + 1) ^ 2 := by
  have hcount := pairCount_lt_three_halves_envelope d
  have hpair := correctedUniformPairEnvelope_quadratic d
  have hsum := correctedSearchEnvelope_le d
  have hpositive : 0 < 27 * (d + 1) ^ 2 := by positivity
  have htotal : 0 < 2 ^ d * 2 ^ (d / 2) * (d + 1) ^ 2 := by positivity
  have hmult : pairCount d * (27 * (d + 1) ^ 2) <
      (2 * 2 ^ d * 2 ^ (d / 2)) * (27 * (d + 1) ^ 2) :=
    Nat.mul_lt_mul_of_pos_right hcount hpositive
  have hbound : correctedSearchEnvelope d ≤
      pairCount d * (27 * (d + 1) ^ 2) + 1 := by
    calc
      correctedSearchEnvelope d ≤
          pairCount d * correctedUniformPairEnvelope d + 1 := hsum
      _ ≤ pairCount d * (27 * (d + 1) ^ 2) + 1 :=
        Nat.add_le_add_right (Nat.mul_le_mul_left _ hpair) 1
  nlinarith

#print axioms correctedSearchEnvelope_lt_three_halves

end CurrentAdditive.FieldMachineHelper.TrialSearchCorrectedEnvelope
