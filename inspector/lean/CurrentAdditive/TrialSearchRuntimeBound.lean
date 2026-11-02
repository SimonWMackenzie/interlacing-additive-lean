import CurrentAdditive.TrialSearchFromDegree
import CurrentAdditive.TrialSearchCorrectedEnvelope

/-! The global physical clock fits the corrected three-halves search bound.
The extra first transition enters the outer controller. -/

namespace CurrentAdditive.FieldSearchCompletion

open CurrentAdditive.FieldMachineHelper.TrialSearchCorrectedEnvelope
open CurrentAdditive.FiniteFieldMachine.RuntimeArithmetic

theorem prefixBudget_uniform (d : Nat) :
    prefixBudget d (d / 2) ≤
      divisorCount (d / 2) * correctedUniformPairEnvelope d := by
  unfold prefixBudget divisorCount
  calc
    (∑ i ∈ Finset.range (d / 2),
        2 ^ (i + 1) * correctedPairEnvelope d (i + 1)) ≤
      ∑ i ∈ Finset.range (d / 2),
        2 ^ (i + 1) * correctedUniformPairEnvelope d := by
          apply Finset.sum_le_sum
          intro i hi
          have hie : i + 1 ≤ d := by
            have h : i < d / 2 := Finset.mem_range.mp hi
            omega
          exact Nat.mul_le_mul_left _ (correctedPairEnvelope_le d (i + 1) hie)
    _ = (∑ i ∈ Finset.range (d / 2), 2 ^ (i + 1)) *
          correctedUniformPairEnvelope d := by
            rw [Finset.sum_mul]

theorem firstPassing_physical_clock_lt (d : Nat) :
    1 + 2 ^ d * prefixBudget d (d / 2) <
      55 * 2 ^ d * 2 ^ (d / 2) * (d + 1) ^ 2 := by
  have hp := prefixBudget_uniform d
  have hu := correctedUniformPairEnvelope_quadratic d
  have hc := pairCount_lt_three_halves_envelope d
  have hpositive : 0 < 27 * (d + 1) ^ 2 := by positivity
  have hunit : 0 < 2 ^ d * 2 ^ (d / 2) * (d + 1) ^ 2 := by positivity
  have hprod :
      pairCount d * (27 * (d + 1) ^ 2) <
        (2 * 2 ^ d * 2 ^ (d / 2)) *
          (27 * (d + 1) ^ 2) :=
    Nat.mul_lt_mul_of_pos_right hc hpositive
  have hbound : 2 ^ d * prefixBudget d (d / 2) ≤
      pairCount d * (27 * (d + 1) ^ 2) := by
    calc
      2 ^ d * prefixBudget d (d / 2) ≤
          2 ^ d *
            (divisorCount (d / 2) * correctedUniformPairEnvelope d) :=
        Nat.mul_le_mul_left _ hp
      _ = pairCount d * correctedUniformPairEnvelope d := by
        simp [pairCount]; ring
      _ ≤ pairCount d * (27 * (d + 1) ^ 2) :=
        Nat.mul_le_mul_left _ hu
  nlinarith

theorem physical_firstPassing_with_clock (d : Nat) (hd : 0 < d) :
    ∃ c < 2 ^ d,
      CurrentAdditive.FiniteFieldConstructor.TrialSearch.firstPassing d =
        some (CurrentAdditive.FiniteFieldConstructor.TrialSearch.monicBits d c) ∧
      ∃ steps < 55 * 2 ^ d * 2 ^ (d / 2) * (d + 1) ^ 2,
        let g := CurrentAdditive.FieldMachineHelper.TrialSearchCombinedMachine.run
          steps (initialConfig d)
        g.l = some (.outer .success) ∧
        g.stk 0 =
          CurrentAdditive.FieldMachineHelper.TrialCounterMachine.counterWord d c := by
  obtain ⟨c, hc, hfirst, steps, hsteps, hout⟩ :=
    physical_firstPassing_total d hd
  exact ⟨c, hc, hfirst, steps,
    lt_of_le_of_lt hsteps (firstPassing_physical_clock_lt d), hout⟩

#print axioms prefixBudget_uniform
#print axioms firstPassing_physical_clock_lt
#print axioms physical_firstPassing_with_clock

end CurrentAdditive.FieldSearchCompletion
