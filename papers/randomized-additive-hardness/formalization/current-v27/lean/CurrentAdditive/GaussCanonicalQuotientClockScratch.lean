import CurrentAdditive.GaussCellQuotient
import EthInapproximability.CurrentPaper.BitMachineCompositionArithmetic

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

namespace CurrentAdditive.GaussCanonicalQuotientClockScratch

open EthInapproximability.CurrentPaper

theorem canonical_computes_polynomial :
    ∃ c : Nat, GaussCellQuotient.canonicalMachine.ComputesWithin
      GaussCellQuotient.canonicalResult (fun n => c*(n+1)^194) := by
  obtain ⟨a,ha⟩ := RationalCanonicalCallback.quotient_outputs_all
  let A := GaussPhysical.GaussBranchSelect.machine
  let B := RationalCanonicalCallback.quotientMachine
  let C := GaussCellQuotient.canonicalMachine
  let c := 35 + 2*(35*A.pushBound+1) + a*(35*A.pushBound+1)^96
  refine ⟨c, ?_⟩
  intro input
  let middle := GaussPhysical.GaussBranchSelect.result input
  have hfirst : A.OutputsWithin input middle (35*(input.length+1)^1) := by
    simpa only [A, middle, pow_one] using
      GaussPhysical.GaussBranchSelect.outputs input
  have hsecond : B.OutputsWithin middle
      (RationalCanonicalCallback.quotientResult middle)
      (a*(middle.length+1)^96) := ha middle
  have hcomp := BitMachineComposition.composition_outputsWithin A B
    hfirst hsecond
  have hlen := BitMachine.output_length_bound A hfirst
  have hclock := BitMachineCompositionArithmetic.composition_time_bound
    input.length 35 1 a 96 A.pushBound middle.length hlen
  have hclock' :
      35*(input.length+1)^1 + 2*middle.length+2 +
        a*(middle.length+1)^96 ≤ c*(input.length+1)^194 := by
    simpa only [c, show (1+1)*(96+1) = 194 by norm_num] using hclock
  apply BitMachine.outputsWithin_mono C
    (by simpa only [C, A, B, GaussCellQuotient.canonicalMachine,
      GaussCellQuotient.canonicalResult, middle] using hcomp)
  exact hclock'

#print axioms canonical_computes_polynomial

end CurrentAdditive.GaussCanonicalQuotientClockScratch
