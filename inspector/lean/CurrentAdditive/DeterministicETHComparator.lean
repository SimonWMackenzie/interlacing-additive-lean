import CurrentAdditive.DeterministicETHEstimator
import Paper2.CmpSpecProof

/-! Reuse the earlier checked physical dyadic comparator at the dynamic
integer midpoint. The comparator machine is fixed; the numerator `2B+k`
is carried in its input word. -/

namespace CurrentAdditive.DeterministicETHComparator

open EthInapproximability.CurrentPaper

def midpointHeader (B k : ℕ) : List Bool :=
  EncodedCommunication.natField (2*B+k)

theorem comparator_spec_of_decoded (B k : ℕ) (out : List Bool) (z : ℝ)
    (hdecode : Paper2.AModel.decodeDyadic out = some z) :
    Paper2.CmpOwner.spec (midpointHeader B k) out = true ↔
      z < (B:ℝ)+(k:ℝ)/2 := by
  rw [Paper2.CmpOwner.spec_iff]
  have hθ : Paper2.CmpOwner.thrW (EncodedCommunication.natField (2*B+k)) =
      (B:ℝ)+(k:ℝ)/2 := by
    simpa using Paper2.CmpOwner.thrW_midpoint B k ([] : List Bool)
  change Paper2.MedianOwner.Below Paper2.AModel.decodeDyadic
      (Paper2.CmpOwner.thrW (EncodedCommunication.natField (2*B+k))) out ↔ _
  rw [hθ]
  simp only [Paper2.MedianOwner.Below, hdecode, Option.some.injEq]
  constructor
  · rintro ⟨v, hv, hlt⟩
    rw [hv]
    exact hlt
  · intro h
    exact ⟨z, rfl, h⟩

/-- The already-built TM2 comparator physically prints the midpoint bit
on the actual dyadic estimator output. -/
theorem comparator_run (B k : ℕ) (out : List Bool) (z : ℝ)
    (hdecode : Paper2.AModel.decodeDyadic out = some z) :
    Paper2.CmpOwner.machine.OutputsWithin
      (EncodedComplexity.pair (midpointHeader B k) out)
      [decide (z < (B:ℝ)+(k:ℝ)/2)]
      (Paper2.CmpOwner.cmpTime (midpointHeader B k).length out.length) := by
  have hr := Paper2.CmpOwner.cmp_outputs (midpointHeader B k) out
  have hb : Paper2.CmpOwner.spec (midpointHeader B k) out =
      decide (z < (B:ℝ)+(k:ℝ)/2) := by
    apply Bool.eq_iff_iff.mpr
    simpa only [decide_eq_true_eq] using
      comparator_spec_of_decoded B k out z hdecode
  simpa only [hb] using hr

#print axioms comparator_spec_of_decoded
#print axioms comparator_run

end CurrentAdditive.DeterministicETHComparator
