import CurrentAdditive.SmallBiasPClassInclusion
import Paper2.ADecider4OneSided
import EthInapproximability.CurrentPaper.SourceFieldWriter

/-!
# A deterministic polynomial estimator as a zero-tape selected algorithm

The existing selected-tape classifier already contains a physical median and
dyadic comparator. This adapter lets that implementation handle a
deterministic estimator: a checked projection recovers the raw estimator
input from `pair input []`, and the given estimator machine runs on it.
-/

noncomputable section

namespace CurrentAdditive.SmallBias

open Classical

set_option maxHeartbeats 2000000

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.EncodedComplexity

private def detCode (est : List Bool → List Bool)
    (hest : BitMachine.Polytime est) : List Bool → List Bool :=
  est ∘ firstPairField

private theorem detCode_polytime (est : List Bool → List Bool)
    (hest : BitMachine.Polytime est) : BitMachine.Polytime (detCode est hest) :=
  BitMachineComposition.polytime_comp firstPairField_polytime hest

noncomputable def selectedDetEstimator (est : List Bool → List Bool)
    (hest : BitMachine.Polytime est) : Paper2.SelectedTape.Algorithm := by
  let hp := detCode_polytime est hest
  let M := Classical.choose hp
  let c := Classical.choose (Classical.choose_spec hp)
  let d := Classical.choose (Classical.choose_spec (Classical.choose_spec hp))
  have hM : M.ComputesWithin (detCode est hest)
      (fun n => c * (n + 1) ^ d) :=
    Classical.choose_spec (Classical.choose_spec (Classical.choose_spec hp))
  refine { cR := 0, dR := 0, cT := c * 2 ^ d, dT := d, machine := M, output := (fun x _ => est x), runs := ?_ }
  intro x t
  have ht : List.ofFn t = [] := by
    apply List.eq_nil_of_length_eq_zero
    simp
  have hr := hM (pair x [])
  have hlen : (pair x []).length + 1 = 2 * (x.length + 1) := by
    rw [pair_length]
    simp
    omega
  change M.OutputsWithin (pair x []) (detCode est hest (pair x []))
    (c * ((pair x []).length + 1) ^ d) at hr
  rw [hlen, mul_pow] at hr
  have hout : detCode est hest (pair x []) = est x := by
    simp only [detCode, Function.comp_apply, firstPairField_pair]
  rw [hout] at hr
  rw [← mul_assoc] at hr
  rw [ht]
  exact hr

theorem selectedDetEstimator_tapeLength (est : List Bool → List Bool)
    (hest : BitMachine.Polytime est) (x : List Bool) :
    (selectedDetEstimator est hest).tapeLength x = 0 := rfl

theorem selectedDetEstimator_output (est : List Bool → List Bool)
    (hest : BitMachine.Polytime est) (x tape : List Bool) :
    (selectedDetEstimator est hest).output x tape = est x := rfl

theorem selectedDetEstimator_prob (est : List Bool → List Bool)
    (hest : BitMachine.Polytime est) (x : List Bool) (E : List Bool → Prop) :
    (selectedDetEstimator est hest).prob x E =
      if E (est x) then 1 else 0 := by
  classical
  simp [Paper2.SelectedTape.Algorithm.prob,
    selectedDetEstimator_tapeLength, selectedDetEstimator_output,
    Paper2.FiniteLaw.prob, Paper2.Unit4Shell.Definitions.uniformTape]

#print axioms CurrentAdditive.SmallBias.selectedDetEstimator_prob

end CurrentAdditive.SmallBias
