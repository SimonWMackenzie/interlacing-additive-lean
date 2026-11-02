import Paper2.E2Sel
import Paper2.HeaderClassifierSelected

/-! a-eth-owner-2 copy of frozen `a-eth-owner-1/AEthClassifier.lean` (SHA-256 1a85577de69db25c9370e9ea631981c7dfe94fca11d7f6627cebe2eaafa3ebf5). Changes: import `AEthClass` -> `E2Sel`. -/

/-!
# Paper A (lock v12), lane `owner:a-eth-1`, segment 3 (partial): the A27 selected classifier with
PER-WORD (growing) accuracy

Lock v12 `sections/06-reduction.tex:134-137` (proof of `thm:quantitative`): "Thus for every fixed
$c<1/12$ the gap $k$ eventually exceeds twice the proposed error. The midpoint test from
\cref{intro:corollary} decides the formula with bounded error."

The A27 statements `HeaderStrip.selectedClassifier_yes/no` (private, independently reviewed, in
the frozen overlay) assume ONE accuracy `a` on EVERY matrix word. A growing estimator
(`EstimatesGrowingSel`) has accuracy `accT c w = c·log₂T/log₂log₂T`, unbounded over all words,
so those statements do not apply to the growing-gap decider. The admitted comparator lemmas
`CmpOwner.medAlgC_yes_natField/no_natField` need the success hypothesis only at the one word
used; this module re-derives the classifier bounds with the hypothesis at that word only
(`selectedClassifier_yes_at`, `selectedClassifier_no_at`) and instantiates them with the growing
accuracy (`growing_classifier_yes/no`). Reuses A27 `selectedClassifier_prob` and
`selectedEstimator_toPrefix_prob` by exact name.

No ledger row is closed.
-/

noncomputable section

namespace Paper2.AEth

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.EncodedCommunication (natField)

/-- **YES side with the success hypothesis at the one word.** -/
theorem selectedClassifier_yes_at (A : Paper2.SelectedTape.Algorithm) (a : ℝ)
    (rest : List Bool) (c B k : ℕ)
    (hA : 2 / 3 ≤ A.prob rest (fun out => ∃ v,
      Paper2.AModel.decodeDyadic out = some v ∧ |v - c| ≤ a))
    (hk : 2 * a < k) (hcB : c ≤ B) :
    99 / 100 ≤ (Paper2.HeaderStrip.selectedClassifier A).prob (natField (2 * B + k) ++ rest)
      (· = [true]) := by
  rw [Paper2.HeaderStrip.selectedClassifier_prob]
  exact Paper2.CmpOwner.medAlgC_yes_natField ((Paper2.HeaderStrip.selectedEstimator A).toPrefix)
    rest c a B k hk
    (by rw [Paper2.HeaderStrip.selectedEstimator_toPrefix_prob]; exact hA) hcB

/-- **NO side with the success hypothesis at the one word.** -/
theorem selectedClassifier_no_at (A : Paper2.SelectedTape.Algorithm) (a : ℝ)
    (rest : List Bool) (c B k : ℕ)
    (hA : 2 / 3 ≤ A.prob rest (fun out => ∃ v,
      Paper2.AModel.decodeDyadic out = some v ∧ |v - c| ≤ a))
    (hk : 2 * a < k) (hBc : B + k ≤ c) :
    (Paper2.HeaderStrip.selectedClassifier A).prob (natField (2 * B + k) ++ rest)
      (· = [true]) ≤ 1 / 100 := by
  rw [Paper2.HeaderStrip.selectedClassifier_prob]
  exact Paper2.CmpOwner.medAlgC_no_natField ((Paper2.HeaderStrip.selectedEstimator A).toPrefix)
    rest c a B k hk
    (by rw [Paper2.HeaderStrip.selectedEstimator_toPrefix_prob]; exact hA) hBc

/-- **Growing accuracy, YES side**: on a decodable matrix word `w` with target `d ≤ B`, if the
gap exceeds twice the growing accuracy at `w`, the classifier accepts `natField (2B+k) ++ w`
with probability `≥ 99/100`. -/
theorem growing_classifier_yes (E : Paper2.SelectedTape.Algorithm) (c : ℝ)
    (hE : EstimatesGrowingSel E c) (w : List Bool) (d B k : ℕ)
    (hd : Paper2.AModel.targetD w = some d) (hk : 2 * ADecider.accT c w < k) (hdB : d ≤ B) :
    99 / 100 ≤ (Paper2.HeaderStrip.selectedClassifier E).prob (natField (2 * B + k) ++ w)
      (· = [true]) :=
  selectedClassifier_yes_at E (ADecider.accT c w) w d B k (hE w d hd) hk hdB

/-- **Growing accuracy, NO side.** -/
theorem growing_classifier_no (E : Paper2.SelectedTape.Algorithm) (c : ℝ)
    (hE : EstimatesGrowingSel E c) (w : List Bool) (d B k : ℕ)
    (hd : Paper2.AModel.targetD w = some d) (hk : 2 * ADecider.accT c w < k) (hBd : B + k ≤ d) :
    (Paper2.HeaderStrip.selectedClassifier E).prob (natField (2 * B + k) ++ w)
      (· = [true]) ≤ 1 / 100 :=
  selectedClassifier_no_at E (ADecider.accT c w) w d B k (hE w d hd) hk hBd

end Paper2.AEth

end

#print axioms Paper2.AEth.selectedClassifier_yes_at
#print axioms Paper2.AEth.selectedClassifier_no_at
#print axioms Paper2.AEth.growing_classifier_yes
#print axioms Paper2.AEth.growing_classifier_no
