import Paper2.HeaderComparatorSelected

/-!
# Final selected-pair carrier for the strip-estimate-median comparator

This reifies the already checked physical median program with its literal
monomial random-tape length. Its selected-pair machine clock is obtained by
the independently checked restricted `ofPrefixMonomial` adapter, not by an
arbitrary input-dependent tape-length field.
-/

noncomputable section

namespace Paper2.HeaderStrip

open EthInapproximability.CurrentPaper.EncodedCommunication

private theorem medianTapeShape (A : Paper2.SelectedTape.Algorithm) :
    ∃ cR dR : ℕ, ∀ n,
      (selectedMedianDecision A).tapeLength n = cR * (n + 1) ^ dR :=
  ⟨Paper2.Unit4Shell.Amplification.reps * (selectedEstimator A).cR,
    (selectedEstimator A).dR, selectedMedianDecision_tapeLength A⟩

/-- One selected-pair fixed-tape algorithm. Its machine is the physical
`medAlgC` program over the physical strip-then-estimate machine. -/
def selectedClassifier (A : Paper2.SelectedTape.Algorithm) :
    Paper2.SelectedTape.Algorithm :=
  Paper2.SelectedTape.Algorithm.ofPrefixMonomial
    (selectedMedianDecision A) (selectedMedianDecision_polynomial A)
    (medianTapeShape A)

theorem selectedClassifier_machine (A : Paper2.SelectedTape.Algorithm) :
    (selectedClassifier A).machine =
      Paper2.MedianOwner.Med.medMachine 146
        (selectedEstimator A).toPrefix.machine Paper2.CmpOwner.machine := by
  change (selectedMedianDecision A).machine = _
  exact Paper2.CmpOwner.medAlgC_machine ((selectedEstimator A).toPrefix)

theorem selectedClassifier_prob (A : Paper2.SelectedTape.Algorithm)
    (w : List Bool) (E : List Bool → Prop) :
    (selectedClassifier A).prob w E = (selectedMedianDecision A).prob w E :=
  Paper2.SelectedTape.Algorithm.ofPrefixMonomial_prob
    (selectedMedianDecision A) (selectedMedianDecision_polynomial A)
    (medianTapeShape A) w E

theorem selectedClassifier_yes (A : Paper2.SelectedTape.Algorithm) (a : ℝ)
    (hA : ∀ w c, Paper2.AModel.targetD w = some c →
      2 / 3 ≤ A.prob w (fun out => ∃ v,
        Paper2.AModel.decodeDyadic out = some v ∧ |v - c| ≤ a))
    (rest : List Bool) (c B k : ℕ)
    (htarget : Paper2.AModel.targetD rest = some c)
    (hk : 2 * a < k) (hcB : c ≤ B) :
    99 / 100 ≤ (selectedClassifier A).prob (natField (2 * B + k) ++ rest)
      (· = [true]) := by
  rw [selectedClassifier_prob]
  exact selectedMedianDecision_yes A a hA rest c B k htarget hk hcB

theorem selectedClassifier_no (A : Paper2.SelectedTape.Algorithm) (a : ℝ)
    (hA : ∀ w c, Paper2.AModel.targetD w = some c →
      2 / 3 ≤ A.prob w (fun out => ∃ v,
        Paper2.AModel.decodeDyadic out = some v ∧ |v - c| ≤ a))
    (rest : List Bool) (c B k : ℕ)
    (htarget : Paper2.AModel.targetD rest = some c)
    (hk : 2 * a < k) (hBc : B + k ≤ c) :
    (selectedClassifier A).prob (natField (2 * B + k) ++ rest)
      (· = [true]) ≤ 1 / 100 := by
  rw [selectedClassifier_prob]
  exact selectedMedianDecision_no A a hA rest c B k htarget hk hBc

/-- The selected-pair all-tape clock is a field of this actual machine,
spelled out for the subsequent SAT-decider composition. -/
theorem selectedClassifier_runs (A : Paper2.SelectedTape.Algorithm)
    (w : List Bool) (t : Fin ((selectedClassifier A).tapeLength w) → Bool) :
    (selectedClassifier A).machine.OutputsWithin
      (EthInapproximability.CurrentPaper.EncodedComplexity.pair w (List.ofFn t))
      ((selectedClassifier A).output w (List.ofFn t))
      ((selectedClassifier A).cT * (w.length + 1) ^ (selectedClassifier A).dT) :=
  (selectedClassifier A).runs w t

#print axioms selectedClassifier_prob
#print axioms selectedClassifier_machine
#print axioms selectedClassifier_yes
#print axioms selectedClassifier_no
#print axioms selectedClassifier_runs

end Paper2.HeaderStrip
