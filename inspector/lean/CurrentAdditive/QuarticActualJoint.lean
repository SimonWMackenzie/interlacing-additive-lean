import CurrentAdditive.QuarticActualLawError

/-!
# Product law for one actual v27 selected experiment

The chosen reduction tape and the estimator's independent fair tape form an
actual product finite law. This theorem reads all table entries from the
same selected output object; its hypotheses will be supplied by the v27
finite guarantees and the eventual estimator classifier.
-/

noncomputable section

namespace Paper2.CurrentAdditive.QuarticClassEndpoint

open Paper2 Paper2.CurrentAdditive.QuarticConstructor
open Paper2.Unit4Shell.Definitions (uniformTape)
open EthInapproximability.CurrentPaper.EncodedCommunication (natField)
open Workspace.Types.CommComplexity

theorem actual_joint_of_class_bias27
    (exp : TotalFiniteConstructorScratch.SelectedExperiment)
    (k : ℕ) (E : SelectedTape.Algorithm) (s : ℕ)
    (Yes No : Prop)
    (hfixed : ∀ t : exp.output.Tape,
      (HeaderStrip.selectedClassifier E).tapeLength
        (natField (2 * exp.output.budget + k) ++
          AModel.matrixWord exp.output.rows exp.output.cols (exp.output.table t).bits) = s)
    (hyes : Yes → ∀ t : exp.output.Tape,
      D (exp.output.table t).matrix ≤ exp.output.budget)
    (hgood : No →
      letI : Fintype exp.output.Tape := exp.tapeFintype
      1 - (1 / 2 : ℝ) ^ 11 ≤ exp.tapeLaw.prob (fun t =>
        exp.output.budget + k ≤ D (exp.output.table t).matrix))
    (hclass : ∀ t : exp.output.Tape,
      (D (exp.output.table t).matrix ≤ exp.output.budget →
        99 / 100 ≤ (HeaderStrip.selectedClassifier E).prob
          (natField (2 * exp.output.budget + k) ++
            AModel.matrixWord exp.output.rows exp.output.cols (exp.output.table t).bits)
          (· = [true])) ∧
      (exp.output.budget + k ≤ D (exp.output.table t).matrix →
        (HeaderStrip.selectedClassifier E).prob
          (natField (2 * exp.output.budget + k) ++
            AModel.matrixWord exp.output.rows exp.output.cols (exp.output.table t).bits)
          (· = [true]) ≤ 1 / 100)) :
    letI : Fintype exp.output.Tape := exp.tapeFintype
    (Yes → 99 / 100 ≤
      (exp.tapeLaw.prod (uniformTape s)).prob (fun x =>
        (HeaderStrip.selectedClassifier E).output
          (natField (2 * exp.output.budget + k) ++
            AModel.matrixWord exp.output.rows exp.output.cols
              (exp.output.table x.1).bits) (List.ofFn x.2) = [true])) ∧
    (No → (exp.tapeLaw.prod (uniformTape s)).prob (fun x =>
        (HeaderStrip.selectedClassifier E).output
          (natField (2 * exp.output.budget + k) ++
            AModel.matrixWord exp.output.rows exp.output.cols
              (exp.output.table x.1).bits) (List.ofFn x.2) = [true]) ≤
      (1 / 2 : ℝ) ^ 11 + 1 / 100) ∧
    (1 / 2 : ℝ) ^ 11 + 1 / 100 < 1 / 3 := by
  letI : Fintype exp.output.Tape := exp.tapeFintype
  exact two_stage_classifier_error27 exp.tapeLaw s
    (fun t => natField (2 * exp.output.budget + k) ++
      AModel.matrixWord exp.output.rows exp.output.cols (exp.output.table t).bits)
    E Yes No
    (fun t => exp.output.budget + k ≤ D (exp.output.table t).matrix)
    hfixed (fun hy t => (hclass t).1 (hyes hy t)) hgood
    (fun _ t ht => (hclass t).2 ht)

#print axioms Paper2.CurrentAdditive.QuarticClassEndpoint.actual_joint_of_class_bias27

end Paper2.CurrentAdditive.QuarticClassEndpoint
