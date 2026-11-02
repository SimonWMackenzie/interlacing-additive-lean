import CurrentAdditive.QuarticEstimatorClassifier
import CurrentAdditive.QuarticMachineWrapper
import Paper2.E2Join

/-!
# Two-stage error of the v27 quartic classifier

The first stage chooses a retained submatrix under the actual selected law;
the second stage runs the amplified estimator on that one matrix. The
probability bound uses the same matrix in both stages and charges the source
failure and estimator failure separately.
-/

noncomputable section

namespace Paper2.CurrentAdditive.QuarticClassEndpoint

open Paper2 Paper2.FiniteLaw
open Paper2.Unit4Shell.Definitions (uniformTape)
open Paper2.Unit4Shell.Amplification

variable {α : Type} [Fintype α]

theorem two_stage_classifier_error27 (μ : FiniteLaw α) (s : ℕ)
    (F : α → List Bool)
    (E : SelectedTape.Algorithm)
    (Yes No : Prop)
    (Good : α → Prop)
    (hfixed : ∀ a, (HeaderStrip.selectedClassifier E).tapeLength (F a) = s)
    (hyes : Yes → ∀ a, 99 / 100 ≤
      (HeaderStrip.selectedClassifier E).prob (F a) (· = [true]))
    (hgood : No → 1 - (1 / 2 : ℝ) ^ 11 ≤ μ.prob Good)
    (hno : No → ∀ a, Good a →
      (HeaderStrip.selectedClassifier E).prob (F a) (· = [true]) ≤ 1 / 100) :
    (Yes → 99 / 100 ≤
      (μ.prod (uniformTape s)).prob (fun x =>
        (HeaderStrip.selectedClassifier E).output (F x.1) (List.ofFn x.2) = [true])) ∧
    (No → (μ.prod (uniformTape s)).prob (fun x =>
        (HeaderStrip.selectedClassifier E).output (F x.1) (List.ofFn x.2) = [true]) ≤
      (1 / 2 : ℝ) ^ 11 + 1 / 100) ∧
    (1 / 2 : ℝ) ^ 11 + 1 / 100 < 1 / 3 := by
  have hper : ∀ a (P : List Bool → Prop),
      (uniformTape s).prob (fun y =>
        P ((HeaderStrip.selectedClassifier E).output (F a) (List.ofFn y))) =
      (HeaderStrip.selectedClassifier E).prob (F a) P := by
    intro a P
    unfold SelectedTape.Algorithm.prob
    exact (AModel.uniformTape_prob_ofFn_congr (hfixed a)
      (fun w => P ((HeaderStrip.selectedClassifier E).output (F a) w))).symm
  have hfirstY : μ.prob (fun _ => ¬ True) ≤ 0 := by
    simp only [not_true_eq_false]
    rw [FiniteLaw.prob_false]
  have hsecondY (hy : Yes) : ∀ a, True →
      (uniformTape s).prob (fun y =>
        ¬ ((HeaderStrip.selectedClassifier E).output (F a) (List.ofFn y) = [true])) ≤
      1 / 100 := by
    intro a _
    have hcomp := prob_not (uniformTape s)
      (fun y => (HeaderStrip.selectedClassifier E).output (F a) (List.ofFn y) = [true])
    rw [hper a (· = [true])] at hcomp
    linarith [hyes hy a]
  have hfailY (hy : Yes) := FiniteLaw.two_stage_failure_le μ (uniformTape s)
    (fun _ => True)
    (fun a y => ¬ ((HeaderStrip.selectedClassifier E).output (F a) (List.ofFn y) = [true]))
    0 (1 / 100) hfirstY (hsecondY hy) (by norm_num)
  have hcompY := prob_not (μ.prod (uniformTape s))
    (fun x => (HeaderStrip.selectedClassifier E).output (F x.1) (List.ofFn x.2) = [true])
  have hfirstN (hn : No) : μ.prob (fun a => ¬ Good a) ≤ (1 / 2 : ℝ) ^ 11 := by
    have hcomp := prob_not μ Good
    linarith [hgood hn]
  have hsecondN (hn : No) : ∀ a, Good a →
      (uniformTape s).prob (fun y =>
        (HeaderStrip.selectedClassifier E).output (F a) (List.ofFn y) = [true]) ≤
      1 / 100 := by
    intro a ha
    rw [hper a (· = [true])]
    exact hno hn a ha
  have hfailN (hn : No) := FiniteLaw.two_stage_failure_le μ (uniformTape s) Good
    (fun a y => (HeaderStrip.selectedClassifier E).output (F a) (List.ofFn y) = [true])
    ((1 / 2 : ℝ) ^ 11) (1 / 100) (hfirstN hn) (hsecondN hn) (by norm_num)
  constructor
  · intro hy
    linarith [hfailY hy]
  constructor
  · intro hn
    exact hfailN hn
  · norm_num

#print axioms Paper2.CurrentAdditive.QuarticClassEndpoint.two_stage_classifier_error27

end Paper2.CurrentAdditive.QuarticClassEndpoint
