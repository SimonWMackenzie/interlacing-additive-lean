import CurrentAdditive.V39FramedComparator
import CurrentAdditive.V39StrictHalfMajority

/-!
Permitted-model correction. Physical comparison is total on all words;
numerical correctness is required ONLY at the one supplied valid input word and
on its actual selected-tape outputs. A consumer may restrict that word to
its valid matrix image. No numerical property of malformed input words or
unreachable output words appears in this interface.
-/

noncomputable section
open Classical

namespace CurrentAdditive.V39ActualOutputMajority

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.EncodedCommunication
open EthInapproximability.CurrentPaper.EncodedComplexity
open CurrentAdditive.V39FramedComparator
open CurrentAdditive.ModelEndpointReview.RationalEndpoint
open CurrentAdditive.V39GeneralHalfMajority
open Paper2 Paper2.FiniteLaw
open Paper2.Unit4Shell.Amplification
open Paper2.Unit4Shell.Definitions (uniformTape)

structure ActualEstimator where
  estimator : SelectedTape.Algorithm
  value : List Bool → ℝ
  comparator : FramedComparator

def ActualEstimator.header (E : ActualEstimator) : AModel.PrefixAlgorithm :=
  (HeaderStrip.selectedEstimator E.estimator).toPrefix

theorem ActualEstimator.headerPoly (E : ActualEstimator) : E.header.Polynomial :=
  HeaderStrip.selectedEstimator_toPrefix_polynomial E.estimator

def ActualEstimator.majority (E : ActualEstimator) : AModel.PrefixAlgorithm :=
  medAlgJudge E.header (comparisonMachine E.comparator) E.comparator.judge
    (compareClock E.header E.headerPoly E.comparator)
    (comparisonSpec E.header E.headerPoly E.comparator)

theorem ActualEstimator.majority_poly (E : ActualEstimator) : E.majority.Polynomial :=
  medAlgJudge_polynomial _ _ _ _
    (comparisonSpec E.header E.headerPoly E.comparator) E.headerPoly
    (compareClock_poly E.header E.headerPoly E.comparator)

theorem ActualEstimator.majority_tape (E : ActualEstimator) (n : ℕ) :
    E.majority.tapeLength n =
      (147 * (HeaderStrip.selectedEstimator E.estimator).cR) *
        (n + 1) ^ (HeaderStrip.selectedEstimator E.estimator).dR := by
  change 147 * ((HeaderStrip.selectedEstimator E.estimator).cR *
    (n + 1) ^ (HeaderStrip.selectedEstimator E.estimator).dR) = _
  ring

private theorem ActualEstimator.shape (E : ActualEstimator) :
    ∃ c d : ℕ, ∀ n, E.majority.tapeLength n = c * (n + 1) ^ d :=
  ⟨147 * (HeaderStrip.selectedEstimator E.estimator).cR,
    (HeaderStrip.selectedEstimator E.estimator).dR, E.majority_tape⟩

def ActualEstimator.classifier (E : ActualEstimator) : SelectedTape.Algorithm :=
  SelectedTape.Algorithm.ofPrefixMonomial E.majority E.majority_poly E.shape

theorem ActualEstimator.classifier_prob (E : ActualEstimator)
    (word : List Bool) (P : List Bool → Prop) :
    E.classifier.prob word P = E.majority.prob word P :=
  SelectedTape.Algorithm.ofPrefixMonomial_prob E.majority E.majority_poly E.shape word P

/-- Comparison only on actual outputs at this one word. This includes
inaccurate estimator runs but says nothing about any other input word.
The public midpoint numerator m is fixed before the estimator tape. -/
def ActualEstimator.actualComparison (E : ActualEstimator) (word : List Bool) (m : ℕ) : Prop :=
  ∀ tape : Fin (E.estimator.tapeLength word) → Bool,
    E.comparator.output (pair (natField m ++ word)
      (E.estimator.output word (List.ofFn tape))) =
    decide (E.value (E.estimator.output word (List.ofFn tape)) < (m : ℝ) / 2)

theorem ActualEstimator.header_vote_prob (E : ActualEstimator) (m : ℕ) (word : List Bool) :
    E.header.prob (natField m ++ word)
      (fun out => E.comparator.judge (natField m ++ word) out = true) =
    E.estimator.prob word
      (fun out => E.comparator.output (pair (natField m ++ word) out) = true) := by
  simp only [FramedComparator.judge]
  exact HeaderStrip.selectedEstimator_toPrefix_prob E.estimator m word _

theorem ActualEstimator.classifier_accept_prob (E : ActualEstimator) (word : List Bool) :
    E.classifier.prob word (· = [true]) =
    (uniformTape (reps * E.header.tapeLength word.length)).prob (fun t =>
      reps < 2 * Fintype.card {i : Fin reps //
        E.comparator.judge word (E.header.output word
          (List.ofFn (MedianOwner.seg reps (E.header.tapeLength word.length) t i))) = true}) := by
  rw [E.classifier_prob, ActualEstimator.majority, medAlgJudge_prob]

/-- Only the one-run comparator-bit probability is needed by the actual
majority machine. It is transferred through physical header stripping as an
output-event law, so unreachable header outputs need no numerical meaning. -/
theorem ActualEstimator.classifier_yes_votes (E : ActualEstimator) (m : ℕ) (word : List Bool)
    (hvote : 2 / 3 ≤ E.estimator.prob word
      (fun out => E.comparator.output (pair (natField m ++ word) out) = true)) :
    99 / 100 < E.classifier.prob (natField m ++ word) (· = [true]) := by
  let w := natField m ++ word
  let s := E.header.tapeLength w.length
  let Good := fun tape : Fin s → Bool =>
    E.comparator.judge w (E.header.output w (List.ofFn tape)) = true
  have hbase : 2 / 3 ≤ (uniformTape s).prob Good := by
    change 2 / 3 ≤ E.header.prob w (fun out => E.comparator.judge w out = true)
    rw [E.header_vote_prob]
    exact hvote
  have h := iid_majority_good_gt (uniformTape s) Good hbase
  rw [E.classifier_accept_prob]
  change 99 / 100 < (uniformTape (reps * s)).prob
    (fun t => reps < 2 * Fintype.card {i : Fin reps // Good (MedianOwner.seg reps s t i)})
  rw [MedianOwner.segment_prob reps s
    (fun x => reps < 2 * Fintype.card {i : Fin reps // Good (x i)})]
  simpa only [← Nat.card_eq_fintype_card] using h

theorem ActualEstimator.classifier_no_votes (E : ActualEstimator) (m : ℕ) (word : List Bool)
    (hvote : E.estimator.prob word
      (fun out => E.comparator.output (pair (natField m ++ word) out) = true) ≤ 1 / 3) :
    E.classifier.prob (natField m ++ word) (· = [true]) < 1 / 100 := by
  let w := natField m ++ word
  let s := E.header.tapeLength w.length
  let Good := fun tape : Fin s → Bool =>
    E.comparator.judge w (E.header.output w (List.ofFn tape)) = true
  have hbase : (uniformTape s).prob Good ≤ 1 / 3 := by
    change E.header.prob w (fun out => E.comparator.judge w out = true) ≤ 1 / 3
    rw [E.header_vote_prob]
    exact hvote
  have h := iid_half_bad_lt (uniformTape s) Good hbase
  have hm := FiniteLaw.prob_mono ((uniformTape s).iid reps)
    (show ∀ tape, reps < 2 * Fintype.card {i : Fin reps // Good (tape i)} →
      reps ≤ 2 * Fintype.card {i : Fin reps // Good (tape i)} from fun _ ht => Nat.le_of_lt ht)
  rw [E.classifier_accept_prob]
  change (uniformTape (reps * s)).prob
    (fun t => reps < 2 * Fintype.card {i : Fin reps // Good (MedianOwner.seg reps s t i)}) < 1 / 100
  rw [MedianOwner.segment_prob reps s
    (fun x => reps < 2 * Fintype.card {i : Fin reps // Good (x i)})]
  have h' := lt_of_le_of_lt hm (by simpa only [← Nat.card_eq_fintype_card] using h)
  exact h'

/-- Numerical correctness is local to actual outputs on word and the one
needed rational threshold. In applications word is the proved valid matrix
word. The comparator retains the full matrix/threshold frame, so its clock may
use polynomial time in the full table even for short numerical outputs. -/
theorem ActualEstimator.fixed_midpoint_strict_law (E : ActualEstimator)
    (word : List Bool) (D B k : ℕ) (u : ℝ) (_hu : 0 ≤ u)
    (hgap : 2 * u < (k : ℝ))
    (hcompare : E.actualComparison word (2 * B + k))
    (haccurate : 2 / 3 ≤ E.estimator.prob word
      (fun out => |E.value out - (D : ℝ)| ≤ u)) :
    (D ≤ B →
      99 / 100 < E.classifier.prob (natField (2 * B + k) ++ word) (· = [true])) ∧
    (B + k ≤ D →
      E.classifier.prob (natField (2 * B + k) ++ word) (· = [true]) < 1 / 100) := by
  have hmid : ((2 * B + k : ℕ) : ℝ) / 2 = (B : ℝ) + (k : ℝ) / 2 := by
    push_cast
    ring
  constructor
  · intro hD
    apply E.classifier_yes_votes
    refine haccurate.trans ?_
    apply FiniteLaw.prob_mono
    intro tape hgood
    change E.comparator.output (pair (natField (2 * B + k) ++ word)
      (E.estimator.output word (List.ofFn tape))) = true
    rw [hcompare tape]
    simp only [decide_eq_true_eq]
    rw [hmid]
    exact midpoint_yes_real _ u D B k hD hgood hgap
  · intro hD
    apply E.classifier_no_votes
    have hsub : ∀ tape : Fin (E.estimator.tapeLength word) → Bool,
        E.comparator.output (pair (natField (2 * B + k) ++ word)
          (E.estimator.output word (List.ofFn tape))) = true →
        ¬ |E.value (E.estimator.output word (List.ofFn tape)) - (D : ℝ)| ≤ u := by
      intro tape hbit hgood
      rw [hcompare tape] at hbit
      have hb : E.value (E.estimator.output word (List.ofFn tape)) <
          ((2 * B + k : ℕ) : ℝ) / 2 := of_decide_eq_true hbit
      rw [hmid] at hb
      have hc : ((B + k : ℕ) : ℝ) ≤ D := by exact_mod_cast hD
      push_cast at hc
      have ha := (abs_le.mp hgood).1
      linarith
    have hm := FiniteLaw.prob_mono
      (uniformTape (E.estimator.tapeLength word)) hsub
    rw [Paper2.Unit4Shell.Amplification.prob_not] at hm
    unfold SelectedTape.Algorithm.prob at haccurate ⊢
    linarith

theorem ActualEstimator.fixed_midpoint_law (E : ActualEstimator)
    (word : List Bool) (D B k : ℕ) (u : ℝ) (hu : 0 ≤ u)
    (hgap : 2 * u < (k : ℝ))
    (hcompare : E.actualComparison word (2 * B + k))
    (haccurate : 2 / 3 ≤ E.estimator.prob word
      (fun out => |E.value out - (D : ℝ)| ≤ u)) :
    (D ≤ B →
      99 / 100 ≤ E.classifier.prob (natField (2 * B + k) ++ word) (· = [true])) ∧
    (B + k ≤ D →
      E.classifier.prob (natField (2 * B + k) ++ word) (· = [true]) ≤ 1 / 100) := by
  have h := E.fixed_midpoint_strict_law word D B k u hu hgap hcompare haccurate
  exact ⟨fun hD => le_of_lt (h.1 hD), fun hD => le_of_lt (h.2 hD)⟩

#print axioms ActualEstimator.majority_poly
#print axioms ActualEstimator.header_vote_prob
#print axioms ActualEstimator.classifier_yes_votes
#print axioms ActualEstimator.classifier_no_votes
#print axioms ActualEstimator.fixed_midpoint_strict_law
#print axioms ActualEstimator.fixed_midpoint_law

end CurrentAdditive.V39ActualOutputMajority
