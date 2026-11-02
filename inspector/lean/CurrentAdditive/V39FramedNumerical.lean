import CurrentAdditive.V39FramedComparator
import CurrentAdditive.SmallBiasZeroTapePhysical

/-!
Selected v39 `def:table-estimation`: the comparator is physically total,
but numerical correctness is needed only on actual estimator outputs.
No value, decoder, or correctness condition is imposed on unreachable words.
The existing physical 147-run program is reused; deterministic calls have
identical output and so give exactly the single comparison bit.
-/

noncomputable section
open Classical

namespace CurrentAdditive.V39FramedNumerical

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.EncodedCommunication
open EthInapproximability.CurrentPaper.EncodedComplexity (pair)
open CurrentAdditive.SmallBias
open CurrentAdditive.V39FramedComparator
open CurrentAdditive.ModelEndpointReview.RationalEndpoint
open Paper2
open Paper2.Unit4Shell.Amplification (reps)

/-- Only physical data and the numerical meaning of actual output words.
The record contains no accuracy or numerical-comparison correctness premise. -/
structure Estimator where
  output : List Bool → List Bool
  physical : BitMachine.Polytime output
  value : List Bool → ℝ
  comparator : FramedComparator

/-- Correct comparison at one actual estimator input. This never asks for
correctness on unreachable output words or on another estimator input. -/
def ComparisonAt (E : Estimator) (word : List Bool) (m : ℕ) : Prop :=
  E.comparator.output
    (pair (natField m ++ word) (E.output word)) =
      decide (E.value (E.output word) < (m:ℝ)/2)

private def Estimator.header (E : Estimator) : AModel.PrefixAlgorithm :=
  (HeaderStrip.selectedEstimator (selectedDetEstimator E.output E.physical)).toPrefix

private theorem Estimator.headerPoly (E : Estimator) : E.header.Polynomial :=
  HeaderStrip.selectedEstimator_toPrefix_polynomial _

private def Estimator.majority (E : Estimator) : AModel.PrefixAlgorithm :=
  medAlgJudge E.header (comparisonMachine E.comparator) E.comparator.judge
    (compareClock E.header E.headerPoly E.comparator)
    (comparisonSpec E.header E.headerPoly E.comparator)

private theorem Estimator.majorityPoly (E : Estimator) : E.majority.Polynomial :=
  medAlgJudge_polynomial _ _ _ _
    (comparisonSpec E.header E.headerPoly E.comparator) E.headerPoly
    (compareClock_poly E.header E.headerPoly E.comparator)

private theorem Estimator.majorityTape (E : Estimator) (n : ℕ) :
    E.majority.tapeLength n = 0 := by
  simp [Estimator.majority, medAlgJudge, Estimator.header,
    SelectedTape.Algorithm.toPrefix, HeaderStrip.selectedEstimator,
    SelectedTape.pullback, selectedDetEstimator]

private theorem Estimator.tapeShape (E : Estimator) :
    ∃ c d : ℕ, ∀ n, E.majority.tapeLength n = c*(n+1)^d :=
  ⟨0, 0, by intro n; simp [E.majorityTape n]⟩

def Estimator.classifier (E : Estimator) : SelectedTape.Algorithm :=
  SelectedTape.Algorithm.ofPrefixMonomial E.majority E.majorityPoly E.tapeShape

private theorem prefix_tape (A : AModel.PrefixAlgorithm) (hp : A.Polynomial)
    (hR : ∃ c d : ℕ, ∀ n, A.tapeLength n = c*(n+1)^d) (x : List Bool) :
    (SelectedTape.Algorithm.ofPrefixMonomial A hp hR).tapeLength x =
      A.tapeLength x.length := by
  change Classical.choose hR*(x.length+1)^
    Classical.choose (Classical.choose_spec hR) = _
  exact (Classical.choose_spec (Classical.choose_spec hR) x.length).symm

theorem classifier_tape_zero (E : Estimator) (x : List Bool) :
    E.classifier.tapeLength x = 0 := by
  change (SelectedTape.Algorithm.ofPrefixMonomial _ _ _).tapeLength x = 0
  rw [prefix_tape, E.majorityTape]

def Estimator.run (E : Estimator) (x : List Bool) : List Bool :=
  E.classifier.output x []

theorem run_singleton (E : Estimator) (x : List Bool) : ∃ b, E.run x = [b] := by
  unfold Estimator.run Estimator.classifier SelectedTape.Algorithm.ofPrefixMonomial
    Estimator.majority medAlgJudge medOutputJudge
  exact ⟨_, rfl⟩

theorem run_polytime (E : Estimator) : BitMachine.Polytime E.run :=
  zeroTapeOutputPolytime E.classifier (classifier_tape_zero E)

def Estimator.machine (E : Estimator) : BitMachine.Machine :=
  Classical.choose (run_polytime E)

def Estimator.clockCoefficient (E : Estimator) : ℕ :=
  Classical.choose (Classical.choose_spec (run_polytime E))

def Estimator.clockDegree (E : Estimator) : ℕ :=
  Classical.choose (Classical.choose_spec (Classical.choose_spec (run_polytime E)))

/-- A fixed actual machine and fixed polynomial clock on all input words.
Neither numerical accuracy nor semantic comparison correctness is used. -/
theorem machine_outputs (E : Estimator) (x : List Bool) :
    E.machine.OutputsWithin x (E.run x)
      (E.clockCoefficient*(x.length+1)^E.clockDegree) :=
  Classical.choose_spec (Classical.choose_spec
    (Classical.choose_spec (run_polytime E))) x

private theorem header_output (E : Estimator) (m : ℕ)
    (word tape : List Bool) :
    E.header.output (natField m ++ word) tape = E.output word := by
  change (HeaderStrip.selectedEstimator
    (selectedDetEstimator E.output E.physical)).output (natField m ++ word) tape = E.output word
  rw [HeaderStrip.selectedEstimator_output, selectedDetEstimator_output]

/-- The physical reused deterministic repetition program gives exactly the
comparator's bit on the actual estimator output. No numerical semantics or
unreachable-output correctness is used to establish this identity. -/
theorem run_on_header (E : Estimator) (m : ℕ) (word : List Bool) :
    E.run (natField m ++ word) =
      [E.comparator.output (pair (natField m ++ word) (E.output word))] := by
  unfold Estimator.run Estimator.classifier SelectedTape.Algorithm.ofPrefixMonomial
    Estimator.majority medAlgJudge medOutputJudge
  simp_rw [header_output]
  change [decide (reps < 2*Fintype.card {i : Fin reps //
    E.comparator.output (pair (natField m ++ word) (E.output word)) = true})] = _
  cases hb : E.comparator.output (pair (natField m ++ word) (E.output word)) <;>
    norm_num [hb, reps]

/-- Only comparison correctness at the actual estimator input is consumed.
For encoded-table endpoints this is supplied only when that word decodes to
a valid finite total nonempty table. -/
theorem midpoint_outputs (E : Estimator) (word : List Bool) (D B k : ℕ)
    (u : ℝ) (hgap : 2*u < (k:ℝ))
    (hacc : |E.value (E.output word)-(D:ℝ)| ≤ u)
    (hcompare : ComparisonAt E word (2*B+k)) :
    (D ≤ B → E.run (natField (2*B+k) ++ word) = [true]) ∧
    (B+k ≤ D → E.run (natField (2*B+k) ++ word) = [false]) := by
  have hmid : ((2*B+k:ℕ):ℝ)/2 = (B:ℝ)+(k:ℝ)/2 := by
    push_cast
    ring
  have hout := run_on_header E (2*B+k) word
  rw [hcompare, hmid] at hout
  have he := abs_le.mp hacc
  constructor
  · intro hD
    have hDR : (D:ℝ) ≤ B := by exact_mod_cast hD
    have hlt : E.value (E.output word) < (B:ℝ)+(k:ℝ)/2 := by nlinarith
    simpa only [hlt, decide_true] using hout
  · intro hD
    have hDR : (B:ℝ)+(k:ℝ) ≤ D := by exact_mod_cast hD
    have hnot : ¬E.value (E.output word) < (B:ℝ)+(k:ℝ)/2 := by
      have hlt : (B:ℝ)+(k:ℝ)/2 < E.value (E.output word) := by nlinarith
      exact not_lt_of_ge hlt.le
    simpa only [hnot, decide_false] using hout

#print axioms classifier_tape_zero
#print axioms run_polytime
#print axioms machine_outputs
#print axioms run_on_header
#print axioms midpoint_outputs

end CurrentAdditive.V39FramedNumerical
