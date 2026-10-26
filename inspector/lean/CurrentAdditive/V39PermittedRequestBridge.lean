import CurrentAdditive.V39ActualOutputMajority
import CurrentAdditive.V39FramedComparatorNormalization

/-!
Construct the normalized physical comparator from exactly the requested
midpoint/table/actual-output frames. The source machine clock is polynomial
in table entry count and is required only on this image. Its numerical law
is also required only on this image, including inaccurate estimator tapes.
No algorithm tests membership in the request image.
-/

noncomputable section
open Classical

namespace CurrentAdditive.V39PermittedRequestBridge

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.EncodedCommunication
open EthInapproximability.CurrentPaper.EncodedComplexity
open CurrentAdditive.V39FramedComparator
open CurrentAdditive.V39ActualOutputMajority
open CurrentAdditive.V39FramedComparatorNormalization
open Paper2

def requestFrame (S : SelectedTape.Algorithm) (word : List Bool) (m : ℕ)
    (tape : Fin (S.tapeLength word) → Bool) : List Bool :=
  pair (natField m ++ word) (S.output word (List.ofFn tape))

/-- An arbitrary selected family of valid table words and fixed rational
midpoints. Only the actual outputs of those words enter the domain. -/
def Requested {ι : Type*} (S : SelectedTape.Algorithm)
    (word : ι → List Bool) (m : ι → ℕ) (input : List Bool) : Prop :=
  ∃ x : ι, ∃ tape : Fin (S.tapeLength (word x)) → Bool,
    input = requestFrame S (word x) (m x) tape

/-- The original table remains in the comparison frame, including when the
estimator's numerical output happens to be very short. -/
theorem table_le_request_length (S : SelectedTape.Algorithm) (word : List Bool)
    (m T : ℕ) (hsize : T ≤ word.length)
    (tape : Fin (S.tapeLength word) → Bool) :
    T ≤ (requestFrame S word m tape).length := by
  unfold requestFrame
  rw [pair_length, List.length_append]
  omega

/-- The paper's table-size clock on requested comparisons suffices to build
the physically total comparator used by the existing majority machine.
There is no clock or numerical correctness hypothesis outside those requests.
The midpoint can vary with the selected word; no universal rational comparison
algorithm or arbitrary output-to-output comparison is assumed. -/
theorem comparator_of_requested_table_clock {ι : Type*}
    (S : SelectedTape.Algorithm) (value : List Bool → ℝ)
    (word : ι → List Bool) (m T : ι → ℕ)
    (hsize : ∀ x, T x ≤ (word x).length)
    (answer : List Bool → Bool) (M : BitMachine.Machine) (c d : ℕ)
    (hclock : ∀ x (tape : Fin (S.tapeLength (word x)) → Bool),
      M.OutputsWithin (requestFrame S (word x) (m x) tape)
        [answer (requestFrame S (word x) (m x) tape)] (c * (T x + 1) ^ d))
    (hcorrect : ∀ x (tape : Fin (S.tapeLength (word x)) → Bool),
      answer (requestFrame S (word x) (m x) tape) =
        decide (value (S.output (word x) (List.ofFn tape)) < (m x : ℝ) / 2)) :
    ∃ R : FramedComparator, ∀ x,
      ({ estimator := S, value := value, comparator := R } : ActualEstimator).actualComparison
        (word x) (m x) := by
  obtain ⟨R, hR⟩ := normalize_framed_comparator
    (Requested S word m) answer M c d (by
      intro input hinput
      rcases hinput with ⟨x, tape, rfl⟩
      exact BitMachine.outputsWithin_mono M (hclock x tape)
        (Nat.mul_le_mul_left c (Nat.pow_le_pow_left
          (Nat.add_le_add_right (table_le_request_length S (word x) (m x)
            (T x) (hsize x) tape) 1) d)))
  refine ⟨R, ?_⟩
  intro x tape
  change R.output (requestFrame S (word x) (m x) tape) = _
  rw [hR _ ⟨x, tape, rfl⟩]
  exact hcorrect x tape

#print axioms table_le_request_length
#print axioms comparator_of_requested_table_clock

end CurrentAdditive.V39PermittedRequestBridge
