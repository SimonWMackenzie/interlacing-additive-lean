import CurrentAdditive.V39RandomEstimatorNormalization
import CurrentAdditive.V39PermittedRequestBridge

/-! Source-neutral physical adapter.  The source routine receives only an
ordinary binary rational and an actual estimator output. Its clock is used
only there, and measured in the original table size. The adapter and its
stack-copy cost are charged before the retained-frame timeout is applied. -/

noncomputable section
open Classical

namespace CurrentAdditive.V39RawRationalAdapter

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.EncodedCommunication
open EthInapproximability.CurrentPaper.EncodedComplexity
open CurrentAdditive.ModelEndpointReview
open CurrentAdditive.ModelEndpointReview.RationalEndpoint
open CurrentAdditive.V39FramedComparator
open CurrentAdditive.V39ActualOutputMajority
open CurrentAdditive.V39RandomEstimatorNormalization
open CurrentAdditive.V39PermittedRequestBridge
open CurrentAdditive.V39FramedComparatorNormalization
open Paper2

def rationalRequest (m : ℕ) (out : List Bool) : List Bool :=
  pair (rationalCode (m : ℤ) 1) out

theorem adapt_request (word out : List Bool) (m : ℕ) :
    RationalCodeAdapter.adapt (pair (natField m ++ word) out) = rationalRequest m out := by
  rw [RationalCodeAdapter.adapt_header]
  simp only [rationalRequest, rationalCode_half]

/-- The overhead includes the literal finite transducer and both stack
reversals used by machine composition; no numerical semantics is used. -/
theorem compose_on_domain (Domain : List Bool → Prop)
    (answer : List Bool → Bool) (M : BitMachine.Machine) (c d : ℕ)
    (hrun : ∀ input, Domain input →
      M.OutputsWithin (RationalCodeAdapter.adapt input)
        [answer (RationalCodeAdapter.adapt input)] (c * (input.length + 1) ^ d)) :
    ∃ R : FramedComparator, ∀ input, Domain input →
      R.output input = answer (RationalCodeAdapter.adapt input) := by
  let K := 2 * RationalCodeAdapter.machine.pushBound * 5 + 9
  apply normalize_framed_comparator Domain (answer ∘ RationalCodeAdapter.adapt)
    (BitMachineComposition.composition RationalCodeAdapter.machine M) (K + c) (d + 1)
  intro input hi
  have ha := RationalCodeAdapter.outputs input
  have hb := BitMachineComposition.composition_outputsWithin
    RationalCodeAdapter.machine M ha (hrun input hi)
  apply BitMachine.outputsWithin_mono _ hb
  have hl := BitMachine.output_length_bound RationalCodeAdapter.machine ha
  have hN : 1 ≤ input.length + 1 := by omega
  have hp : input.length + 1 ≤ (input.length + 1) ^ (d + 1) := by
    calc _ = (input.length + 1) ^ 1 := (pow_one _).symm
         _ ≤ _ := Nat.pow_le_pow_right hN (by omega)
  have hd : (input.length + 1) ^ d ≤ (input.length + 1) ^ (d + 1) :=
    Nat.pow_le_pow_right hN (by omega)
  have hm := Nat.mul_le_mul_left c hd
  have hK := Nat.mul_le_mul_left K hp
  dsimp [K] at *
  nlinarith

/-- Exactly the actual tape outputs on the supplied valid table family are
requested. The raw comparator is never required to compare outputs with
one another, nor to be correct or fast on malformed or unreachable inputs. -/
theorem comparator_of_rational_requests {ι : Type*}
    (S : SelectedTape.Algorithm) (value : List Bool → ℝ)
    (word : ι → List Bool) (m T : ι → ℕ)
    (hsize : ∀ x, T x ≤ (word x).length)
    (answer : List Bool → Bool) (M : BitMachine.Machine) (c d : ℕ)
    (hrun : ∀ x (tape : Fin (S.tapeLength (word x)) → Bool),
      M.OutputsWithin (rationalRequest (m x) (S.output (word x) (List.ofFn tape)))
        [answer (rationalRequest (m x) (S.output (word x) (List.ofFn tape)))]
        (c * (T x + 1) ^ d))
    (hcorrect : ∀ x (tape : Fin (S.tapeLength (word x)) → Bool),
      answer (rationalRequest (m x) (S.output (word x) (List.ofFn tape))) =
        decide (value (S.output (word x) (List.ofFn tape)) < (m x : ℝ) / 2)) :
    ∃ R : FramedComparator, ∀ x,
      ({ estimator := S, value := value, comparator := R } : ActualEstimator).actualComparison
        (word x) (m x) := by
  obtain ⟨R, hR⟩ := compose_on_domain (Requested S word m) answer M c d (by
    intro input hi
    obtain ⟨x, tape, rfl⟩ := hi
    rw [requestFrame, adapt_request]
    exact BitMachine.outputsWithin_mono M (hrun x tape)
      (Nat.mul_le_mul_left c (Nat.pow_le_pow_left
        (Nat.add_le_add_right (table_le_request_length S (word x) (m x)
          (T x) (hsize x) tape) 1) d)))
  refine ⟨R, ?_⟩
  intro x tape
  change R.output (requestFrame S (word x) (m x) tape) = _
  rw [hR _ ⟨x, tape, rfl⟩]
  simpa only [requestFrame, adapt_request] using hcorrect x tape

/-- End-to-end extraction from the two literal raw machines. All valid
outputs and complete event laws are preserved, using the original random
tape length. Comparator normalization takes place only after projection. -/
theorem actualEstimator_of_raw_rational_requests {ι : Type*}
    (A : RawEstimator) (value : List Bool → ℝ)
    (word : ι → List Bool) (m T : ι → ℕ)
    (hsize : ∀ x, T x ≤ (word x).length) (ce de : ℕ)
    (hest : ∀ x (tape : Fin (A.tapeLength (word x)) → Bool),
      A.machine.OutputsWithin (pair (word x) (List.ofFn tape))
        (A.output (word x) (List.ofFn tape)) (ce * (T x + 1) ^ de))
    (answer : List Bool → Bool) (M : BitMachine.Machine) (cc dc : ℕ)
    (hcmp : ∀ x (tape : Fin (A.tapeLength (word x)) → Bool),
      M.OutputsWithin (rationalRequest (m x) (A.output (word x) (List.ofFn tape)))
        [answer (rationalRequest (m x) (A.output (word x) (List.ofFn tape)))]
        (cc * (T x + 1) ^ dc))
    (hcorrect : ∀ x (tape : Fin (A.tapeLength (word x)) → Bool),
      answer (rationalRequest (m x) (A.output (word x) (List.ofFn tape))) =
        decide (value (A.output (word x) (List.ofFn tape)) < (m x : ℝ) / 2)) :
    ∃ R : FramedComparator,
      (∀ x, ({ estimator := A.normalize ce de, value := value, comparator := R } :
        ActualEstimator).actualComparison (word x) (m x)) ∧
      (∀ x (P : List Bool → Prop),
        (A.normalize ce de).prob (word x) P = A.prob (word x) P) := by
  let S := A.normalize ce de
  have heq : ∀ x (tape : Fin (S.tapeLength (word x)) → Bool),
      S.output (word x) (List.ofFn tape) = A.output (word x) (List.ofFn tape) := by
    intro x tape
    exact A.normalize_output_valid ce de (word x) (T x) (hsize x) tape (hest x tape)
  obtain ⟨R, hR⟩ := comparator_of_rational_requests S value word m T hsize answer M cc dc
    (by intro x tape; simpa only [heq x tape] using hcmp x tape)
    (by intro x tape; simpa only [heq x tape] using hcorrect x tape)
  refine ⟨R, hR, ?_⟩
  intro x P
  exact A.normalize_prob_valid ce de (word x) (T x) (hsize x) (hest x) P

#print axioms adapt_request
#print axioms compose_on_domain
#print axioms comparator_of_rational_requests
#print axioms actualEstimator_of_raw_rational_requests

end CurrentAdditive.V39RawRationalAdapter
