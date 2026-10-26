import CurrentAdditive.V39PermittedNumericalExtraction
import CurrentAdditive.V39FramedNumerical

/-! The deterministic estimator is given in its original deterministic
machine convention, with the literal matrix word as input. Comparison is
still only of its actual output with polynomial-length rational midpoints.
No randomized accuracy or zero-tape representation is imposed on it. -/

noncomputable section
open Classical

namespace CurrentAdditive.V39PermittedDeterministicExtraction

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.EncodedCommunication
open EthInapproximability.CurrentPaper.EncodedComplexity
open CurrentAdditive.V39RawRationalAdapter
open CurrentAdditive.V39PermittedNumericalExtraction
open CurrentAdditive.V39DomainClockTotalization
open CurrentAdditive.V39FramedNumerical
open CurrentAdditive.Eventual (entries)
open CurrentAdditive.ModelEndpointReview
open CurrentAdditive.ModelEndpointReview.RationalEndpoint

structure PermittedDeterministicEstimator where
  output : List Bool → List Bool
  value : List Bool → ℝ
  machine : BitMachine.Machine
  ce : ℕ
  de : ℕ
  estimator_clock : ∀ word, ValidTable word →
    machine.OutputsWithin word (output word) (ce * (entries word + 1) ^ de)
  compare : List Bool → Bool
  comparator_machine : BitMachine.Machine
  cc : ℕ → ℕ → ℕ
  dc : ℕ → ℕ → ℕ
  comparator_clock : ∀ c d word, ValidTable word → ∀ m : ℕ,
    (rationalCode (m : ℤ) 1).length ≤ c * (entries word + 1) ^ d →
    comparator_machine.OutputsWithin (rationalRequest m (output word))
      [compare (rationalRequest m (output word))]
      (cc c d * (entries word + 1) ^ dc c d)
  comparator_correct : ∀ c d word, ValidTable word → ∀ m : ℕ,
    (rationalCode (m : ℤ) 1).length ≤ c * (entries word + 1) ^ d →
    compare (rationalRequest m (output word)) =
      decide (value (output word) < (m : ℝ) / 2)

/-- Literal valid-domain deterministic extraction, including the physical
rational/output adapter and both timeout/default gates. It preserves every
valid output, including outputs outside the estimator's accuracy guarantee. -/
theorem extract_family (A : PermittedDeterministicEstimator) {ι : Type*}
    (word : ι → List Bool) (m : ι → ℕ) (c d : ℕ)
    (hvalid : ∀ x, ValidTable (word x))
    (hmid : ∀ x, (rationalCode (m x : ℤ) 1).length ≤
      c * (entries (word x) + 1) ^ d) :
    ∃ E : Estimator, E.value = A.value ∧
      (∀ word, ValidTable word → E.output word = A.output word) ∧
      (∀ x, ComparisonAt E (word x) (m x)) := by
  obtain ⟨total, hpoly, hpreserve⟩ := totalize_on_domain ValidTable A.output A.machine A.ce A.de
    (by
      intro word hv
      exact BitMachine.outputsWithin_mono A.machine (A.estimator_clock word hv)
        (Nat.mul_le_mul_left A.ce (Nat.pow_le_pow_left
          (Nat.add_le_add_right (table_entries_le_length word) 1) A.de)))
  let Domain := fun input => ∃ x, input = pair (natField (m x) ++ word x) (A.output (word x))
  obtain ⟨R, hR⟩ := compose_on_domain Domain A.compare A.comparator_machine
    (A.cc c d) (A.dc c d) (by
      intro input hi
      obtain ⟨x, rfl⟩ := hi
      rw [adapt_request]
      apply BitMachine.outputsWithin_mono _
        (A.comparator_clock c d (word x) (hvalid x) (m x) (hmid x))
      have hlength : entries (word x) ≤
          (pair (natField (m x) ++ word x) (A.output (word x))).length := by
        have hh := table_entries_le_length (word x)
        rw [pair_length, List.length_append]
        omega
      exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left
        (Nat.add_le_add_right hlength 1) _))
  let E : Estimator := {
    output := total
    physical := hpoly
    value := A.value
    comparator := R }
  refine ⟨E, rfl, hpreserve, ?_⟩
  intro x
  change R.output (pair (natField (m x) ++ word x) (total (word x))) =
    decide (A.value (total (word x)) < (m x : ℝ) / 2)
  rw [hpreserve (word x) (hvalid x)]
  rw [hR _ ⟨x, rfl⟩, adapt_request]
  exact A.comparator_correct c d (word x) (hvalid x) (m x) (hmid x)

/-- Public fixed-midpoint classification on the actual table family.
Only the source gap and estimator accuracy are needed after extraction;
the numerical-comparison premise is fully discharged. -/
theorem fixed_midpoint_outputs (A : PermittedDeterministicEstimator) {ι : Type*}
    (word : ι → List Bool) (D B k : ι → ℕ) (u : ι → ℝ) (c d : ℕ)
    (hvalid : ∀ x, ValidTable (word x))
    (hmid : ∀ x, (rationalCode (2 * B x + k x : ℤ) 1).length ≤
      c * (entries (word x) + 1) ^ d)
    (hacc : ∀ x, |A.value (A.output (word x)) - (D x : ℝ)| ≤ u x)
    (hgap : ∀ x, 2 * u x < (k x : ℝ)) :
    ∃ E : Estimator, E.value = A.value ∧
      (∀ word, ValidTable word → E.output word = A.output word) ∧
      ∀ x,
        (D x ≤ B x → E.run (natField (2 * B x + k x) ++ word x) = [true]) ∧
        (B x + k x ≤ D x → E.run (natField (2 * B x + k x) ++ word x) = [false]) := by
  obtain ⟨E, hv, ho, hc⟩ := extract_family A word (fun x => 2 * B x + k x) c d hvalid hmid
  refine ⟨E, hv, ho, fun x => ?_⟩
  apply midpoint_outputs E (word x) (D x) (B x) (k x) (u x) (hgap x)
    (by rw [hv, ho (word x) (hvalid x)]; exact hacc x) (hc x)

#print axioms extract_family
#print axioms fixed_midpoint_outputs

end CurrentAdditive.V39PermittedDeterministicExtraction
