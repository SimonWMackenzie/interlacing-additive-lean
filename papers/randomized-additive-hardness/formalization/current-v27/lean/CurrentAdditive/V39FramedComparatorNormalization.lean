import CurrentAdditive.V39FramedComparator
import CurrentAdditive.V39DomainClockTotalization

/-! Generic normalization for every permitted comparator, deterministic or
randomized. The requested domain can include actual outputs on all selected
tapes. No numerical semantics, accuracy, or deterministic estimator is used. -/

noncomputable section
open Classical

namespace CurrentAdditive.V39FramedComparatorNormalization

open EthInapproximability.CurrentPaper
open CurrentAdditive.V39FramedComparator
open CurrentAdditive.V39DomainClockTotalization

/-- A source comparison routine need only halt polynomially on its requested
valid domain. Charged fixed timeout and default-bit conversion construct the
physically total framed comparator, preserving every requested answer. -/
theorem normalize_framed_comparator
    (Requested : List Bool → Prop) (answer : List Bool → Bool)
    (M : BitMachine.Machine) (c d : ℕ)
    (hvalid : ∀ input, Requested input →
      M.OutputsWithin input [answer input] (c*(input.length+1)^d)) :
    ∃ R : FramedComparator,
      ∀ input, Requested input → R.output input = answer input := by
  obtain ⟨total, hpoly, hpreserve⟩ := totalize_boolean_on_domain
    Requested answer M c d hvalid
  exact ⟨{ output := total, physical := hpoly }, hpreserve⟩

/-- Source clocks may be stated directly in table entry count T. The full
comparison frame must contain at least T bits; then the timeout is a
polynomial in frame length, and no short numerical-representation clock is
required. This theorem is independent of any estimator's tape or output law. -/
theorem normalize_framed_comparator_of_table_clock
    (Requested : List Bool → Prop) (tableSize : List Bool → ℕ)
    (answer : List Bool → Bool) (M : BitMachine.Machine) (c d : ℕ)
    (hsize : ∀ input, Requested input → tableSize input ≤ input.length)
    (hvalid : ∀ input, Requested input →
      M.OutputsWithin input [answer input] (c*(tableSize input+1)^d)) :
    ∃ R : FramedComparator,
      ∀ input, Requested input → R.output input = answer input := by
  apply normalize_framed_comparator Requested answer M c d
  intro input hi
  exact BitMachine.outputsWithin_mono M (hvalid input hi)
    (Nat.mul_le_mul_left c (Nat.pow_le_pow_left
      (Nat.add_le_add_right (hsize input hi) 1) d))

#print axioms normalize_framed_comparator
#print axioms normalize_framed_comparator_of_table_clock

end CurrentAdditive.V39FramedComparatorNormalization
