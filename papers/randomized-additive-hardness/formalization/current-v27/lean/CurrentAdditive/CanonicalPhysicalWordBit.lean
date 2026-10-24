import CurrentAdditive.CanonicalPhysicalPayloadIndex
import EthInapproximability.CurrentPaper.MatrixTableLookup

namespace CurrentAdditive.FiniteFieldConstructor.CanonicalTable

open CurrentAdditive.FiniteFieldConstructor
open EthInapproximability.CurrentPaper

theorem printed_word_get (d modulus n x y : ℕ) (j : Fin n) :
    (BitPrinter.word d modulus n x y)[j.val]?.getD false =
      BitPrinter.bit d modulus x y j.val := by
  simp [BitPrinter.word, j.isLt]

/-- The inherited physical table lookup reads the selected bit of a
normal-order finite-field word, preserving the entire word and unary
coordinate. The field-word generator itself is a separate physical stage. -/
theorem physical_printed_word_bit (d modulus n x y : ℕ)
    (j : Fin n) (out : List Bool) :
    ∃ steps ≤ 32 * (n + j.val + n + 1) ^ 2,
      MatrixTableLookup.run steps
        (MatrixTableLookup.cfg (some MatrixTableLookup.start)
          MatrixTableLookup.initial [] (List.replicate n true)
          (List.replicate j.val true) []
          (BitPrinter.word d modulus n x y) out) =
      MatrixTableLookup.cfg none MatrixTableLookup.initial []
        (List.replicate n true) (List.replicate j.val true) []
        (BitPrinter.word d modulus n x y)
        (BitPrinter.bit d modulus x y j.val :: out) := by
  obtain ⟨steps, hsteps, hrun⟩ := MatrixTableLookup.lookup_run
    0 n j.val (BitPrinter.word d modulus n x y) out
  refine ⟨steps, ?_, ?_⟩
  · simpa [BitPrinter.word_length] using hsteps
  · simpa only [Nat.zero_mul, Nat.zero_add, List.replicate_zero,
      printed_word_get] using hrun

#print axioms printed_word_get
#print axioms physical_printed_word_bit

end CurrentAdditive.FiniteFieldConstructor.CanonicalTable
