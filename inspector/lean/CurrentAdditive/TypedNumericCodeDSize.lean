import CurrentAdditive.TypedNumericCodeDJoin
import CurrentAdditive.DeterministicCodeDNumericOutputSize

/-! The existing serialized output-size theorem is applied to the exact
first-position numeric relabelling of the typed source, rather than to an
unrelated numeric alphabet. -/

namespace CurrentAdditive.TypedNumericCodeDJoin

open Paper2
open CurrentAdditive.ExecutableCodeSource
open CurrentAdditive.OrderedAlphabetCodec
open CurrentAdditive.InjectiveCodeDTransport
open CurrentAdditive.DeterministicCodeDNumericOutputSize
open CurrentAdditive.DeterministicCodeDActualSourceSize
open CurrentAdditive.SequentialCode
open CurrentAdditive.SequentialSourceCode
open CurrentAdditive.CodeDCanonicalSourceV2

variable {Y : Type} [Fintype Y] [DecidableEq Y]

theorem typed_numeric_serialized_size (D q : Nat)
    (μ : PositiveRationalLaw Y) (table : AlphabetTable Y μ) :
    (encodedSource
      (mapSource (encode μ table)
        (CurrentAdditive.IndexedExecutableStep.codeDArray D q μ table))).length ≤
      3 * (generatedFeatures q D
          ((numericEntries μ table).map Prod.fst)).size *
        (6 * q * (table.entries.size + 1) +
          8 * outputWeightBits D (numericEntries μ table) q + 15) + 1 := by
  obtain ⟨bytes, hbytes, hsize⟩ :=
    numericTargetBytes_total_bounded μ table D q
  rw [numeric_target_exact] at hbytes
  cases hbytes
  exact hsize

#print axioms typed_numeric_serialized_size

end CurrentAdditive.TypedNumericCodeDJoin
