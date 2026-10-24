import CurrentAdditive.DeterministicOrderedAlphabetSize
import CurrentAdditive.DeterministicSequentialLabelSupport
import Mathlib.Tactic

/-!
The actual ordered numeric Code D alphabet fixes the bit width of every
generated coordinate. Combined with the already checked sequential rational
bit budget, this gives a fully explicit bound for the exact V2 output bytes.
-/

namespace CurrentAdditive.DeterministicCodeDNumericOutputSize

open Paper2 CurrentAdditive.ExecutableCodeSource
open CurrentAdditive.OrderedAlphabetCodec
open CurrentAdditive.DeterministicOrderedAlphabetSize
open CurrentAdditive.DeterministicSequentialLabelSupport
open CurrentAdditive.DeterministicCodeDActualSourceSize
open CurrentAdditive.SequentialSourceCode

theorem numericOutput_code_bits {Y : Type} [Fintype Y] [DecidableEq Y]
    (μ : PositiveRationalLaw Y) (table : AlphabetTable Y μ)
    (D q : Nat) (out : Array ((Fin q → Nat) × ℚ))
    (hrun : sequentialMaterialized D (numericEntries μ table) q = some out) :
    ∀ entry ∈ out.toList, ∀ j : Fin q,
      (entry.1 j).bits.length ≤ table.entries.size := by
  have hlabels := sequentialMaterialized_labels D (numericEntries μ table)
    table.entries.size (numericEntries_codes_lt μ table) q out hrun
  intro entry he j
  have hlt := hlabels entry he j
  simpa only [Nat.size_eq_bits_len] using
    (Nat.size_le.mpr (lt_trans hlt Nat.lt_two_pow_self))

theorem numericSequential_encodedSource_length_le {Y : Type}
    [Fintype Y] [DecidableEq Y]
    (μ : PositiveRationalLaw Y) (table : AlphabetTable Y μ)
    (D q : Nat) (out : Array ((Fin q → Nat) × ℚ))
    (hrun : sequentialMaterialized D (numericEntries μ table) q = some out) :
    (CodeDCanonicalSourceV2.encodedSource out).length ≤
      3 * (SequentialCode.generatedFeatures q D
          ((numericEntries μ table).map Prod.fst)).size *
        (6 * q * (table.entries.size + 1) +
          8 * outputWeightBits D (numericEntries μ table) q + 15) + 1 := by
  exact actualSequentialEncodedSource_length_le D (numericEntries μ table)
    (numericEntries_positive μ table) (numericEntries_mass μ table)
    q out hrun table.entries.size (numericOutput_code_bits μ table D q out hrun)

theorem numericTargetBytes_total_bounded {Y : Type}
    [Fintype Y] [DecidableEq Y]
    (μ : PositiveRationalLaw Y) (table : AlphabetTable Y μ)
    (D q : Nat) :
    ∃ bytes,
      CodeDTargetV2.targetBytes D (numericEntries μ table) q = some bytes ∧
      bytes.length ≤
        3 * (SequentialCode.generatedFeatures q D
            ((numericEntries μ table).map Prod.fst)).size *
          (6 * q * (table.entries.size + 1) +
            8 * outputWeightBits D (numericEntries μ table) q + 15) + 1 := by
  obtain ⟨out, hrun, _⟩ := sequentialMaterialized_total D
    (numericEntries μ table) (numericEntries_positive μ table) q
  refine ⟨CodeDCanonicalSourceV2.encodedSource out, ?_, ?_⟩
  · simp [CodeDTargetV2.targetBytes, hrun]
  · exact numericSequential_encodedSource_length_le μ table D q out hrun

#print axioms numericSequential_encodedSource_length_le
#print axioms numericTargetBytes_total_bounded

end CurrentAdditive.DeterministicCodeDNumericOutputSize
