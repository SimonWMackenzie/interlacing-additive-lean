import CurrentAdditive.SequentialNumeratorBit

set_option maxHeartbeats 1000000

namespace CurrentAdditive.RationalCandidateCompletion

open CurrentAdditive.SequentialCode
open CurrentAdditive.SequentialSourceCode
open CurrentAdditive.RationalBitBounds

/-- A positive normalized rational alphabet has an actually constructed
sequential source. Its support is no larger than the final feature count,
and each final rational weight has numerator and denominator within the
explicit input-length and support-reduction bit budget. -/
theorem sequentialMaterialized_complete_bits {Y : Type*}
    [DecidableEq Y] (D : Nat) (alphabet : Array (Y × ℚ))
    (halphabetPositive : SourcePositive alphabet)
    (halphabetMass : sourceMass alphabet = 1) (q : Nat) :
    ∃ out : Array ((Fin q → Y) × ℚ),
      ∃ enc : CommonDenominator (fun i : Fin out.size => out[i].2),
        sequentialMaterialized D alphabet q = some out ∧
        out.size ≤ (generatedFeatures q D (alphabet.map Prod.fst)).size ∧
        Nat.size enc.denominator ≤
          q * ((∑ j : Fin alphabet.size,
              Nat.size (alphabet[j].2).den) + 1) +
          4 * q * alphabet.size *
            (generatedFeatures q D (alphabet.map Prod.fst)).size ^ 2 *
            Nat.size ((generatedFeatures q D (alphabet.map Prod.fst)).size + 1) + 1 ∧
        ∀ i : Fin out.size,
          Nat.size (enc.numerator i).natAbs ≤ Nat.size enc.denominator := by
  obtain ⟨out, hrun, _, hsupport⟩ :=
    sequentialMaterialized_exists_bounded D alphabet halphabetPositive q
  let ea := inputLawCommonDenominator
    (fun j : Fin alphabet.size => alphabet[j].2)
  obtain ⟨enc, hbits, hnumbits⟩ :=
    sequentialMaterialized_numerator_bits D alphabet
      halphabetPositive halphabetMass ea q out hrun
  have hinput : Nat.size ea.denominator ≤
      (∑ j : Fin alphabet.size, Nat.size (alphabet[j].2).den) + 1 := by
    exact inputLaw_denominator_bits _
  refine ⟨out, enc, hrun, hsupport, ?_, hnumbits⟩
  have hscaled := Nat.mul_le_mul_left q hinput
  omega

#print axioms sequentialMaterialized_complete_bits

end CurrentAdditive.RationalCandidateCompletion
