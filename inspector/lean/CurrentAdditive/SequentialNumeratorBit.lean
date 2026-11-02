import CurrentAdditive.SequentialBitBound

set_option maxHeartbeats 1000000

namespace CurrentAdditive.RationalCandidateCompletion

open CurrentAdditive.SequentialCode
open CurrentAdditive.SequentialSourceCode
open CurrentAdditive.SequentialAppendMoments
open CurrentAdditive.SequentialFiniteLaw
open CurrentAdditive.RationalBitBounds

/-- For a positive, normalized input alphabet, the actual sequential output
is also a positive, normalized rational law. Hence the integer numerator in
any shared-denominator representation fits the denominator's bit budget. -/
theorem sequentialMaterialized_numerator_bits {Y : Type*}
    [DecidableEq Y] (D : Nat) (alphabet : Array (Y × ℚ))
    (halphabetPositive : SourcePositive alphabet)
    (halphabetMass : sourceMass alphabet = 1)
    (ea : CommonDenominator
      (fun j : Fin alphabet.size => alphabet[j].2))
    (q : Nat) (out : Array ((Fin q → Y) × ℚ))
    (hrun : sequentialMaterialized D alphabet q = some out) :
    ∃ enc : CommonDenominator (fun i : Fin out.size => out[i].2),
      Nat.size enc.denominator ≤
        q * Nat.size ea.denominator +
        4 * q * alphabet.size *
          (generatedFeatures q D (alphabet.map Prod.fst)).size ^ 2 *
          Nat.size ((generatedFeatures q D (alphabet.map Prod.fst)).size + 1) + 1 ∧
      ∀ i : Fin out.size,
        Nat.size (enc.numerator i).natAbs ≤ Nat.size enc.denominator := by
  obtain ⟨enc, hbits⟩ :=
    sequentialMaterialized_denominator_bits D alphabet ea q out hrun
  obtain ⟨out', hout', hpos'⟩ :=
    sequentialMaterialized_total D alphabet halphabetPositive q
  rw [hrun] at hout'
  have hpos : SourcePositive out := by
    cases Option.some.inj hout'
    exact hpos'
  have hmass : sourceMass out = 1 :=
    sequentialMaterialized_mass D alphabet halphabetMass q out hrun
  refine ⟨enc, hbits, ?_⟩
  intro i
  have hpositive : ∀ j : Fin out.size, 0 ≤ out[j].2 := by
    intro j
    have hj := (Array.all_eq_true.mp hpos) j.val j.isLt
    have hj' : 0 < out[j].2 := by
      simpa [SourcePositive] using hj
    exact le_of_lt hj'
  have hle : out[i].2 ≤ 1 := by
    have hsingle := Finset.single_le_sum
      (s := Finset.univ) (f := fun j : Fin out.size => out[j].2)
      (by intro j hj; exact hpositive j) (Finset.mem_univ i)
    rw [sourceMass_eq_sum_fin] at hmass
    have hsingle' : out[i].2 ≤
        ∑ j : Fin out.size, out[j].2 := by simpa using hsingle
    exact hsingle'.trans_eq hmass
  exact numerator_bits_le_denominator enc i (hpositive i) hle

#print axioms sequentialMaterialized_numerator_bits

end CurrentAdditive.RationalCandidateCompletion
