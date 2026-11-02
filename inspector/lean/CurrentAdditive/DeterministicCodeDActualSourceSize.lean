import CurrentAdditive.DeterministicCodeDSerializedSize
import CurrentAdditive.SequentialCompleteBit
import CurrentAdditive.CramerMinorBound
import Mathlib.Tactic

/-!
The actual sequential Code D source has a concrete encoded-byte bound once
its alphabet codes have a bit bound. The rational-weight budget and support
bound come from the checked sequential construction, rather than a new
resource certificate.
-/

namespace CurrentAdditive.DeterministicCodeDActualSourceSize

open CurrentAdditive.SequentialCode
open CurrentAdditive.SequentialSourceCode
open CurrentAdditive.RationalBitBounds
open CurrentAdditive.DeterministicCodeDSerializedSize

theorem canonical_bits_of_common {κ : Type*} {w : κ → ℚ}
    (enc : CommonDenominator w) (i : κ) (B : Nat)
    (hb : Nat.size enc.denominator ≤ B)
    (hn : Nat.size (enc.numerator i).natAbs ≤ B) :
    Nat.size (w i).num.natAbs ≤ B ∧ Nat.size (w i).den ≤ B := by
  have hcomponents := rat_components_le_of_divInt (w i)
    (enc.numerator i) (enc.denominator : ℤ)
    (by exact_mod_cast (Nat.ne_of_gt enc.positive)) (enc.represents i)
  constructor
  · exact (Nat.size_le_size hcomponents.1).trans hn
  · have hd : (enc.denominator : ℤ).natAbs = enc.denominator := by simp
    rw [hd] at hcomponents
    exact (Nat.size_le_size hcomponents.2).trans hb

def outputWeightBits (D : Nat) (alphabet : Array (Nat × ℚ)) (q : Nat) : Nat :=
  q * ((∑ j : Fin alphabet.size, Nat.size (alphabet[j].2).den) + 1) +
    4 * q * alphabet.size *
      (generatedFeatures q D (alphabet.map Prod.fst)).size ^ 2 *
      Nat.size ((generatedFeatures q D (alphabet.map Prod.fst)).size + 1) + 1

theorem actualSequentialEncodedSource_length_le (D : Nat)
    (alphabet : Array (Nat × ℚ))
    (halphabetPositive : SourcePositive alphabet)
    (halphabetMass : sourceMass alphabet = 1)
    (q : Nat) (out : Array ((Fin q → Nat) × ℚ))
    (hrun : sequentialMaterialized D alphabet q = some out)
    (U : Nat)
    (hcode : ∀ entry ∈ out.toList,
      ∀ j : Fin q, (entry.1 j).bits.length ≤ U) :
    (CodeDCanonicalSourceV2.encodedSource out).length ≤
      3 * (generatedFeatures q D (alphabet.map Prod.fst)).size *
        (6 * q * (U + 1) + 8 * outputWeightBits D alphabet q + 15) + 1 := by
  obtain ⟨out', enc, hrun', hsupport, hden, hnum⟩ :=
    CurrentAdditive.RationalCandidateCompletion.sequentialMaterialized_complete_bits
      D alphabet halphabetPositive halphabetMass q
  rw [hrun] at hrun'
  have heq := Option.some.inj hrun'
  subst out'
  have hb : Nat.size enc.denominator ≤ outputWeightBits D alphabet q := by
    simpa only [outputWeightBits] using hden
  have hweight : ∀ entry ∈ out.toList,
      Nat.size entry.2.num.natAbs ≤ outputWeightBits D alphabet q ∧
      Nat.size entry.2.den ≤ outputWeightBits D alphabet q := by
    intro entry he
    obtain ⟨i, hi, hix⟩ := Array.mem_iff_getElem.mp (by simpa using he)
    let j : Fin out.size := ⟨i, hi⟩
    have hcanon := canonical_bits_of_common enc j
      (outputWeightBits D alphabet q) hb ((hnum j).trans hb)
    simpa [j, hix] using hcanon
  have hbytes := encodedSource_length_le out U
    (outputWeightBits D alphabet q) hcode
    (by intro entry he; exact (hweight entry he).1)
    (by intro entry he; exact (hweight entry he).2)
  calc
    (CodeDCanonicalSourceV2.encodedSource out).length ≤
        3 * out.size *
          (6 * q * (U + 1) + 8 * outputWeightBits D alphabet q + 15) + 1 := hbytes
    _ ≤ 3 * (generatedFeatures q D (alphabet.map Prod.fst)).size *
        (6 * q * (U + 1) + 8 * outputWeightBits D alphabet q + 15) + 1 := by
      gcongr

#print axioms actualSequentialEncodedSource_length_le

end CurrentAdditive.DeterministicCodeDActualSourceSize
