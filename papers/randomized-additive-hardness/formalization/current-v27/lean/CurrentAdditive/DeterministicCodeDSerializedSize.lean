import CurrentAdditive.GaussClock
import CurrentAdditive.CodeDTargetV2
import Mathlib.Tactic

/-!
Exact framing-cost bounds for the physical Code D input and output formats.
The hypotheses concern the actual integers and rational weights being encoded;
no machine or successor runtime is inferred from these byte counts.
-/

namespace CurrentAdditive.DeterministicCodeDSerializedSize

open EthInapproximability.CurrentPaper
open CurrentAdditive.CodeDCodec
open CurrentAdditive.CodeDCodecV2
open CurrentAdditive.CodeDSourceCodecV2
open CurrentAdditive.CodeDCanonicalSourceV2

theorem alphabetEntry_length_le (entry : Nat × ℚ) (U S : Nat)
    (hcode : entry.1.bits.length ≤ U)
    (hnum : Nat.size entry.2.num.natAbs ≤ S)
    (hden : Nat.size entry.2.den ≤ S) :
    (CodeDTargetV2.alphabetEntry entry).length ≤ 2 * U + 8 * S + 12 := by
  have hw : (encodeRawRat (CodeDCanonicalSourceV2.rawOfRat entry.2)).length ≤
      4 * S + 5 := by
    simpa only [CodeDCanonicalSourceV2.rawOfRat,
      GaussPhysical.rawOfRat] using
      (GaussPhysical.rawOfRat_code_length entry.2 S hnum hden)
  rw [CodeDTargetV2.alphabetEntry, BitMachineBankCodec.encode_length]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  norm_num
  omega

theorem alphabetBytes_length_le (alphabet : Array (Nat × ℚ)) (U S : Nat)
    (hcode : ∀ entry ∈ alphabet.toList, entry.1.bits.length ≤ U)
    (hnum : ∀ entry ∈ alphabet.toList, Nat.size entry.2.num.natAbs ≤ S)
    (hden : ∀ entry ∈ alphabet.toList, Nat.size entry.2.den ≤ S) :
    (CodeDTargetV2.alphabetBytes alphabet).length ≤
      3 * alphabet.size * (2 * U + 8 * S + 13) + 1 := by
  have h := SourceListEncoding.encode_map_length_le alphabet.toList
    CodeDTargetV2.alphabetEntry (2 * U + 8 * S + 12)
    (by
      intro entry he
      exact alphabetEntry_length_le entry U S
        (hcode entry he) (hnum entry he) (hden entry he))
  simpa [CodeDTargetV2.alphabetBytes, CodeDCodecV2.encodeItems] using h

theorem canonicalEntry_length_le {q : Nat} (entry : (Fin q → Nat) × ℚ)
    (U S : Nat)
    (hcode : ∀ j : Fin q, (entry.1 j).bits.length ≤ U)
    (hnum : Nat.size entry.2.num.natAbs ≤ S)
    (hden : Nat.size entry.2.den ≤ S) :
    (CodeDSourceCodecV2.encodeEntry (canonicalEntry entry)).length ≤
      6 * q * (U + 1) + 8 * S + 14 := by
  have hword :
      (CodeDCodecV2.encodeItems
        (List.ofFn (fun j : Fin q => (entry.1 j).bits))).length ≤
        3 * q * (U + 1) + 1 := by
    have h := SourceListEncoding.encode_map_length_le
      (List.ofFn (fun j : Fin q => (entry.1 j).bits)) id U (by
        intro x hx
        obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hx
        exact hcode j)
    simpa [CodeDCodecV2.encodeItems] using h
  have hw : (encodeRawRat (CodeDCanonicalSourceV2.rawOfRat entry.2)).length ≤
      4 * S + 5 := by
    simpa only [CodeDCanonicalSourceV2.rawOfRat,
      GaussPhysical.rawOfRat] using
      (GaussPhysical.rawOfRat_code_length entry.2 S hnum hden)
  rw [CodeDSourceCodecV2.encodeEntry, BitMachineBankCodec.encode_length]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  norm_num
  dsimp [canonicalEntry]
  nlinarith

theorem encodedSource_length_le {q : Nat}
    (source : Array ((Fin q → Nat) × ℚ)) (U S : Nat)
    (hcode : ∀ entry ∈ source.toList,
      ∀ j : Fin q, (entry.1 j).bits.length ≤ U)
    (hnum : ∀ entry ∈ source.toList,
      Nat.size entry.2.num.natAbs ≤ S)
    (hden : ∀ entry ∈ source.toList,
      Nat.size entry.2.den ≤ S) :
    (encodedSource source).length ≤
      3 * source.size * (6 * q * (U + 1) + 8 * S + 15) + 1 := by
  have h := SourceListEncoding.encode_map_length_le source.toList
    (fun entry => CodeDSourceCodecV2.encodeEntry (canonicalEntry entry))
    (6 * q * (U + 1) + 8 * S + 14)
    (by
      intro entry he
      exact canonicalEntry_length_le entry U S
        (hcode entry he) (hnum entry he) (hden entry he))
  simpa [encodedSource, canonicalSource, CodeDSourceCodecV2.encodeSource,
    CodeDCodecV2.encodeItems, List.map_map] using h

#print axioms alphabetBytes_length_le
#print axioms encodedSource_length_le

end CurrentAdditive.DeterministicCodeDSerializedSize
