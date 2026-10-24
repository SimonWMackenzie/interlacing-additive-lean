import CurrentAdditive.CylinderOrderedSpec
import CurrentAdditive.CylinderMomentCountBound

/-!
Exact dimensions and bit charges for the ordered cylinder packet.  The
manuscript's fixed order is 8192, so the feature count is a polynomial in
the numeric coordinate and alphabet counts.  The payload charge retains the
actual encoded feature lengths, including repeated alphabet entries.
-/

namespace CurrentAdditive.CylinderResourceSpec

open Finset
open EthInapproximability.CurrentPaper
open SequentialCode
open CurrentAdditive.CylinderFeatureCodec
open CurrentAdditive.CylinderOrderedSpec

def fixedD : Nat := 8192

def featureCountAt (D q m : Nat) : Nat :=
  ∑ k ∈ Finset.range (min D q + 1), q.choose k * m ^ k

def featureCount (q m : Nat) : Nat := featureCountAt fixedD q m

theorem featureCountAt_exact (D q : Nat) (alphabet : Array Nat) :
    (generatedList q D alphabet.toList).length =
      featureCountAt D q alphabet.size := by
  rw [generatedList_exact]
  simpa [featureCountAt] using
    (SequentialFeatureCount.generatedFeatures_size_min q D alphabet)

theorem featureCountAt_polynomial (D q m : Nat) :
    featureCountAt D q m ≤ (1 + q * m) ^ D := by
  exact moment_count_le_one_add_pow q D m

theorem featureCount_exact (q : Nat) (alphabet : Array Nat) :
    (generatedList q fixedD alphabet.toList).length =
      featureCount q alphabet.size := by
  exact featureCountAt_exact fixedD q alphabet

theorem featureCount_polynomial (q m : Nat) :
    featureCount q m ≤ (1 + q * m) ^ fixedD := by
  exact featureCountAt_polynomial fixedD q m

def featurePayloadBitsAt (q D : Nat) (alphabet : Array Nat) : Nat :=
  SourceListEncoding.totalLength
    ((generatedList q D alphabet.toList).map encodeFeature)

theorem featurePacket_bitlength_at (q D : Nat) (alphabet : Array Nat) :
    (featurePacket q D alphabet).length ≤
      3 * featurePayloadBitsAt q D alphabet +
      3 * featureCountAt D q alphabet.size + 1 := by
  have h := SourceListEncoding.encode_length
    ((generatedList q D alphabet.toList).map encodeFeature)
  simpa [featurePacket, featurePayloadBitsAt,
    featureCountAt_exact D q alphabet] using h

def featurePayloadBits (q : Nat) (alphabet : Array Nat) : Nat :=
  featurePayloadBitsAt q fixedD alphabet

theorem featurePacket_bitlength (q : Nat) (alphabet : Array Nat) :
    (featurePacket q fixedD alphabet).length ≤
      3 * featurePayloadBits q alphabet +
      3 * featureCount q alphabet.size + 1 := by
  exact featurePacket_bitlength_at q fixedD alphabet

theorem row_count (q : Nat) (alphabet : Array Nat)
    (source : Array ((Fin q → Nat) × ℚ)) :
    (streamedRows q fixedD alphabet source).length =
      featureCount q alphabet.size := by
  simp [streamedRows, featureCount_exact]

theorem row_width (q : Nat) (alphabet : Array Nat)
    (source : Array ((Fin q → Nat) × ℚ))
    (row : List Bool)
    (h : row ∈ streamedRows q fixedD alphabet source) :
    row.length = source.size := by
  simp only [streamedRows, List.mem_map] at h
  obtain ⟨feature, _, rfl⟩ := h
  simp [rowBits]

theorem matrix_cell_count (q : Nat) (alphabet : Array Nat)
    (source : Array ((Fin q → Nat) × ℚ)) :
    ((streamedRows q fixedD alphabet source).map List.length).sum =
      featureCount q alphabet.size * source.size := by
  have hrow : ∀ row ∈ streamedRows q fixedD alphabet source,
      row.length = source.size := by
    intro row hr
    exact row_width q alphabet source row hr
  have hmap : (streamedRows q fixedD alphabet source).map List.length =
      List.replicate (featureCount q alphabet.size) source.size := by
    apply List.ext_getElem
    · simp [row_count]
    · intro i hi₁ hi₂
      simp only [List.getElem_map]
      have hi : i < (streamedRows q fixedD alphabet source).length := by
        simpa using hi₁
      simpa using row_width q alphabet source _
        (List.getElem_mem hi)
  rw [hmap]
  simp

#print axioms featureCount_exact
#print axioms featureCountAt_exact
#print axioms featureCountAt_polynomial
#print axioms featureCount_polynomial
#print axioms featurePacket_bitlength
#print axioms matrix_cell_count

end CurrentAdditive.CylinderResourceSpec
