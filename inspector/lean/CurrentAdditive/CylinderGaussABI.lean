import CurrentAdditive.CylinderResourceSpec
import CurrentAdditive.GaussTypedPacket
import CurrentAdditive.SequentialArrayBridge
import CurrentAdditive.SequentialSourceCode
import CurrentAdditive.SequentialCompressionTotality
import CurrentAdditive.GaussMatrixClock

/-! Exact bytes connecting the cylinder matrix to the materialized Gauss ABI. -/

namespace CurrentAdditive.CylinderGaussABI

open EthInapproximability.CurrentPaper
open CurrentAdditive.CylinderFeatureCodec
open CurrentAdditive.GaussPhysical
open CurrentAdditive.SequentialCode
open CurrentAdditive.SequentialCompressionTotality

theorem raw_zero : GaussPhysical.rawOfRat (0 : ℚ) = zeroRat := by
  norm_num [GaussPhysical.rawOfRat, zeroRat]

theorem raw_one : GaussPhysical.rawOfRat (1 : ℚ) = oneRat := by
  norm_num [GaussPhysical.rawOfRat, oneRat]

theorem zero_one_packet (x : ℚ) (hx : x = 0 ∨ x = 1) :
    encodeZeroOne x = CodeDCodec.encodeRawRat (GaussPhysical.rawOfRat x) := by
  rcases hx with h | h <;> subst x
  · simp [encodeZeroOne, raw_zero]
  · simp [encodeZeroOne, raw_one]

theorem typedRows_of_rectangular (a : Array (Array ℚ)) (K : Nat)
    (hK : columnCount a = K)
    (hrow : ∀ i, i < a.size → (a[i]?.getD #[]).size = K) :
    GaussPhysical.typedRows
      (SequentialArrayBridge.matrixOfArray a) =
      a.toList.map Array.toList := by
  apply List.ext_getElem
  · simp [GaussPhysical.typedRows]
  · intro i hi₁ hi₂
    simp only [GaussPhysical.typedRows, List.getElem_map,
      List.getElem_finRange] at *
    have hi : i < a.size := by simpa using hi₂
    have hs : (a[i]).size = K := by
      simpa [Array.getElem?_eq_getElem hi] using hrow i hi
    apply List.ext_getElem
    · simp [hK, hs]
    · intro j hj₁ hj₂
      have hj : j < (a[i]).size := by simpa using hj₂
      simp [SequentialArrayBridge.matrixOfArray, cell,
        Array.getElem?_eq_getElem hi,
        Array.getElem?_eq_getElem hj]

theorem cylinder_to_gauss_bytes (q D : Nat) (alphabet : Array Nat)
    (source : Array ((Fin q → Nat) × ℚ)) :
    cylinderMatrixBits q D alphabet source =
      GaussPhysical.encodeTypedMatrix
        (SequentialArrayBridge.matrixOfArray
          (cylinders q D alphabet source)) := by
  let a := cylinders q D alphabet source
  have hpos : 0 < (generatedFeatures q D alphabet).size :=
    SequentialSourceCode.generatedFeatures_pos q D alphabet
  have hK : columnCount a = source.size := by
    simpa [a, cylinders] using
      (featureRows_columnCount (generatedFeatures q D alphabet).size
        (fun v j => generatedFeatureValue v
          (generatedFeatures q D alphabet)[j]) source hpos)
  have hrow : ∀ i, i < a.size → (a[i]?.getD #[]).size = source.size := by
    intro i hi
    simpa [a, Array.getElem?_eq_getElem hi] using
      cylinders_columns q D alphabet source i hi
  have htyped := typedRows_of_rectangular a source.size hK hrow
  change encodeRows a = GaussPhysical.encodeTypedMatrix
    (SequentialArrayBridge.matrixOfArray a)
  rw [GaussPhysical.encodeTypedMatrix, htyped]
  unfold GaussPhysical.encodeRationalMatrix GaussPhysical.encodeMatrix
    GaussPhysical.encodeRow encodeRows
  simp only [List.map_map]
  apply congrArg CodeDCodecV2.encodeItems
  apply List.map_congr_left
  intro row hrowmem
  apply congrArg CodeDCodecV2.encodeItems
  simp only [Function.comp_apply, List.map_map]
  apply List.map_congr_left
  intro x hx
  have hzeroone : x = 0 ∨ x = 1 := by
    have hrowA : row ∈ a := by simpa using hrowmem
    have hxA : x ∈ row := by simpa using hx
    obtain ⟨i, hi, hri⟩ := Array.mem_iff_getElem.mp hrowA
    obtain ⟨j, hj, hxj⟩ := Array.mem_iff_getElem.mp hxA
    have hci : i < (cylinders q D alphabet source).size := by
      simpa [a] using hi
    have hcj : j < (cylinders q D alphabet source)[i].size := by
      simpa [a, hri] using hj
    have hz := cylinder_entry_zero_one q D alphabet source i j hci hcj
    simpa [a, hri, hxj] using hz
  exact zero_one_packet x hzeroone

theorem cylinder_matrix_bitlength (q D : Nat) (alphabet : Array Nat)
    (source : Array ((Fin q → Nat) × ℚ)) :
    (cylinderMatrixBits q D alphabet source).length ≤
      3 * (generatedFeatures q D alphabet).size *
        (3 * source.size * 10 + 2) + 1 := by
  let a := cylinders q D alphabet source
  have hpos : 0 < (generatedFeatures q D alphabet).size :=
    SequentialSourceCode.generatedFeatures_pos q D alphabet
  have hrows : a.size = (generatedFeatures q D alphabet).size :=
    cylinders_rows q D alphabet source
  have hcols : columnCount a = source.size := by
    simpa [a, cylinders] using
      (featureRows_columnCount (generatedFeatures q D alphabet).size
        (fun v j => generatedFeatureValue v
          (generatedFeatures q D alphabet)[j]) source hpos)
  let B := SequentialArrayBridge.matrixOfArray a
  have hbits : ∀ i j, Nat.size (B i j).num.natAbs ≤ 1 ∧
      Nat.size (B i j).den ≤ 1 := by
    intro i j
    have hi : i.val < (cylinders q D alphabet source).size := i.isLt
    have hj : j.val < (cylinders q D alphabet source)[i.val].size := by
      rw [cylinders_columns q D alphabet source i.val hi]
      simpa [hcols] using j.isLt
    have h01 := cylinder_entry_zero_one q D alphabet source
      i.val j.val hi hj
    have hB : B i j = (cylinders q D alphabet source)[i.val][j.val] := by
      have hjA : j.val < a[i.val].size := by simpa [a] using hj
      simp [B, SequentialArrayBridge.matrixOfArray, cell, a,
        Array.getElem?_eq_getElem hjA]
    rw [hB]
    rcases h01 with h | h <;> rw [h] <;> norm_num
  have hb := GaussPhysical.encodeTypedMatrix_length B 1 hbits
  rw [cylinder_to_gauss_bytes]
  simpa [B, a, hrows, hcols] using hb

#print axioms cylinder_to_gauss_bytes
#print axioms cylinder_matrix_bitlength

end CurrentAdditive.CylinderGaussABI
