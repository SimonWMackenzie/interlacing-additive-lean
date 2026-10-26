import CurrentAdditive.CylinderEvalByteBounds

namespace CurrentAdditive.CylinderEvalOutputBounds

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineBankCodec
open CurrentAdditive.CylinderFeatureCodec CurrentAdditive.CylinderEvalByteBounds

def rowCoefficient : ℕ := 3*cellCap+4

theorem feature_count_le (feature : List (ℕ × ℕ)) :
    feature.length≤(encodeFeature feature).length := by
  simpa only [CylinderGeneralFeatureSemanticBare.descriptor_bytes,List.length_map] using
    count_le_list (feature.map encodePair)

theorem encoded_row_le {q : ℕ} (feature : List (ℕ × ℕ))
    (source : Array ((Fin q → ℕ) × ℚ)) :
    (CylinderRowSerializer.encodedRow (CylinderOrderedSpec.rowBits feature source)).length≤
      rowCoefficient*((SourceListEncoding.encode
        (CylinderProductionProjection.tupleWords source)).length+1) := by
  have hr := row_length_le (CylinderOrderedSpec.rowBits feature source)
  have hc := count_le_list (CylinderProductionProjection.tupleWords source)
  have hlen : (CylinderOrderedSpec.rowBits feature source).length=source.toList.length := by
    simp only [CylinderOrderedSpec.rowBits,List.length_map]
  rw [hlen] at hr
  have htuple : (CylinderProductionProjection.tupleWords source).length=source.toList.length := by
    simp only [CylinderProductionProjection.tupleWords,List.length_map]
  rw [htuple] at hc
  have hm := Nat.mul_le_mul_right (3*(cellCap+1)) hc
  dsimp only [rowCoefficient]
  nlinarith

theorem streamed_count_le (q D : ℕ) (alphabet : Array ℕ)
    (source : Array ((Fin q → ℕ) × ℚ)) :
    (CylinderOrderedSpec.streamedRows q D alphabet source).length≤
      (generatedFeatureBits q D alphabet).length := by
  have h := count_le_list ((SequentialCode.generatedFeatures q D alphabet).toList.map encodeFeature)
  simpa only [CylinderOrderedSpec.streamedRows,List.length_map,
    CylinderOrderedSpec.generatedList_exact,generatedFeatureBits,encodeFeatures,
    CodeDCodecV2.encodeItems] using h

theorem matrix_length_le (q D : ℕ) (alphabet : Array ℕ)
    (source : Array ((Fin q → ℕ) × ℚ)) :
    (cylinderMatrixBits q D alphabet source).length≤
      (3*rowCoefficient+4)*
        ((encode ![List.replicate q true,generatedFeatureBits q D alphabet,
          SourceListEncoding.encode (CylinderProductionProjection.tupleWords source)]).length+1)^2 := by
  let rows := CylinderOrderedSpec.streamedRows q D alphabet source
  let F := (generatedFeatureBits q D alphabet).length
  let T := (SourceListEncoding.encode (CylinderProductionProjection.tupleWords source)).length
  let N := (encode ![List.replicate q true,generatedFeatureBits q D alphabet,
          SourceListEncoding.encode (CylinderProductionProjection.tupleWords source)]).length
  have hrows : ∀ row∈rows,(CylinderRowSerializer.encodedRow row).length≤rowCoefficient*(T+1) := by
    intro row hrow
    obtain ⟨feature,_,rfl⟩ := List.mem_map.mp hrow
    exact encoded_row_le feature source
  have hm := SourceListEncoding.encode_map_length_le rows CylinderRowSerializer.encodedRow
    (rowCoefficient*(T+1)) hrows
  have hc := streamed_count_le q D alphabet source
  have hF := word_length_le_encode (![List.replicate q true,generatedFeatureBits q D alphabet,
          SourceListEncoding.encode (CylinderProductionProjection.tupleWords source)]) (1 : Fin 3)
  have hT := word_length_le_encode (![List.replicate q true,generatedFeatureBits q D alphabet,
          SourceListEncoding.encode (CylinderProductionProjection.tupleWords source)]) (2 : Fin 3)
  change F≤N at hF
  change T≤N at hT
  change rows.length≤F at hc
  have hp := Nat.mul_le_mul (hc.trans hF)
    (Nat.add_le_add_right (Nat.mul_le_mul_left rowCoefficient (Nat.add_le_add_right hT 1)) 1)
  have hbound : (cylinderMatrixBits q D alphabet source).length≤
      3*N*(rowCoefficient*(N+1)+1)+1 := by
    rw [← CylinderOrderedSpec.streamedRows_encoding]
    change (SourceListEncoding.encode (rows.map CylinderRowSerializer.encodedRow)).length≤_
    nlinarith [hm,hp]
  nlinarith

end CurrentAdditive.CylinderEvalOutputBounds

#print axioms CurrentAdditive.CylinderEvalOutputBounds.matrix_length_le
