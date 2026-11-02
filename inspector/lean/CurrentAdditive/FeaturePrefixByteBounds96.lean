import CurrentAdditive.FeatureOuterMeasure96
import CurrentAdditive.FeatureGeneratedIteration96
import CurrentAdditive.FeatureStateSize96
import CurrentAdditive.FeaturePacketBound

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
namespace CurrentAdditive.FeaturePrefixByteBounds96
open EthInapproximability.CurrentPaper
open FeatureOldDescriptorFrame96 FeatureOldDescriptorSemantics96
open CylinderFeatureCodec FeaturePacketBound
open FeatureGeneratedIteration96

def labels (alphabet : Array (Nat × ℚ)) := (alphabet.map Prod.fst).toList

def packetCap (q : Nat) (alphabet : Array (Nat × ℚ)) : Nat :=
  3*(1+q*alphabet.size)^8192*
    (3*8193*(pairCap q (alphabet.map Prod.fst)+1)+2)+1

theorem pairCap_mono (j q : Nat) (a : Array Nat) (hj : j≤q) :
    pairCap j a≤pairCap q a := by
  have hb : j.bits.length≤q.bits.length := by
    simpa only [Nat.size_eq_bits_len] using Nat.size_le_size hj
  unfold pairCap
  omega

theorem packet_eq (j : Nat) (alphabet : Array (Nat × ℚ)) :
    SourceListEncoding.encode (words (featuresAt j (labels alphabet)))=
      generatedFeatureBits j 8192 (alphabet.map Prod.fst) := by
  simp only [featuresAt,labels,CylinderOrderedSpec.generatedList_exact,words,
    generatedFeatureBits,encodeFeatures,CodeDCodecV2.encodeItems]

theorem packet_le (j q : Nat) (alphabet : Array (Nat × ℚ)) (hj : j≤q) :
    (SourceListEncoding.encode (words (featuresAt j (labels alphabet)))).length≤packetCap q alphabet := by
  rw [packet_eq]
  have h := FeaturePacketBound.packet_length_le j 8192 (alphabet.map Prod.fst)
  have hp := pairCap_mono j q (alphabet.map Prod.fst) hj
  simp only [Array.size_map] at h
  apply h.trans
  unfold packetCap
  gcongr <;> omega

theorem count_le (j q : Nat) (alphabet : Array (Nat × ℚ)) (hj : j≤q) :
    (featuresAt j (labels alphabet)).length≤packetCap q alphabet := by
  have hm := CylinderRawInputProjection.input_measure_le (words (featuresAt j (labels alphabet)))
  have hp := packet_le j q alphabet hj
  unfold CylinderProductionProjectionClock.inputMeasure at hm
  simp only [words,List.length_map] at hm hp
  omega

theorem fields_le (j q : Nat) (alphabet : Array (Nat × ℚ)) (hj : j≤q) :
    (SourceListEncoding.fields (words (featuresAt j (labels alphabet)))).length≤packetCap q alphabet := by
  have h := packet_le j q alphabet hj
  unfold SourceListEncoding.encode at h
  simp only [List.length_append] at h
  omega

theorem new_feature_le (j q : Nat) (alphabet : Array (Nat × ℚ)) (hj : j<q)
    (c : List (Nat × Nat)) (hc : c∈featuresAt j (labels alphabet))
    (y : Nat) (hy : y∈labels alphabet) :
    (encodeFeature ((j,y)::c)).length≤3*8193*(pairCap q (alphabet.map Prod.fst)+1)+1 := by
  have hc' : c∈(SequentialCode.generatedFeatures j 8192 (alphabet.map Prod.fst)).toList := by
    simpa only [featuresAt,labels,CylinderOrderedSpec.generatedList_exact] using hc
  have hlen := SequentialFeatureCount.generatedFeatures_length_le j 8192 (alphabet.map Prod.fst) c hc'
  have hnew : (encodePair (j,y)).length≤pairCap q (alphabet.map Prod.fst) := by
    have hb : j.bits.length≤q.bits.length := by
      simpa only [Nat.size_eq_bits_len] using Nat.size_le_size hj.le
    have hybits : y.bits.length≤labelBits (alphabet.map Prod.fst) := by
      apply List.le_sum_of_mem
      exact List.mem_map.mpr ⟨y,hy,rfl⟩
    rw [CylinderPairWriter.pair_length]
    unfold pairCap
    dsimp only [Prod.fst,Prod.snd]
    omega
  have hall (p : Nat × Nat) (hp : p∈(j,y)::c) :
      (encodePair p).length≤pairCap q (alphabet.map Prod.fst) := by
    rcases List.mem_cons.mp hp with rfl | hp
    · exact hnew
    · exact (generated_pair_length_le j 8192 (alphabet.map Prod.fst) c hc' p hp).trans
        (pairCap_mono j q _ hj.le)
  have h := SourceListEncoding.encode_map_length_le ((j,y)::c) encodePair
    (pairCap q (alphabet.map Prod.fst)) hall
  change (encodeFeature ((j,y)::c)).length≤_ at h
  have hlen' : ((j,y)::c).length≤8193 := by simp only [List.length_cons]; omega
  exact h.trans (Nat.add_le_add_right (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 3 hlen')) 1)

theorem raw_scalar_bounds {q : Nat} (alphabet : Array (Nat × ℚ))
    (source : Array ((Fin q → Nat) × ℚ)) :
    let N := (CylinderRawInputProjection.input alphabet source).length
    q≤N ∧ alphabet.size≤N ∧ (CodeDTargetV2.alphabetBytes alphabet).length≤N ∧
      (SourceListEncoding.encode (FeatureInnerAlphabetRun64.labelWords (labels alphabet))).length≤6*N+1 := by
  dsimp only
  have hq := CylinderRawInputProjection.field_length_le alphabet source 0
  have ha := CylinderRawInputProjection.field_length_le alphabet source 1
  simp only [Matrix.cons_val_zero,List.length_replicate,Matrix.cons_val_one] at hq ha
  have hm := CylinderRawInputProjection.input_measure_le (CylinderProductionProjection.alphabetItems alphabet)
  unfold CylinderProductionProjectionClock.inputMeasure at hm
  have hcount : alphabet.size≤(CodeDTargetV2.alphabetBytes alphabet).length := by
    simpa only [CylinderProductionProjection.alphabetItems,List.length_map,Array.length_toList,
      CodeDTargetV2.alphabetBytes,CodeDCodecV2.encodeItems] using
      (show (CylinderProductionProjection.alphabetItems alphabet).length≤
        (SourceListEncoding.encode (CylinderProductionProjection.alphabetItems alphabet)).length by omega)
  have hl := labelBits_le_alphabetBytes alphabet
  have he := SourceListEncoding.encode_length (FeatureInnerAlphabetRun64.labelWords (labels alphabet))
  have hs : SourceListEncoding.totalLength (FeatureInnerAlphabetRun64.labelWords (labels alphabet))=
      labelBits (alphabet.map Prod.fst) := by
    simp [SourceListEncoding.totalLength,FeatureInnerAlphabetRun64.labelWords,labels,labelBits,Function.comp_def]
  have hc : (FeatureInnerAlphabetRun64.labelWords (labels alphabet)).length=alphabet.size := by
    simp [FeatureInnerAlphabetRun64.labelWords,labels]
  rw [hs,hc] at he
  exact ⟨hq,hcount.trans ha,ha,by omega⟩

#print axioms packet_le
#print axioms raw_scalar_bounds
end CurrentAdditive.FeaturePrefixByteBounds96
