import CurrentAdditive.FeaturePrefixByteBounds96

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
namespace CurrentAdditive.GenericFeaturePrefixByteBounds
open EthInapproximability.CurrentPaper
open FeatureOldDescriptorFrame96 FeatureOldDescriptorSemantics96
open CylinderFeatureCodec FeaturePacketBound
def featurePrefix (D j : Nat) (ys : List Nat) := CylinderOrderedSpec.generatedList j D ys

def labels (alphabet : Array (Nat × ℚ)) := (alphabet.map Prod.fst).toList

def packetCap (D q : Nat) (alphabet : Array (Nat × ℚ)) : Nat :=
  3*(1+q*alphabet.size)^D*
    (3*(D+1)*(pairCap q (alphabet.map Prod.fst)+1)+2)+1

theorem pairCap_mono (j q : Nat) (a : Array Nat) (hj : j≤q) :
    pairCap j a≤pairCap q a := by
  have hb : j.bits.length≤q.bits.length := by
    simpa only [Nat.size_eq_bits_len] using Nat.size_le_size hj
  unfold pairCap
  omega

theorem packet_eq (D : Nat) (j : Nat) (alphabet : Array (Nat × ℚ)) :
    SourceListEncoding.encode (words (featurePrefix D j (labels alphabet)))=
      generatedFeatureBits j D (alphabet.map Prod.fst) := by
  simp only [featurePrefix,labels,CylinderOrderedSpec.generatedList_exact,words,
    generatedFeatureBits,encodeFeatures,CodeDCodecV2.encodeItems]

theorem packet_le (D : Nat) (j q : Nat) (alphabet : Array (Nat × ℚ)) (hj : j≤q) :
    (SourceListEncoding.encode (words (featurePrefix D j (labels alphabet)))).length≤packetCap D q alphabet := by
  rw [packet_eq D]
  have h := FeaturePacketBound.packet_length_le j D (alphabet.map Prod.fst)
  have hp := pairCap_mono j q (alphabet.map Prod.fst) hj
  simp only [Array.size_map] at h
  apply h.trans
  unfold packetCap
  gcongr <;> omega

theorem count_le (D : Nat) (j q : Nat) (alphabet : Array (Nat × ℚ)) (hj : j≤q) :
    (featurePrefix D j (labels alphabet)).length≤packetCap D q alphabet := by
  have hm := CylinderRawInputProjection.input_measure_le (words (featurePrefix D j (labels alphabet)))
  have hp := packet_le D j q alphabet hj
  unfold CylinderProductionProjectionClock.inputMeasure at hm
  simp only [words,List.length_map] at hm hp
  omega

theorem fields_le (D : Nat) (j q : Nat) (alphabet : Array (Nat × ℚ)) (hj : j≤q) :
    (SourceListEncoding.fields (words (featurePrefix D j (labels alphabet)))).length≤packetCap D q alphabet := by
  have h := packet_le D j q alphabet hj
  unfold SourceListEncoding.encode at h
  simp only [List.length_append] at h
  omega

theorem new_feature_le (D : Nat) (j q : Nat) (alphabet : Array (Nat × ℚ)) (hj : j<q)
    (c : List (Nat × Nat)) (hc : c∈featurePrefix D j (labels alphabet))
    (y : Nat) (hy : y∈labels alphabet) :
    (encodeFeature ((j,y)::c)).length≤3*(D+1)*(pairCap q (alphabet.map Prod.fst)+1)+1 := by
  have hc' : c∈(SequentialCode.generatedFeatures j D (alphabet.map Prod.fst)).toList := by
    simpa only [featurePrefix,labels,CylinderOrderedSpec.generatedList_exact] using hc
  have hlen := SequentialFeatureCount.generatedFeatures_length_le j D (alphabet.map Prod.fst) c hc'
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
    · exact (generated_pair_length_le j D (alphabet.map Prod.fst) c hc' p hp).trans
        (pairCap_mono j q _ hj.le)
  have h := SourceListEncoding.encode_map_length_le ((j,y)::c) encodePair
    (pairCap q (alphabet.map Prod.fst)) hall
  change (encodeFeature ((j,y)::c)).length≤_ at h
  have hlen' : ((j,y)::c).length≤(D+1) := by simp only [List.length_cons]; omega
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

/-- Constants depend only on the fixed dimension, including dimension zero. -/
def packetCoefficient (D : Nat) := 100*(D+1)
def packetExponent (D : Nat) := 2*D+1

theorem packetCap_polynomial (D : Nat) {q : Nat} (alphabet : Array (Nat × ℚ))
    (source : Array ((Fin q → Nat) × ℚ)) :
    packetCap D q alphabet ≤ packetCoefficient D*
      ((CylinderRawInputProjection.input alphabet source).length+1)^packetExponent D := by
  let N := (CylinderRawInputProjection.input alphabet source).length
  let U := N+1
  obtain ⟨hq,hm,hb,_⟩ := raw_scalar_bounds alphabet source
  have hbase : 1+q*alphabet.size ≤ U^2 := by dsimp [U]; nlinarith
  have hpow := Nat.pow_le_pow_left hbase D
  rw [←pow_mul] at hpow
  have hp := pairCap_actual_input q alphabet
  have hpN : pairCap q (alphabet.map Prod.fst)+1 ≤ 4*U := by dsimp [U]; omega
  have hU : 1 ≤ U := by dsimp [U]; omega
  have hfactor : 3*(D+1)*(pairCap q (alphabet.map Prod.fst)+1)+2 ≤ 16*(D+1)*U := by
    have hmul := Nat.mul_le_mul_left (3*(D+1)) hpN
    have hDU : 1 ≤ (D+1)*U := by nlinarith
    nlinarith
  have hprod := Nat.mul_le_mul hpow hfactor
  have hone : 1 ≤ U^(2*D+1) := one_le_pow₀ hU
  change packetCap D q alphabet ≤ 100*(D+1)*U^(2*D+1)
  calc
    packetCap D q alphabet = 3*((1+q*alphabet.size)^D*
        (3*(D+1)*(pairCap q (alphabet.map Prod.fst)+1)+2))+1 := by
      unfold packetCap; rw [Nat.mul_assoc]
    _ ≤ 3*(U^(2*D)*(16*(D+1)*U))+1 := Nat.add_le_add_right (Nat.mul_le_mul_left 3 hprod) 1
    _ = 48*(D+1)*U^(2*D+1)+1 := by rw [pow_succ]; ring
    _ ≤ _ := by nlinarith

/-- The generic actual-input packet bound is consumed directly, without a
power-of-two enlargement of the dimension. -/
theorem packet_length_actual_polynomial (D : Nat) {q : Nat}
    (alphabet : Array (Nat × ℚ)) (source : Array ((Fin q → Nat) × ℚ)) :
    (generatedFeatureBits q D (alphabet.map Prod.fst)).length ≤ packetCoefficient D*
      ((CylinderRawInputProjection.input alphabet source).length+1)^packetExponent D := by
  have h := FeaturePacketBound.packet_length_actual_input q D alphabet
  let N := (CylinderRawInputProjection.input alphabet source).length
  let U := N+1
  obtain ⟨hq,hm,hb,_⟩ := raw_scalar_bounds alphabet source
  have hbase : 1+q*alphabet.size ≤ U^2 := by dsimp [U]; nlinarith
  have hpow := Nat.pow_le_pow_left hbase D
  rw [←pow_mul] at hpow
  have hinput : 2*(q+(CodeDTargetV2.alphabetBytes alphabet).length)+3 ≤ 4*U := by dsimp [U]; omega
  have hU : 1 ≤ U := by dsimp [U]; omega
  have hfactor : 3*D*(2*(q+(CodeDTargetV2.alphabetBytes alphabet).length)+3)+2 ≤ 16*(D+1)*U := by
    have hmul := Nat.mul_le_mul_left (3*D) hinput
    nlinarith
  have hprod := Nat.mul_le_mul hpow hfactor
  have hone : 1 ≤ U^(2*D+1) := one_le_pow₀ hU
  change _ ≤ 100*(D+1)*U^(2*D+1)
  calc
    _ ≤ 3*(1+q*alphabet.size)^D*
      (3*D*(2*(q+(CodeDTargetV2.alphabetBytes alphabet).length)+3)+2)+1 := h
    _ ≤ 3*(U^(2*D)*(16*(D+1)*U))+1 := by
      rw [Nat.mul_assoc]; exact Nat.add_le_add_right (Nat.mul_le_mul_left 3 hprod) 1
    _ = 48*(D+1)*U^(2*D+1)+1 := by rw [pow_succ]; ring
    _ ≤ _ := by nlinarith

#print axioms packetCap_polynomial
#print axioms packet_length_actual_polynomial
end CurrentAdditive.GenericFeaturePrefixByteBounds
