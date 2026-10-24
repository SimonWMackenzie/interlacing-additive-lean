import CurrentAdditive.GenericFeatureOuterMeasure

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
namespace CurrentAdditive.GenericFeaturePrefixMeasurePolynomial
open EthInapproximability.CurrentPaper
open FeatureOldDescriptorFrame96 FeatureOldDescriptorSemantics96 GenericFeatureOuterMeasure
open CylinderFeatureCodec FeaturePacketBound GenericFeaturePrefixByteBounds

theorem featurePrefix_succ (D j : Nat) (ys : List Nat) :
    featurePrefix D (j+1) ys = CylinderOrderedSpec.extendList D j ys (featurePrefix D j ys) := by
  simp [featurePrefix,CylinderOrderedSpec.generatedList,List.range_succ,List.foldl_append]

def smallCap (D q : Nat) (alphabet : Array (Nat × ℚ)) :=
  3*(D+1)*(pairCap q (alphabet.map Prod.fst)+1)+1

theorem packetCap_decompose (D : Nat) (q : Nat) (alphabet : Array (Nat × ℚ)) :
    packetCap D q alphabet=3*(1+q*alphabet.size)^D*(smallCap D q alphabet+1)+1 := by
  unfold packetCap smallCap
  apply congrArg (fun t => 3*(1+q*alphabet.size)^D*t+1)
  omega

theorem smallCap_le (D : Nat) (q : Nat) (alphabet : Array (Nat × ℚ)) :
    smallCap D q alphabet ≤ packetCap D q alphabet := by
  let F := (1+q*alphabet.size)^D
  let t := smallCap D q alphabet
  have hF : 1 ≤ F := one_le_pow₀ (by omega)
  have ht : t+1 ≤ F*(t+1) := by simpa only [one_mul] using Nat.mul_le_mul_right (t+1) hF
  rw [packetCap_decompose D]
  change t ≤ 3*F*(t+1)+1
  calc
    _ ≤ F*(t+1) := (Nat.le_succ t).trans ht
    _ ≤ 3*(F*(t+1))+1 := by omega
    _ = _ := by rw [Nat.mul_assoc]

theorem extension_body_le (D : Nat) (j q : Nat) (alphabet : Array (Nat × ℚ)) (hj : j<q)
    (c : List (Nat × Nat)) (hc : c∈featurePrefix D j (labels alphabet)) :
    (FeatureEligibleDescriptor96.extensions j c (labels alphabet)).length ≤
      3*(labels alphabet).length*(smallCap D q alphabet+1) := by
  have ht := SourceListEncoding.totalLength_map_le (labels alphabet)
    (fun y => encodeFeature ((j,y)::c)) (smallCap D q alphabet)
    (fun y hy => new_feature_le D j q alphabet hj c hc y hy)
  have hf := SourceListEncoding.fields_length
    ((labels alphabet).map (fun y => encodeFeature ((j,y)::c)))
  simp only [List.length_map] at hf
  change (SourceListEncoding.fields _).length ≤ _
  nlinarith

theorem extensionBytes_le (D : Nat) (j q : Nat) (alphabet : Array (Nat × ℚ)) (hj : j<q) :
    extensionBytes j (labels alphabet) (featurePrefix D j (labels alphabet)) ≤
      (featurePrefix D j (labels alphabet)).length*
        (3*(labels alphabet).length*(smallCap D q alphabet+1)) := by
  have h := SourceListEncoding.totalLength_map_le (featurePrefix D j (labels alphabet))
    (fun c => FeatureEligibleDescriptor96.extensions j c (labels alphabet))
    (3*(labels alphabet).length*(smallCap D q alphabet+1))
    (fun c hc => extension_body_le D j q alphabet hj c hc)
  simpa only [SourceListEncoding.totalLength,List.map_map,Function.comp_def,extensionBytes] using h

theorem labels_length (alphabet : Array (Nat × ℚ)) : (labels alphabet).length=alphabet.size := by simp [labels]

theorem measure_le (D : Nat) {q : Nat} (alphabet : Array (Nat × ℚ))
    (source : Array ((Fin q → Nat) × ℚ)) (j : Nat) (hj : j<q) :
    GenericFeatureOuterMeasure.measure D j (labels alphabet) (featurePrefix D j (labels alphabet)) [] []
      (CylinderRawInputProjection.input alphabet source) ≤
      100*(packetCap D q alphabet+(CylinderRawInputProjection.input alphabet source).length+1)^3 := by
  let N := (CylinderRawInputProjection.input alphabet source).length
  let P := packetCap D q alphabet
  let U := P+N+1
  obtain ⟨hq,ha,hbytes,halpha⟩ := raw_scalar_bounds alphabet source
  have hp := packet_le D j q alphabet hj.le
  have hf := fields_le D (j+1) q alphabet (by omega)
  rw [featurePrefix_succ] at hf
  have hc := count_le D j q alphabet hj.le
  have hs := smallCap_le D q alphabet
  have he := extensionBytes_le D j q alphabet hj
  have hy : (labels alphabet).length ≤ N := by rw [labels_length]; exact ha
  have hU : 1 ≤ U := by dsimp [U]; omega
  have hPU : P ≤ U := by dsimp [U]; omega
  have hNU : N ≤ U := by dsimp [U]; omega
  have hS : smallCap D q alphabet+1 ≤ U := by dsimp [U,P]; omega
  have hC : (featurePrefix D j (labels alphabet)).length ≤ U := hc.trans hPU
  have hY : (labels alphabet).length ≤ U := hy.trans hNU
  have heU : extensionBytes j (labels alphabet) (featurePrefix D j (labels alphabet)) ≤ 3*U^3 := by
    have hmul := Nat.mul_le_mul hC (Nat.mul_le_mul (Nat.mul_le_mul_left 3 hY) hS)
    calc
      _ ≤ _ := he
      _ ≤ U*(3*U*U) := hmul
      _ = _ := by ring
  have hjbit : j.bits.length ≤ N :=
    (by rw [Nat.size_eq_bits_len]; exact Nat.size_le.mpr j.lt_two_pow_self : j.bits.length ≤ j).trans (hj.le.trans hq)
  have hjnext : (j+1).bits.length ≤ N :=
    (by rw [Nat.size_eq_bits_len]; exact Nat.size_le.mpr (j+1).lt_two_pow_self : (j+1).bits.length ≤ j+1).trans (by omega)
  have hU3 : U ≤ U^3 := le_self_pow hU (by decide)
  change GenericFeatureOuterMeasure.measure D j _ _ [] [] _ ≤ 100*U^3
  unfold GenericFeatureOuterMeasure.measure
  simp only [List.length_nil]
  nlinarith

def measureCoefficient (D : Nat) := 100*(packetCoefficient D+1)^3
def measureExponent (D : Nat) := 3*packetExponent D

theorem measure_polynomial (D : Nat) {q : Nat} (alphabet : Array (Nat × ℚ))
    (source : Array ((Fin q → Nat) × ℚ)) (j : Nat) (hj : j<q) :
    GenericFeatureOuterMeasure.measure D j (labels alphabet) (featurePrefix D j (labels alphabet)) [] []
      (CylinderRawInputProjection.input alphabet source) ≤
      measureCoefficient D*((CylinderRawInputProjection.input alphabet source).length+1)^measureExponent D := by
  let N := (CylinderRawInputProjection.input alphabet source).length
  let U := N+1
  have hP := packetCap_polynomial D alphabet source
  change packetCap D q alphabet ≤ packetCoefficient D*U^packetExponent D at hP
  change GenericFeatureOuterMeasure.measure D j (labels alphabet) (featurePrefix D j (labels alphabet)) [] []
    (CylinderRawInputProjection.input alphabet source) ≤ measureCoefficient D*U^measureExponent D
  have hU : 1 ≤ U := by dsimp [U]; omega
  have hlinear : U ≤ U^packetExponent D := le_self_pow hU (by unfold packetExponent; omega)
  have hsum : packetCap D q alphabet+N+1 ≤ (packetCoefficient D+1)*U^packetExponent D := by
    change packetCap D q alphabet+U ≤ _
    nlinarith
  calc
    _ ≤ 100*(packetCap D q alphabet+N+1)^3 := measure_le D alphabet source j hj
    _ ≤ 100*(((packetCoefficient D+1)*U^packetExponent D)^3) :=
      Nat.mul_le_mul_left 100 (Nat.pow_le_pow_left hsum 3)
    _ = _ := by rw [mul_pow,←pow_mul,←Nat.mul_assoc]; simp only [measureCoefficient,measureExponent,Nat.mul_comm]

#print axioms measure_le
#print axioms measure_polynomial
end CurrentAdditive.GenericFeaturePrefixMeasurePolynomial
