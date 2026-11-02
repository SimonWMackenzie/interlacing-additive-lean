import CurrentAdditive.FeaturePrefixByteBounds96

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
namespace CurrentAdditive.FeaturePrefixMeasurePolynomial96
open EthInapproximability.CurrentPaper
open FeatureOldDescriptorFrame96 FeatureOldDescriptorSemantics96 FeatureOuterMeasure96
open CylinderFeatureCodec FeaturePacketBound FeatureGeneratedIteration96 FeaturePrefixByteBounds96

def smallCap (q : Nat) (alphabet : Array (Nat × ℚ)) :=
  3*8193*(pairCap q (alphabet.map Prod.fst)+1)+1

theorem packetCap_decompose (q : Nat) (alphabet : Array (Nat × ℚ)) :
    packetCap q alphabet=3*(1+q*alphabet.size)^8192*(smallCap q alphabet+1)+1 := by
  unfold packetCap smallCap
  apply congrArg (fun t => 3*(1+q*alphabet.size)^8192*t+1)
  omega

theorem smallCap_le (q : Nat) (alphabet : Array (Nat × ℚ)) :
    smallCap q alphabet ≤ packetCap q alphabet := by
  let F := (1+q*alphabet.size)^8192
  let t := smallCap q alphabet
  have hF : 1 ≤ F := one_le_pow₀ (by omega)
  have ht : t+1 ≤ F*(t+1) := by simpa only [one_mul] using Nat.mul_le_mul_right (t+1) hF
  rw [packetCap_decompose]
  change t ≤ 3*F*(t+1)+1
  calc
    _ ≤ F*(t+1) := (Nat.le_succ t).trans ht
    _ ≤ 3*(F*(t+1))+1 := by omega
    _ = _ := by rw [Nat.mul_assoc]

theorem extension_body_le (j q : Nat) (alphabet : Array (Nat × ℚ)) (hj : j<q)
    (c : List (Nat × Nat)) (hc : c∈featuresAt j (labels alphabet)) :
    (FeatureEligibleDescriptor96.extensions j c (labels alphabet)).length ≤
      3*(labels alphabet).length*(smallCap q alphabet+1) := by
  have ht := SourceListEncoding.totalLength_map_le (labels alphabet)
    (fun y => encodeFeature ((j,y)::c)) (smallCap q alphabet)
    (fun y hy => new_feature_le j q alphabet hj c hc y hy)
  have hf := SourceListEncoding.fields_length
    ((labels alphabet).map (fun y => encodeFeature ((j,y)::c)))
  simp only [List.length_map] at hf
  change (SourceListEncoding.fields _).length ≤ _
  nlinarith

theorem extensionBytes_le (j q : Nat) (alphabet : Array (Nat × ℚ)) (hj : j<q) :
    extensionBytes j (labels alphabet) (featuresAt j (labels alphabet)) ≤
      (featuresAt j (labels alphabet)).length*
        (3*(labels alphabet).length*(smallCap q alphabet+1)) := by
  have h := SourceListEncoding.totalLength_map_le (featuresAt j (labels alphabet))
    (fun c => FeatureEligibleDescriptor96.extensions j c (labels alphabet))
    (3*(labels alphabet).length*(smallCap q alphabet+1))
    (fun c hc => extension_body_le j q alphabet hj c hc)
  simpa only [SourceListEncoding.totalLength,List.map_map,Function.comp_def,extensionBytes] using h

theorem labels_length (alphabet : Array (Nat × ℚ)) : (labels alphabet).length=alphabet.size := by simp [labels]

theorem measure_le {q : Nat} (alphabet : Array (Nat × ℚ))
    (source : Array ((Fin q → Nat) × ℚ)) (j : Nat) (hj : j<q) :
    FeatureOuterMeasure96.measure j (labels alphabet) (featuresAt j (labels alphabet)) [] []
      (CylinderRawInputProjection.input alphabet source) ≤
      100*(packetCap q alphabet+(CylinderRawInputProjection.input alphabet source).length+1)^3 := by
  let N := (CylinderRawInputProjection.input alphabet source).length
  let P := packetCap q alphabet
  let U := P+N+1
  obtain ⟨hq,ha,hbytes,halpha⟩ := raw_scalar_bounds alphabet source
  have hp := packet_le j q alphabet hj.le
  have hf := fields_le (j+1) q alphabet (by omega)
  rw [featuresAt_succ] at hf
  have hc := count_le j q alphabet hj.le
  have hs := smallCap_le q alphabet
  have he := extensionBytes_le j q alphabet hj
  have hy : (labels alphabet).length ≤ N := by rw [labels_length]; exact ha
  have hU : 1 ≤ U := by dsimp [U]; omega
  have hPU : P ≤ U := by dsimp [U]; omega
  have hNU : N ≤ U := by dsimp [U]; omega
  have hS : smallCap q alphabet+1 ≤ U := by dsimp [U,P]; omega
  have hC : (featuresAt j (labels alphabet)).length ≤ U := hc.trans hPU
  have hY : (labels alphabet).length ≤ U := hy.trans hNU
  have heU : extensionBytes j (labels alphabet) (featuresAt j (labels alphabet)) ≤ 3*U^3 := by
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
  change FeatureOuterMeasure96.measure j _ _ [] [] _ ≤ 100*U^3
  unfold FeatureOuterMeasure96.measure
  simp only [List.length_nil]
  nlinarith

theorem raw_power_merge (U : Nat) :
    3*(U^16384*(100000*U))+1=300000*U^16385+1 := by ring

theorem packetCap_polynomial {q : Nat} (alphabet : Array (Nat × ℚ))
    (source : Array ((Fin q → Nat) × ℚ)) :
    packetCap q alphabet ≤ 400000*((CylinderRawInputProjection.input alphabet source).length+1)^16385 := by
  let N := (CylinderRawInputProjection.input alphabet source).length
  let U := N+1
  obtain ⟨hq,hm,hb,_⟩ := raw_scalar_bounds alphabet source
  have hbase : 1+q*alphabet.size ≤ U^2 := by dsimp [U]; nlinarith
  have hpow := Nat.pow_le_pow_left hbase 8192
  rw [←pow_mul] at hpow
  norm_num1 at hpow
  have hp := pairCap_actual_input q alphabet
  have hpN : pairCap q (alphabet.map Prod.fst) ≤ 4*N+2 := by omega
  have hfactor : 3*8193*(pairCap q (alphabet.map Prod.fst)+1)+2 ≤ 100000*U := by
    dsimp [U]; omega
  change packetCap q alphabet ≤ 400000*U^16385
  have hprod := Nat.mul_le_mul hpow hfactor
  have hU : 1 ≤ U := by dsimp [U]; omega
  have hone : 1 ≤ U^16385 := one_le_pow₀ hU
  calc
    packetCap q alphabet = 3*((1+q*alphabet.size)^8192*
      (3*8193*(pairCap q (alphabet.map Prod.fst)+1)+2))+1 := by unfold packetCap; rw [Nat.mul_assoc]
    _ ≤ 3*(U^16384*(100000*U))+1 := Nat.add_le_add_right (Nat.mul_le_mul_left 3 hprod) 1
    _ = 300000*U^16385+1 := raw_power_merge U
    _ ≤ _ := by omega

def measureCoefficient : Nat := 100*400001^3

theorem measure_polynomial {q : Nat} (alphabet : Array (Nat × ℚ))
    (source : Array ((Fin q → Nat) × ℚ)) (j : Nat) (hj : j<q) :
    FeatureOuterMeasure96.measure j (labels alphabet) (featuresAt j (labels alphabet)) [] []
      (CylinderRawInputProjection.input alphabet source) ≤
      measureCoefficient*((CylinderRawInputProjection.input alphabet source).length+1)^49155 := by
  let N := (CylinderRawInputProjection.input alphabet source).length
  let U := N+1
  have hP := packetCap_polynomial alphabet source
  change packetCap q alphabet ≤ 400000*U^16385 at hP
  change FeatureOuterMeasure96.measure j (labels alphabet) (featuresAt j (labels alphabet)) [] []
    (CylinderRawInputProjection.input alphabet source) ≤ measureCoefficient*U^49155
  have hU : 1 ≤ U := by dsimp [U]; omega
  have hlinear : U ≤ U^16385 := le_self_pow hU (by decide)
  have hsum : packetCap q alphabet+N+1 ≤ 400001*U^16385 := by omega
  calc
    _ ≤ 100*(packetCap q alphabet+N+1)^3 := measure_le alphabet source j hj
    _ ≤ 100*((400001*U^16385)^3) := Nat.mul_le_mul_left 100 (Nat.pow_le_pow_left hsum 3)
    _ = _ := by rw [mul_pow,←pow_mul,←Nat.mul_assoc]; norm_num [measureCoefficient]

#print axioms measure_le
#print axioms packetCap_polynomial
end CurrentAdditive.FeaturePrefixMeasurePolynomial96
