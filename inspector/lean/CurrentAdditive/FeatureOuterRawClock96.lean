import CurrentAdditive.FeaturePacketClockBound96
import CurrentAdditive.FeaturePrefixMeasurePolynomial96
import CurrentAdditive.FeatureIterationSumBound96

/-! A fixed public polynomial bounds the actual coordinate iteration in the
original encoded weighted input. All intermediate list/count/byte bounds are
derived from its generated-prefix semantics, without an output-size premise. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
namespace CurrentAdditive.FeatureOuterRawClock96
open EthInapproximability.CurrentPaper
open FeatureOldDescriptorFrame96 FeatureOldDescriptorSemantics96
open FeatureGeneratedIteration96 FeaturePrefixByteBounds96 FeaturePrefixMeasurePolynomial96

private noncomputable opaque stepDatum :
    {C : Nat // C=FeaturePacketClockBound96.packetCoefficient*(measureCoefficient+1)^6} :=
  ⟨FeaturePacketClockBound96.packetCoefficient*(measureCoefficient+1)^6,rfl⟩

def stepCoefficient : Nat := stepDatum.val

theorem stepCoefficient_eq : stepCoefficient=
    FeaturePacketClockBound96.packetCoefficient*(measureCoefficient+1)^6 := stepDatum.property
attribute [local irreducible] stepCoefficient

theorem plus_one_le (C P : Nat) (hP : 1 ≤ P) : C*P+1 ≤ (C+1)*P := by nlinarith

theorem packet_clock_raw {q : Nat} (alphabet : Array (Nat × ℚ))
    (source : Array ((Fin q → Nat) × ℚ)) (j : Nat) (hj : j<q) :
    FeatureCoordinateTransition96.packetClock j (labels alphabet) (featuresAt j (labels alphabet)) [] []
      (CylinderRawInputProjection.input alphabet source) ≤
      stepCoefficient*((CylinderRawInputProjection.input alphabet source).length+1)^294930 := by
  let U := (CylinderRawInputProjection.input alphabet source).length+1
  let M := FeatureOuterMeasure96.measure j (labels alphabet) (featuresAt j (labels alphabet)) [] []
    (CylinderRawInputProjection.input alphabet source)
  have hM := measure_polynomial alphabet source j hj
  change M ≤ measureCoefficient*U^49155 at hM
  have hU : 1 ≤ U := by dsimp [U]; omega
  have hpow : 1 ≤ U^49155 := one_le_pow₀ hU
  have hm : M+1 ≤ (measureCoefficient+1)*U^49155 :=
    (Nat.add_le_add_right hM 1).trans (plus_one_le measureCoefficient (U^49155) hpow)
  have h := FeaturePacketClockBound96.clock_le j (labels alphabet) (featuresAt j (labels alphabet)) [] []
    (CylinderRawInputProjection.input alphabet source)
  change _ ≤ stepCoefficient*U^294930
  calc
    _ ≤ FeaturePacketClockBound96.packetCoefficient*(M+1)^6 := h
    _ ≤ FeaturePacketClockBound96.packetCoefficient*(((measureCoefficient+1)*U^49155)^6) :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hm 6)
    _ = (FeaturePacketClockBound96.packetCoefficient*(measureCoefficient+1)^6)*U^294930 := by
      rw [mul_pow,←pow_mul,Nat.mul_assoc]
    _ = _ := congrArg (fun C => C*U^294930) stepCoefficient_eq.symm

theorem state_raw {q : Nat} (alphabet : Array (Nat × ℚ))
    (source : Array ((Fin q → Nat) × ℚ)) (j : Nat) (hj : j ≤ q) :
    (states (labels alphabet) (CylinderRawInputProjection.input alphabet source) j).length ≤
      1000000000*((CylinderRawInputProjection.input alphabet source).length+1)^16385 := by
  let N := (CylinderRawInputProjection.input alphabet source).length
  let U := N+1
  let P := packetCap q alphabet
  obtain ⟨hq,ha,hbytes,halpha⟩ := raw_scalar_bounds alphabet source
  have hp := packet_le j q alphabet hj
  have hf := fields_le j q alphabet hj
  have hc := count_le j q alphabet hj
  have hy : (labels alphabet).length ≤ N := by rw [FeaturePrefixMeasurePolynomial96.labels_length]; exact ha
  have hbits : j.bits.length ≤ N :=
    (by rw [Nat.size_eq_bits_len]; exact Nat.size_le.mpr j.lt_two_pow_self : j.bits.length ≤ j).trans (hj.trans hq)
  have hm : FeatureStateSize96.measure j (labels alphabet) (featuresAt j (labels alphabet)) [] []
      (CylinderRawInputProjection.input alphabet source) ≤ 3*P+9*N+2 := by
    unfold FeatureStateSize96.measure
    simp only [List.length_nil]
    omega
  have hs := (FeatureStateSize96.stateWord_length_le j (labels alphabet) (featuresAt j (labels alphabet)) [] []
    (CylinderRawInputProjection.input alphabet source)).trans (Nat.mul_le_mul_left 300 hm)
  have hP := packetCap_polynomial alphabet source
  change P ≤ 400000*U^16385 at hP
  have hlinear : U ≤ U^16385 := le_self_pow (by dsimp [U]; omega) (by decide)
  change _ ≤ 1000000000*U^16385
  change (FeatureCoordinateTransition96.stateWord j (labels alphabet) (featuresAt j (labels alphabet)) [] []
    (CylinderRawInputProjection.input alphabet source)).length ≤ _
  exact hs.trans (by omega)

private noncomputable opaque commonDatum : {C : Nat // C=stepCoefficient+1000000000} :=
  ⟨stepCoefficient+1000000000,rfl⟩

def commonCoefficient : Nat := commonDatum.val

theorem commonCoefficient_eq : commonCoefficient=stepCoefficient+1000000000 := commonDatum.property
attribute [local irreducible] commonCoefficient

private noncomputable opaque finalDatum :
    {C : Nat // C=FeatureIterationSumBound96.coefficient*(commonCoefficient+1)} :=
  ⟨FeatureIterationSumBound96.coefficient*(commonCoefficient+1),rfl⟩

def coefficient : Nat := finalDatum.val

theorem coefficient_eq : coefficient=FeatureIterationSumBound96.coefficient*(commonCoefficient+1) := finalDatum.property
attribute [local irreducible] coefficient

def exponent : Nat := 294932

theorem power_product (A C U d : Nat) :
    A*U^2*(C*U^d)=(A*C)*U^(d+2) := by rw [pow_add]; ring

/-- The actual packet loader and complete coordinate loop have one fixed
polynomial clock in the original encoded production input. -/
theorem clock_le {q : Nat} (alphabet : Array (Nat × ℚ))
    (source : Array ((Fin q → Nat) × ℚ)) :
    FeatureIterationPacket96.clock q (alphabet.map Prod.fst).toList
      (CylinderRawInputProjection.input alphabet source) ≤
      coefficient*((CylinderRawInputProjection.input alphabet source).length+1)^exponent := by
  let raw := CylinderRawInputProjection.input alphabet source
  let U := raw.length+1
  let B := commonCoefficient*U^294930
  have hU : 1 ≤ U := by dsimp [U]; omega
  have hstepC : stepCoefficient ≤ commonCoefficient := by rw [commonCoefficient_eq]; omega
  have hstateC : 1000000000 ≤ commonCoefficient := by rw [commonCoefficient_eq]; omega
  have hstep (j : Nat) (hj : j<q) :
      FeatureCoordinateTransition96.packetClock j (labels alphabet) (featuresAt j (labels alphabet)) [] [] raw ≤ B :=
    (packet_clock_raw alphabet source j hj).trans (Nat.mul_le_mul_right _ hstepC)
  have hstate (j : Nat) (hj : j ≤ q) : (states (labels alphabet) raw j).length ≤ B := by
    have h := state_raw alphabet source j hj
    have hp : U^16385 ≤ U^294930 := pow_le_pow_right₀ hU (by decide)
    exact h.trans ((Nat.mul_le_mul_left 1000000000 hp).trans (Nat.mul_le_mul_right _ hstateC))
  have h := FeatureIterationSumBound96.clock_le q (labels alphabet) raw B hstep hstate
  have hq := (raw_scalar_bounds alphabet source).1
  have hqU : q+1 ≤ U := by dsimp [U,raw]; omega
  have hB : B+1 ≤ (commonCoefficient+1)*U^294930 := plus_one_le _ _ (one_le_pow₀ hU)
  change FeatureIterationPacket96.clock q (labels alphabet) raw ≤ coefficient*U^exponent
  calc
    _ ≤ FeatureIterationSumBound96.coefficient*(q+1)^2*(B+1) := h
    _ ≤ FeatureIterationSumBound96.coefficient*U^2*((commonCoefficient+1)*U^294930) :=
      Nat.mul_le_mul (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hqU 2)) hB
    _ = (FeatureIterationSumBound96.coefficient*(commonCoefficient+1))*U^294932 := power_product _ _ _ _
    _ = coefficient*U^exponent := congrArg (fun C => C*U^294932) coefficient_eq.symm

#print axioms clock_le
end CurrentAdditive.FeatureOuterRawClock96
