import CurrentAdditive.GenericFeaturePacketClockBound
import CurrentAdditive.GenericFeaturePrefixMeasurePolynomial
import CurrentAdditive.GenericFeatureIterationSumBound
import CurrentAdditive.GenericFeaturePrefixStatePolynomial

/-! A fixed public polynomial bounds the actual coordinate iteration in the
original encoded weighted input. All intermediate list/count/byte bounds are
derived from its generated-prefix semantics, without an output-size premise. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
namespace CurrentAdditive.GenericFeatureOuterRawClock
open EthInapproximability.CurrentPaper
open GenericFeatureOldDescriptorFrame GenericFeatureOldDescriptorSemantics
open GenericFeatureGeneratedIteration GenericFeaturePrefixByteBounds GenericFeaturePrefixMeasurePolynomial

private noncomputable opaque stepDatum (D : Nat) :
    {C : Nat // C=GenericFeaturePacketClockBound.packetCoefficient D*(measureCoefficient D+1)^6} :=
  ⟨GenericFeaturePacketClockBound.packetCoefficient D*(measureCoefficient D+1)^6,rfl⟩

def stepCoefficient (D : Nat) : Nat := (stepDatum D).val

theorem stepCoefficient_eq (D : Nat) : stepCoefficient D=
    GenericFeaturePacketClockBound.packetCoefficient D*(measureCoefficient D+1)^6 := (stepDatum D).property
attribute [local irreducible] stepCoefficient

def stateRawCoefficient (D : Nat) := 1000000*(D+1)

theorem plus_one_le (C P : Nat) (hP : 1 ≤ P) : C*P+1 ≤ (C+1)*P := by nlinarith

theorem packet_clock_raw (D : Nat) {q : Nat} (alphabet : Array (Nat × ℚ))
    (source : Array ((Fin q → Nat) × ℚ)) (j : Nat) (hj : j<q) :
    GenericFeatureCoordinateTransition.packetClock D j (labels alphabet) (featuresAt D j (labels alphabet)) [] []
      (CylinderRawInputProjection.input alphabet source) ≤
      stepCoefficient D*((CylinderRawInputProjection.input alphabet source).length+1)^(measureExponent D*6) := by
  let U := (CylinderRawInputProjection.input alphabet source).length+1
  let M := GenericFeatureOuterMeasure.measure D j (labels alphabet) (featuresAt D j (labels alphabet)) [] []
    (CylinderRawInputProjection.input alphabet source)
  have hM := measure_polynomial D alphabet source j hj
  change M ≤ measureCoefficient D*U^measureExponent D at hM
  have hU : 1 ≤ U := by dsimp [U]; omega
  have hpow : 1 ≤ U^measureExponent D := one_le_pow₀ hU
  have hm : M+1 ≤ (measureCoefficient D+1)*U^measureExponent D :=
    (Nat.add_le_add_right hM 1).trans (plus_one_le (measureCoefficient D) (U^measureExponent D) hpow)
  have h := GenericFeaturePacketClockBound.clock_le D j (labels alphabet) (featuresAt D j (labels alphabet)) [] []
    (CylinderRawInputProjection.input alphabet source)
  change _ ≤ stepCoefficient D*U^(measureExponent D*6)
  calc
    _ ≤ GenericFeaturePacketClockBound.packetCoefficient D*(M+1)^6 := h
    _ ≤ GenericFeaturePacketClockBound.packetCoefficient D*(((measureCoefficient D+1)*U^measureExponent D)^6) :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hm 6)
    _ = (GenericFeaturePacketClockBound.packetCoefficient D*(measureCoefficient D+1)^6)*U^(measureExponent D*6) := by
      rw [mul_pow,←pow_mul,Nat.mul_assoc]
    _ = _ := congrArg (fun C => C*U^(measureExponent D*6)) (stepCoefficient_eq D).symm

theorem state_raw (D : Nat) {q : Nat} (alphabet : Array (Nat × ℚ))
    (source : Array ((Fin q → Nat) × ℚ)) (j : Nat) (hj : j ≤ q) :
    (states D (labels alphabet) (CylinderRawInputProjection.input alphabet source) j).length ≤
      stateRawCoefficient D*((CylinderRawInputProjection.input alphabet source).length+1)^packetExponent D := by
  exact GenericFeaturePrefixStatePolynomial.state_length D alphabet source j hj

private noncomputable opaque commonDatum (D : Nat) : {C : Nat // C=stepCoefficient D+stateRawCoefficient D} :=
  ⟨stepCoefficient D+stateRawCoefficient D,rfl⟩

def commonCoefficient (D : Nat) : Nat := (commonDatum D).val

theorem commonCoefficient_eq (D : Nat) : commonCoefficient D=stepCoefficient D+stateRawCoefficient D := (commonDatum D).property
attribute [local irreducible] commonCoefficient

private noncomputable opaque finalDatum (D : Nat) :
    {C : Nat // C=GenericFeatureIterationSumBound.coefficient D*(commonCoefficient D+1)} :=
  ⟨GenericFeatureIterationSumBound.coefficient D*(commonCoefficient D+1),rfl⟩

def coefficient (D : Nat) : Nat := (finalDatum D).val

theorem coefficient_eq (D : Nat) : coefficient D=GenericFeatureIterationSumBound.coefficient D*(commonCoefficient D+1) := (finalDatum D).property
attribute [local irreducible] coefficient

def exponent (D : Nat) : Nat := measureExponent D*6+2

theorem power_product (A C U d : Nat) :
    A*U^2*(C*U^d)=(A*C)*U^(d+2) := by rw [pow_add]; ring

/-- The actual packet loader and complete coordinate loop have one fixed
polynomial clock in the original encoded production input. -/
theorem clock_le (D : Nat) {q : Nat} (alphabet : Array (Nat × ℚ))
    (source : Array ((Fin q → Nat) × ℚ)) :
    GenericFeatureIterationPacket.clock D q (alphabet.map Prod.fst).toList
      (CylinderRawInputProjection.input alphabet source) ≤
      coefficient D*((CylinderRawInputProjection.input alphabet source).length+1)^exponent D := by
  let raw := CylinderRawInputProjection.input alphabet source
  let U := raw.length+1
  let B := commonCoefficient D*U^(measureExponent D*6)
  have hU : 1 ≤ U := by dsimp [U]; omega
  have hstepC : stepCoefficient D ≤ commonCoefficient D := by rw [commonCoefficient_eq]; omega
  have hstateC : stateRawCoefficient D ≤ commonCoefficient D := by rw [commonCoefficient_eq]; omega
  have hstep (j : Nat) (hj : j<q) :
      GenericFeatureCoordinateTransition.packetClock D j (labels alphabet) (featuresAt D j (labels alphabet)) [] [] raw ≤ B :=
    (packet_clock_raw D alphabet source j hj).trans (Nat.mul_le_mul_right _ hstepC)
  have hstate (j : Nat) (hj : j ≤ q) : (states D (labels alphabet) raw j).length ≤ B := by
    have h := state_raw D alphabet source j hj
    have hp : U^packetExponent D ≤ U^(measureExponent D*6) := pow_le_pow_right₀ hU (by unfold measureExponent packetExponent; omega)
    exact h.trans ((Nat.mul_le_mul_left (stateRawCoefficient D) hp).trans (Nat.mul_le_mul_right _ hstateC))
  have h := GenericFeatureIterationSumBound.clock_le D q (labels alphabet) raw B hstep hstate
  have hq := (raw_scalar_bounds alphabet source).1
  have hqU : q+1 ≤ U := by dsimp [U,raw]; omega
  have hB : B+1 ≤ (commonCoefficient D+1)*U^(measureExponent D*6) := plus_one_le _ _ (one_le_pow₀ hU)
  change GenericFeatureIterationPacket.clock D q (labels alphabet) raw ≤ coefficient D*U^exponent D
  calc
    _ ≤ GenericFeatureIterationSumBound.coefficient D*(q+1)^2*(B+1) := h
    _ ≤ GenericFeatureIterationSumBound.coefficient D*U^2*((commonCoefficient D+1)*U^(measureExponent D*6)) :=
      Nat.mul_le_mul (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hqU 2)) hB
    _ = (GenericFeatureIterationSumBound.coefficient D*(commonCoefficient D+1))*U^(measureExponent D*6+2) := power_product _ _ _ _
    _ = coefficient D*U^exponent D := congrArg (fun C => C*U^(measureExponent D*6+2)) (coefficient_eq D).symm

#print axioms clock_le
end CurrentAdditive.GenericFeatureOuterRawClock
