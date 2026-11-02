import CurrentAdditive.GenericFeaturePrefixMeasurePolynomial
import CurrentAdditive.GenericFeatureFinalStateProjection

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace CurrentAdditive.GenericFeaturePrefixStatePolynomial
open EthInapproximability.CurrentPaper
open FeatureOldDescriptorFrame96
open GenericFeaturePrefixByteBounds GenericFeaturePrefixMeasurePolynomial

def coefficient (D : Nat) := 1000000*(D+1)
abbrev exponent := packetExponent

/-- Actual serializer size of each generated prefix state. This scalar fact
has no execution claim; the loop proof separately charges real transitions. -/
theorem state_length (D : Nat) {q : Nat} (alphabet : Array (Nat × ℚ))
    (source : Array ((Fin q → Nat) × ℚ)) (j : Nat) (hj : j ≤ q) :
    (GenericFeatureFinalStateProjection.states D (labels alphabet)
      (CylinderRawInputProjection.input alphabet source) j).length ≤
      coefficient D*((CylinderRawInputProjection.input alphabet source).length+1)^exponent D := by
  let N := (CylinderRawInputProjection.input alphabet source).length
  let U := N+1
  let P := packetCap D q alphabet
  obtain ⟨hq,ha,hbytes,halpha⟩ := raw_scalar_bounds alphabet source
  have hp := packet_le D j q alphabet hj
  have hf := fields_le D j q alphabet hj
  have hc := count_le D j q alphabet hj
  have hy : (labels alphabet).length ≤ N := by rw [labels_length]; exact ha
  have hbits : j.bits.length ≤ N :=
    (by rw [Nat.size_eq_bits_len]; exact Nat.size_le.mpr j.lt_two_pow_self : j.bits.length ≤ j).trans (hj.trans hq)
  have hm : FeatureStateSize96.measure j (labels alphabet) (featurePrefix D j (labels alphabet)) [] []
      (CylinderRawInputProjection.input alphabet source) ≤ 3*P+9*N+2 := by
    unfold FeatureStateSize96.measure
    simp only [List.length_nil]
    omega
  have hs := (FeatureStateSize96.stateWord_length_le j (labels alphabet) (featurePrefix D j (labels alphabet)) [] []
    (CylinderRawInputProjection.input alphabet source)).trans (Nat.mul_le_mul_left 300 hm)
  have hP := packetCap_polynomial D alphabet source
  change P ≤ packetCoefficient D*U^packetExponent D at hP
  have hlinear : U ≤ U^packetExponent D := le_self_pow (by dsimp [U]; omega) (by unfold packetExponent; omega)
  change _ ≤ coefficient D*U^packetExponent D
  change (FeatureCoordinateTransition96.stateWord j (labels alphabet) (featurePrefix D j (labels alphabet)) [] []
    (CylinderRawInputProjection.input alphabet source)).length ≤ _
  apply hs.trans
  have hNU : N ≤ U^packetExponent D := (by dsimp [U]; omega : N ≤ U).trans hlinear
  dsimp only [coefficient,packetCoefficient] at hP ⊢
  have hone : 1 ≤ U^packetExponent D := one_le_pow₀ (by dsimp [U]; omega)
  nlinarith

#print axioms state_length
end CurrentAdditive.GenericFeaturePrefixStatePolynomial
