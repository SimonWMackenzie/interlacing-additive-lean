import CurrentAdditive.FeatureBoundedExtension64

/-! A single uniform polynomial envelope for the complete descriptor
extension, including every physically cleared stack. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 600000
namespace CurrentAdditive.FeatureExtensionPolynomial64
open EthInapproximability.CurrentPaper
open CurrentAdditive.FeatureBoundedExtension64
open CurrentAdditive.FeatureExtensionCompose64

noncomputable def rawCoefficient : Nat :=
  10*(UnaryBinaryEncoding.coefficient+100)+9

noncomputable def bankCoefficient : Nat :=
  1+BitMachineStackGrowth.perStep FeaturePairRaw64.program*rawCoefficient

noncomputable def appendCoefficient : Nat :=
  2*bankCoefficient+20+
    V2ItemFrameClock.coefficient*(10*bankCoefficient+2)^2

noncomputable def firstCoefficient : Nat :=
  rawCoefficient+appendCoefficient+1

noncomputable def coefficient : Nat :=
  (1+48*BitMachineStackGrowth.perStep FeatureExtensionCompose64.program)*
    firstCoefficient+51

theorem clock_le (S : Fin 64 → List Bool) (j y : Nat)
    (c : List (Nat × Nat)) (body : List Bool) (N : Nat)
    (hbank : bankSize S ≤ N)
    (hprepared : FeaturePreparedCallback.preparedSize j y c ≤ N)
    (hraw : (raw j y c).length ≤ N)
    (hbody : body.length ≤ N)
    (hframed : (EncodedCommunication.natField (raw j y c).length ++ raw j y c).length ≤ N) :
    FeatureBoundedExtension64.clock S j y c body ≤ coefficient*(N+1)^4 := by
  let M := N+1
  have hM : 1 ≤ M := by dsimp [M]; omega
  have hNM : N ≤ M := by dsimp [M]; omega
  have hsq : M ≤ M^2 := le_self_pow hM (by decide)
  have hquad : M^2 ≤ M^4 := by nlinarith
  have hprep2 := Nat.pow_le_pow_left (hprepared.trans hNM) 2
  have hp := FeaturePairRaw64.clock_poly j y c
  have hpc : FeaturePairRaw64.clock j y c ≤ rawCoefficient*M^2 :=
    hp.trans (Nat.mul_le_mul_left _ hprep2)
  have hrc : rawCap S j y c ≤ bankCoefficient*M^2 := by
    have hmul := Nat.mul_le_mul_left
      (BitMachineStackGrowth.perStep FeaturePairRaw64.program) hpc
    unfold rawCap bankCoefficient
    nlinarith
  have hinner : (raw j y c).length+10*rawCap S j y c+1 ≤
      (10*bankCoefficient+2)*M^2 := by nlinarith
  have hinner2 := Nat.pow_le_pow_left hinner 2
  have hpoly : ((10*bankCoefficient+2)*M^2)^2 =
      (10*bankCoefficient+2)^2*M^4 := by ring
  rw [hpoly] at hinner2
  have hmul := Nat.mul_le_mul_left V2ItemFrameClock.coefficient hinner2
  have happend : appendClock S j y c body ≤ appendCoefficient*M^4 := by
    have hrc4 := hrc.trans (Nat.mul_le_mul_left bankCoefficient hquad)
    unfold appendClock appendCoefficient
    nlinarith
  have hfirst : firstClock S j y c body ≤ firstCoefficient*M^4 := by
    have hpc4 := hpc.trans (Nat.mul_le_mul_left rawCoefficient hquad)
    unfold firstClock firstCoefficient
    nlinarith
  have hlast := Nat.mul_le_mul_left
    (48*BitMachineStackGrowth.perStep FeatureExtensionCompose64.program) hfirst
  change FeatureBoundedExtension64.clock S j y c body ≤ coefficient*M^4
  unfold FeatureBoundedExtension64.clock coefficient
  nlinarith

#print axioms clock_le
end CurrentAdditive.FeatureExtensionPolynomial64
