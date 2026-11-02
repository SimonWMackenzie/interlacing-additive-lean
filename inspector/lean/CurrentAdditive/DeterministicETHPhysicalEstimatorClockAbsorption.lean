import CurrentAdditive.DeterministicETHPhysicalPipelineClock

/-! A fixed polynomial-time estimator can be absorbed into the charged
dynamic physical pipeline. Only the rectangle word length and producer time
remain as source-side bounds. -/

namespace CurrentAdditive.DeterministicETHPhysicalEstimatorClockAbsorption

set_option maxHeartbeats 1000000

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.EncodedCommunication
open CurrentAdditive.DeterministicETHPhysicalPipelineClock
open CurrentAdditive.DeterministicETHPhysicalFixedBackend

theorem dynamic_pipeline_power_bound
    (Me : BitMachine.Machine) (Ce Ee : ℕ)
    (i : Instance) (hi : i.Valid) (out : List Bool)
    (hMe : Me.OutputsWithin (matrix (square i)) out
      (Ce*((matrix (square i)).length+1)^Ee))
    (tproducer Z : ℕ) (hZ : 1 ≤ Z)
    (hword : (encodeInstance i).length ≤ Z)
    (hproducer : tproducer ≤ Z) :
    CurrentAdditive.DeterministicETHPhysicalDynamicIndexedMain.clock
      i out tproducer (Ce*((matrix (square i)).length+1)^Ee) ≤
      ((5 + (10^15+1000)*(Me.pushBound+43)^12*3^24) *
        (Ce*41^Ee+1)^24 * 2^(24*(2*Ee+1))) *
        Z^(24*(2*Ee+1)) := by
  let A := Ce*41^Ee
  let e := 2*Ee
  let t := e+1
  let C := 5 + (10^15+1000)*(Me.pushBound+43)^12*3^24
  have h2Z : Z+1 ≤ 2*Z := by omega
  have hbase : 1 ≤ 2*Z := by omega
  have hpow : (Z+1)^e ≤ (2*Z)^e := Nat.pow_le_pow_left h2Z e
  have hpow' : (2*Z)^e ≤ (2*Z)^t :=
    Nat.pow_le_pow_right hbase (by dsimp [t]; omega)
  have hlin : Z+1 ≤ (2*Z)^t :=
    h2Z.trans (Nat.le_self_pow (by dsimp [t]; omega) (2*Z))
  have hinner : Z+A*(Z+1)^e+1 ≤ (A+1)*(2*Z)^t := by
    have hA : A*(Z+1)^e ≤ A*(2*Z)^t :=
      (Nat.mul_le_mul_left A hpow).trans (Nat.mul_le_mul_left A hpow')
    nlinarith
  have hmain := dynamic_pipeline_from_word_producer Me Ce Ee i hi out
    hMe tproducer Z hword hproducer
  have hpow24 := Nat.pow_le_pow_left hinner 24
  have hbound :
      C * (Z+A*(Z+1)^e+1)^24 ≤
        C * ((A+1)*(2*Z)^t)^24 := Nat.mul_le_mul_left C hpow24
  calc
    CurrentAdditive.DeterministicETHPhysicalDynamicIndexedMain.clock
        i out tproducer (Ce*((matrix (square i)).length+1)^Ee)
        ≤ C * (Z+A*(Z+1)^e+1)^24 := by simpa [C, A, e] using hmain
    _ ≤ C * ((A+1)*(2*Z)^t)^24 := hbound
    _ = (C*(A+1)^24*2^(24*t))*Z^(24*t) := by
      simp only [mul_pow, ← pow_mul]
      ring
    _ = ((5 + (10^15+1000)*(Me.pushBound+43)^12*3^24) *
          (Ce*41^Ee+1)^24 * 2^(24*(2*Ee+1))) *
          Z^(24*(2*Ee+1)) := rfl

theorem dynamic_pipeline_table_bound_of_estimator_poly
    (Me : BitMachine.Machine) (Ce Ee : ℕ)
    (i : Instance) (hi : i.Valid) (out : List Bool)
    (hMe : Me.OutputsWithin (matrix (square i)) out
      (Ce*((matrix (square i)).length+1)^Ee))
    (tproducer : ℕ) (w : List Bool) (H B p d : ℕ)
    (hH : 1 ≤ H) (hB : 1 ≤ B)
    (hword : (encodeInstance i).length ≤ H*B^p*(w.length+1)^d)
    (hproducer : tproducer ≤ H*B^p*(w.length+1)^d) :
    CurrentAdditive.DeterministicETHPhysicalDynamicIndexedMain.clock
      i out tproducer (Ce*((matrix (square i)).length+1)^Ee) ≤
      (((5 + (10^15+1000)*(Me.pushBound+43)^12*3^24) *
        (Ce*41^Ee+1)^24 * 2^(24*(2*Ee+1))) * H^(24*(2*Ee+1))) *
        B^(p*(24*(2*Ee+1))) *
        (w.length+1)^(d*(24*(2*Ee+1))) := by
  let X := w.length+1
  let q := 24*(2*Ee+1)
  let Z := H*B^p*X^d
  let C := (5 + (10^15+1000)*(Me.pushBound+43)^12*3^24) *
    (Ce*41^Ee+1)^24 * 2^q
  have hX : 1 ≤ X := by dsimp [X]; omega
  have hBp : 1 ≤ B^p := Nat.one_le_pow _ _ hB
  have hXd : 1 ≤ X^d := Nat.one_le_pow _ _ hX
  have hZ : 1 ≤ Z := by
    have hp : 0 < H*B^p*X^d :=
      Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) (by omega)
    dsimp [Z]
    omega
  have hc := dynamic_pipeline_power_bound Me Ce Ee i hi out hMe
    tproducer Z hZ hword hproducer
  calc
    CurrentAdditive.DeterministicETHPhysicalDynamicIndexedMain.clock
        i out tproducer (Ce*((matrix (square i)).length+1)^Ee)
        ≤ C*Z^q := by simpa [C, q] using hc
    _ = (C*H^q)*B^(p*q)*X^(d*q) := by
      dsimp [Z]
      simp only [mul_pow, ← pow_mul]
      ring
    _ = (((5 + (10^15+1000)*(Me.pushBound+43)^12*3^24) *
          (Ce*41^Ee+1)^24 * 2^(24*(2*Ee+1))) * H^(24*(2*Ee+1))) *
          B^(p*(24*(2*Ee+1))) *
          (w.length+1)^(d*(24*(2*Ee+1))) := rfl

#print axioms dynamic_pipeline_power_bound
#print axioms dynamic_pipeline_table_bound_of_estimator_poly

end CurrentAdditive.DeterministicETHPhysicalEstimatorClockAbsorption
