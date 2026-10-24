import CurrentAdditive.DeterministicETHPhysicalSizeClock
import CurrentAdditive.DeterministicETHPhysicalDynamicIndexedMain

/-! A single resource bound on the rectangle word, its producer clock, and
the estimator clock controls every charged physical handoff. The estimator's
actual run supplies the output-length bound used by the comparator. -/

namespace CurrentAdditive.DeterministicETHPhysicalPipelineClock

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.EncodedCommunication
open CurrentAdditive.DeterministicETHPhysicalFixedBackend
open CurrentAdditive.DeterministicETHPhysicalSizeClock

theorem dynamic_pipeline_clock_le
    (Me : BitMachine.Machine) (i : Instance) (hi : i.Valid)
    (out : List Bool) (Te tproducer Z : ℕ)
    (hMe : Me.OutputsWithin (matrix (square i)) out Te)
    (hZ : 1 ≤ Z)
    (hword : (encodeInstance i).length ≤ Z)
    (hest : Te ≤ Z) (hproducer : tproducer ≤ Z) :
    CurrentAdditive.DeterministicETHPhysicalDynamicIndexedMain.clock
      i out tproducer Te ≤
      (5 + (10^15+1000)*(Me.pushBound+43)^12*3^24) * Z^24 := by
  let W := (encodeInstance i).length
  have hZ24 : Z ≤ Z^24 := Nat.le_self_pow (by omega) Z
  have hthree : W+Te+1 ≤ 3*Z := by dsimp [W] at *; omega
  have hp := Nat.pow_le_pow_left hthree 24
  have hb := dynamic_backend_clock_of_estimator_run Me i hi out Te hMe
  have hback : CurrentAdditive.DeterministicETHPhysicalDynamicBackend.clock i out Te ≤
      (10^15+1000)*(Me.pushBound+43)^12*(3*Z)^24 :=
    hb.trans (Nat.mul_le_mul_left _ hp)
  have hsmall : tproducer + 2*W+2 ≤ 5*Z := by omega
  change tproducer + 2*W+2 +
    CurrentAdditive.DeterministicETHPhysicalDynamicBackend.clock i out Te ≤ _
  calc
    tproducer + 2*W+2 +
        CurrentAdditive.DeterministicETHPhysicalDynamicBackend.clock i out Te
        ≤ 5*Z + (10^15+1000)*(Me.pushBound+43)^12*(3*Z)^24 :=
      Nat.add_le_add hsmall hback
    _ ≤ 5*Z^24 + (10^15+1000)*(Me.pushBound+43)^12*(3*Z)^24 :=
      Nat.add_le_add_right (Nat.mul_le_mul_left 5 hZ24) _
    _ = (5 + (10^15+1000)*(Me.pushBound+43)^12*3^24)*Z^24 := by
      rw [mul_pow]
      ring

theorem dynamic_pipeline_table_bound
    (Me : BitMachine.Machine) (i : Instance) (hi : i.Valid)
    (out : List Bool) (Te tproducer : ℕ)
    (hMe : Me.OutputsWithin (matrix (square i)) out Te)
    (w : List Bool) (H B p d : ℕ)
    (hH : 1 ≤ H) (hB : 1 ≤ B)
    (hword : (encodeInstance i).length ≤ H*B^p*(w.length+1)^d)
    (hest : Te ≤ H*B^p*(w.length+1)^d)
    (hproducer : tproducer ≤ H*B^p*(w.length+1)^d) :
    CurrentAdditive.DeterministicETHPhysicalDynamicIndexedMain.clock
      i out tproducer Te ≤
      ((5 + (10^15+1000)*(Me.pushBound+43)^12*3^24)*H^24) *
        B^(24*p) * (w.length+1)^(24*d) := by
  let X := w.length+1
  let Z := H*B^p*X^d
  have hX : 1 ≤ X := by dsimp [X]; omega
  have hBp : 1 ≤ B^p := Nat.one_le_pow _ _ hB
  have hXd : 1 ≤ X^d := Nat.one_le_pow _ _ hX
  have hZ : 1 ≤ Z := by
    have hp : 0 < H*B^p*X^d :=
      Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) (by omega)
    dsimp [Z]
    omega
  have hc := dynamic_pipeline_clock_le Me i hi out Te tproducer Z hMe
    hZ hword hest hproducer
  calc
    CurrentAdditive.DeterministicETHPhysicalDynamicIndexedMain.clock
        i out tproducer Te
        ≤ (5 + (10^15+1000)*(Me.pushBound+43)^12*3^24)*Z^24 := hc
    _ = ((5 + (10^15+1000)*(Me.pushBound+43)^12*3^24)*H^24) *
          B^(24*p)*X^(24*d) := by
      dsimp [Z]
      simp only [mul_pow, ← pow_mul]
      ring
    _ = ((5 + (10^15+1000)*(Me.pushBound+43)^12*3^24)*H^24) *
          B^(24*p)*(w.length+1)^(24*d) := rfl

theorem dynamic_pipeline_from_word_producer
    (Me : BitMachine.Machine) (Ce Ee : ℕ)
    (i : Instance) (hi : i.Valid) (out : List Bool)
    (hMe : Me.OutputsWithin (matrix (square i)) out
      (Ce*((matrix (square i)).length+1)^Ee))
    (tproducer Z : ℕ)
    (hword : (encodeInstance i).length ≤ Z)
    (hproducer : tproducer ≤ Z) :
    CurrentAdditive.DeterministicETHPhysicalDynamicIndexedMain.clock
      i out tproducer (Ce*((matrix (square i)).length+1)^Ee) ≤
      (5 + (10^15+1000)*(Me.pushBound+43)^12*3^24) *
        (Z + Ce*41^Ee*(Z+1)^(2*Ee) + 1)^24 := by
  let Te := Ce*((matrix (square i)).length+1)^Ee
  let Z' := Z + Ce*41^Ee*(Z+1)^(2*Ee) + 1
  have hWZ : (encodeInstance i).length+1 ≤ Z+1 := by omega
  have hTe : Te ≤ Ce*41^Ee*(Z+1)^(2*Ee) := by
    have hc := estimator_clock_le i hi Ce Ee
    have hp := Nat.pow_le_pow_left hWZ (2*Ee)
    exact hc.trans (Nat.mul_le_mul_left _ hp)
  have hZ' : 1 ≤ Z' := by dsimp [Z']; omega
  have hW' : (encodeInstance i).length ≤ Z' := by dsimp [Z']; omega
  have hTe' : Te ≤ Z' := by dsimp [Z']; omega
  have hproducer' : tproducer ≤ Z' := by dsimp [Z']; omega
  exact dynamic_pipeline_clock_le Me i hi out Te tproducer Z' hMe
    hZ' hW' hTe' hproducer'

#print axioms dynamic_pipeline_clock_le
#print axioms dynamic_pipeline_table_bound
#print axioms dynamic_pipeline_from_word_producer

end CurrentAdditive.DeterministicETHPhysicalPipelineClock
