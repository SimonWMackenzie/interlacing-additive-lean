import CurrentAdditive.DeterministicETHPhysicalDynamicBackend

/-! Uniform bounds for the charged physical square/estimator/comparator
pipeline, measured from the actual encoded rectangle and estimator clock. -/

namespace CurrentAdditive.DeterministicETHPhysicalSizeClock

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.EncodedCommunication
open CurrentAdditive.DeterministicETHPhysicalFixedBackend

theorem square_encoded_length_le (i : Instance) (hi : i.Valid) :
    (encodeInstance (square i)).length ≤
      40 * ((encodeInstance i).length+1)^2 := by
  let W := (encodeInstance i).length
  let S := Paper2.SquarePadding.side i.rows i.cols
  have hI := encodeInstance_length i
  have hS := Paper2.Unit4Shell.SquareWriter.side_le_two_sum
    (n := i.cols) hi.1
  have htable : i.table.length = i.rows * i.cols := hi.2.2
  have hc : 0 < i.cols := hi.2.1
  have hr : 0 < i.rows := hi.1
  have hrW : i.rows ≤ W := by
    have : i.rows ≤ i.rows*i.cols := Nat.le_mul_of_pos_right _ hc
    dsimp [W]
    omega
  have hcW : i.cols ≤ W := by
    have : i.cols ≤ i.rows*i.cols := Nat.le_mul_of_pos_left _ hr
    dsimp [W]
    omega
  have hSW : S ≤ 4*W := by
    dsimp [S] at *
    omega
  have hnfS := EncodedGraph.natField_length_upper S
  have hthr : (natField i.threshold).length ≤ W := by
    dsimp [W]
    simp only [encodeInstance, List.length_append]
    omega
  have hsquare : (encodeInstance (square i)).length =
      2*(natField S).length + (natField i.threshold).length + S^2 := by
    simp only [square, Paper2.ASquare.squareInstance,
      encodeInstance, List.length_append,
      MatrixMaterialization.rowMajor_length]
    ring
  rw [hsquare]
  have hpow : S^2 ≤ (4*W)^2 := Nat.pow_le_pow_left hSW 2
  have hWpos : 1 ≤ W+1 := by omega
  dsimp [W] at *
  nlinarith

theorem dynamic_backend_clock_le (i : Instance) (hi : i.Valid)
    (out : List Bool) (Te : ℕ) :
    CurrentAdditive.DeterministicETHPhysicalDynamicBackend.clock i out Te ≤
      (10^15+1000) *
        ((encodeInstance i).length + out.length + Te + 1)^12 := by
  let W := (encodeInstance i).length
  let O := out.length
  let X := W + O + Te + 1
  let s := square i
  let x := matrix s
  let h := natField i.threshold
  let w1 := encodeInstance s
  let w2 := EncodedComplexity.pair x h
  let w3 := EncodedComplexity.pair out h
  let w4 := EncodedComplexity.pair i.threshold.bits
    (EncodedComplexity.pair out [])
  let w5 := EncodedComplexity.pair h (EncodedComplexity.pair out [])
  let w6 := EncodedComplexity.pair h out
  have hX : 1 ≤ X := by dsimp [X]; omega
  have hX2 : X ≤ X^2 := by nlinarith
  have hX12 : X^2 ≤ X^12 := Nat.pow_le_pow_right hX (by norm_num)
  have hW : W+1 ≤ X := by dsimp [X]; omega
  have hW1 : w1.length ≤ 40*X^2 := by
    have hs := square_encoded_length_le i hi
    have hp := Nat.pow_le_pow_left hW 2
    exact hs.trans (Nat.mul_le_mul_left _ hp)
  have hH : h.length ≤ X := by
    have : h.length ≤ W := by
      dsimp [h, W]
      simp only [encodeInstance, List.length_append]
      omega
    omega
  have hbits : i.threshold.bits.length ≤ X := by
    have he := encodeInstance_length i
    dsimp [W] at *
    omega
  have hx : x.length ≤ w1.length := by
    dsimp [x, w1, matrix, s, square]
    simp only [AFront.Projection.matrixWord, encodeInstance, List.length_append]
    omega
  have hW2 : w2.length ≤ 82*X^2 := by
    dsimp [w2]
    rw [EncodedComplexity.pair_length]
    have h0 : 1 ≤ X^2 := by omega
    omega
  have hW3 : w3.length ≤ 4*X^2 := by
    dsimp [w3]
    rw [EncodedComplexity.pair_length]
    omega
  have hW4 : w4.length ≤ 6*X^2 := by
    dsimp [w4]
    simp only [EncodedComplexity.pair_length, List.length_nil]
    omega
  have hW5 : w5.length ≤ 6*X^2 := by
    dsimp [w5]
    simp only [EncodedComplexity.pair_length, List.length_nil]
    omega
  have hW6 : w6.length ≤ 4*X^2 := by
    dsimp [w6]
    rw [EncodedComplexity.pair_length]
    omega
  have hCmp : Paper2.CmpOwner.cmpTime h.length O ≤ 50*X^2 := by
    have hO : O ≤ X := by dsimp [O, X]; omega
    have hprod : (O+2)*(2*O+3) ≤ (X+2)*(2*X+3) :=
      Nat.mul_le_mul (by omega) (by omega)
    dsimp [Paper2.CmpOwner.cmpTime, Paper2.CmpOwner.outTime]
    nlinarith [hprod]
  have hSq := Paper2.ASquare.Post.fullBound_le i hi
  have hSq' : Paper2.ASquare.Post.fullBound i.rows i.cols i.threshold ≤
      10^15 * X^12 := by
    dsimp [W] at hW
    exact hSq.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hW 12))
  change Paper2.ASquare.Post.fullBound i.rows i.cols i.threshold +
    2*w1.length+2 +
    (3*(w1.length+1) + 2*w2.length+2 +
      (2*x.length+Te+2*O+6 + 2*w3.length+2 +
        (3*(w3.length+1) + 2*w4.length+2 +
          (2*i.threshold.bits.length+(4*i.threshold.bits.length+4)+
            2*h.length+6 + 2*w5.length+2 +
            (3*(w5.length+1) + 2*w6.length+2 +
              Paper2.CmpOwner.cmpTime h.length O))))) ≤
    (10^15+1000)*X^12
  have hX12' : 1 ≤ X^12 := Nat.one_le_pow _ _ hX
  omega

theorem dynamic_backend_clock_of_estimator_run
    (Me : BitMachine.Machine) (i : Instance) (hi : i.Valid)
    (out : List Bool) (Te : ℕ)
    (hMe : Me.OutputsWithin (matrix (square i)) out Te) :
    CurrentAdditive.DeterministicETHPhysicalDynamicBackend.clock i out Te ≤
      (10^15+1000) * (Me.pushBound+43)^12 *
        ((encodeInstance i).length + Te + 1)^24 := by
  let W := (encodeInstance i).length
  let Y := W + Te + 1
  have hY : 1 ≤ Y := by dsimp [Y]; omega
  have hY2 : Y ≤ Y^2 := by nlinarith
  have hW : W+1 ≤ Y := by dsimp [Y]; omega
  have hx : (matrix (square i)).length ≤ 40*Y^2 := by
    have hs := square_encoded_length_le i hi
    have hp := Nat.pow_le_pow_left hW 2
    have hmat : (matrix (square i)).length ≤
        (encodeInstance (square i)).length := by
      simp only [matrix, AFront.Projection.matrixWord, encodeInstance,
        List.length_append]
      omega
    exact hmat.trans (hs.trans (Nat.mul_le_mul_left _ hp))
  have hout := BitMachine.output_length_bound Me hMe
  have hTe : Te ≤ Y^2 := by dsimp [Y] at *; omega
  have hO : out.length ≤ (40+Me.pushBound)*Y^2 := by
    have hpush : Te*Me.pushBound ≤ Me.pushBound*Y^2 := by
      calc
        Te*Me.pushBound = Me.pushBound*Te := by ring
        _ ≤ Me.pushBound*Y^2 := Nat.mul_le_mul_left _ hTe
    calc
      out.length ≤ (matrix (square i)).length + Te*Me.pushBound := hout
      _ ≤ 40*Y^2 + Me.pushBound*Y^2 := Nat.add_le_add hx hpush
      _ = (40+Me.pushBound)*Y^2 := by ring
  have hX : W + out.length + Te + 1 ≤ (Me.pushBound+43)*Y^2 := by
    calc
      W + out.length + Te + 1 = Y + out.length := by dsimp [Y]; omega
      _ ≤ Y + (40+Me.pushBound)*Y^2 := Nat.add_le_add_left hO _
      _ ≤ Y^2 + (40+Me.pushBound)*Y^2 :=
        Nat.add_le_add_right hY2 _
      _ = (Me.pushBound+41)*Y^2 := by ring
      _ ≤ (Me.pushBound+43)*Y^2 := by nlinarith
  have hclock := dynamic_backend_clock_le i hi out Te
  have hpow := Nat.pow_le_pow_left hX 12
  calc
    CurrentAdditive.DeterministicETHPhysicalDynamicBackend.clock i out Te
        ≤ (10^15+1000) * (W + out.length + Te + 1)^12 := hclock
    _ ≤ (10^15+1000) * ((Me.pushBound+43)*Y^2)^12 :=
      Nat.mul_le_mul_left _ hpow
    _ = (10^15+1000) * (Me.pushBound+43)^12 * Y^24 := by
      simp only [mul_pow, ← pow_mul, Nat.mul_assoc]
    _ = (10^15+1000) * (Me.pushBound+43)^12 *
          ((encodeInstance i).length + Te + 1)^24 := rfl

theorem estimator_clock_le (i : Instance) (hi : i.Valid) (Ce Ee : ℕ) :
    Ce * ((matrix (square i)).length+1)^Ee ≤
      (Ce*41^Ee) * ((encodeInstance i).length+1)^(2*Ee) := by
  let X := (encodeInstance i).length+1
  have hX : 1 ≤ X := by dsimp [X]; omega
  have hX2 : 1 ≤ X^2 := Nat.one_le_pow _ _ hX
  have hmat : (matrix (square i)).length ≤
      (encodeInstance (square i)).length := by
    simp only [matrix, AFront.Projection.matrixWord,
      encodeInstance, List.length_append]
    omega
  have hs := square_encoded_length_le i hi
  have hlen : (matrix (square i)).length+1 ≤ 41*X^2 := by
    have hs' : (encodeInstance (square i)).length ≤ 40*X^2 := hs
    omega
  have hp := Nat.pow_le_pow_left hlen Ee
  calc
    Ce * ((matrix (square i)).length+1)^Ee ≤
        Ce * (41*X^2)^Ee := Nat.mul_le_mul_left _ hp
    _ = (Ce*41^Ee)*X^(2*Ee) := by
      simp only [mul_pow, ← pow_mul, Nat.mul_assoc]
    _ = (Ce*41^Ee) * ((encodeInstance i).length+1)^(2*Ee) := rfl

private theorem mul_pow_reassoc (A B X n m : ℕ) :
    A * (B * X^n)^m = (A*B^m) * X^(m*n) := by
  calc
    A * (B * X^n)^m = A * (B^m * (X^n)^m) := by rw [mul_pow]
    _ = A * (B^m * X^(n*m)) := by rw [← pow_mul]
    _ = (A*B^m) * X^(m*n) := by rw [Nat.mul_comm n m]; ac_rfl

#print axioms square_encoded_length_le
#print axioms dynamic_backend_clock_le
#print axioms dynamic_backend_clock_of_estimator_run
#print axioms estimator_clock_le

end CurrentAdditive.DeterministicETHPhysicalSizeClock
