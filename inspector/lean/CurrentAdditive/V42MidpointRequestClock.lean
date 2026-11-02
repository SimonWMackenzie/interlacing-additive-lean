import CurrentAdditive.V40MidpointRequestClock
import CurrentAdditive.V42RandomPermittedFamily
noncomputable section
namespace CurrentAdditive.V40MidpointRequest
open Paper2 Turing EthInapproximability.CurrentPaper BitMachineEncoding EncodedCommunication MinimumRatioContext EntryClockPoly
open CurrentAdditive.V42PublicSchedule
theorem v42_encoded_length (L k : ℕ)
    (f : Fin (sampleSide L k) → Fin (sampleSide L k) → Bool) :
    (encodeInstance (V42RandomPermittedFamily.instanceWord L k f)).length ≤
      7 * sampleSide L k ^ 2 + 3 := by
  have hp := V42RandomPermittedFamily.side_pos L k
  have hn := V42RandomPermittedFamily.numerator_le_entries L k
  have hB : B L k ≤ sampleSide L k ^ 2 := by unfold V42RandomPermittedFamily.numerator at hn; omega
  have hm : sampleSide L k ≤ sampleSide L k ^ 2 := by nlinarith
  have hdim := EncodedGraph.natField_length_upper (sampleSide L k)
  have hbudget := EncodedGraph.natField_length_upper (B L k)
  simp only [V42RandomPermittedFamily.instanceWord, encodeInstance, List.length_append,
    MatrixMaterialization.rowMajor_length]
  nlinarith

theorem v42_matrix_length (L k : ℕ)
    (f : Fin (sampleSide L k) → Fin (sampleSide L k) → Bool) :
    (V42RandomPermittedFamily.matrixWord L k f).length ≤ 5 * sampleSide L k ^ 2 + 2 := by
  have hp := V42RandomPermittedFamily.side_pos L k
  have hm : sampleSide L k ≤ sampleSide L k ^ 2 := by nlinarith
  have hdim := EncodedGraph.natField_length_upper (sampleSide L k)
  simp only [V42RandomPermittedFamily.matrixWord, AModel.matrixWord, List.length_append,
    MatrixMaterialization.rowMajor_length]
  nlinarith

theorem v42_public_clock_le (L k : ℕ)
    (f : Fin (sampleSide L k) → Fin (sampleSide L k) → Bool) :
    clock (B L k) k (encodeInstance (V42RandomPermittedFamily.instanceWord L k f)) ≤
      cap (sampleSide L k ^ 2) := by
  let T := sampleSide L k ^ 2
  have hn : 2*B L k+k ≤ 2*T := V42RandomPermittedFamily.numerator_le_entries L k
  have hb : B L k ≤ T := by omega
  have hk : k ≤ 2*T := by omega
  have hword := v42_encoded_length L k f
  have hmatrix : (AFront.Projection.matrixPart
      (encodeInstance (V42RandomPermittedFamily.instanceWord L k f))).length ≤ 5*T+2 := by
    rw [AFront.Projection.matrixPart_encodeInstance]
    exact v42_matrix_length L k f
  have hheader : (natField (2*B L k+k)).length ≤ 4*T+1 :=
    (EncodedGraph.natField_length_upper _).trans (by omega)
  have hf : fieldClock (B L k) k ≤
      invokeCap FieldM (2*T) ((UnaryBinaryEncoding.coefficient+10)*(2*T+1)^2) := by
    apply invoke_le
    · simpa using hn
    · gcongr
  have hm : matrixClock (encodeInstance (V42RandomPermittedFamily.instanceWord L k f)) ≤
      invokeCap MatrixM (7*T+3) (3*(7*T+4)) := by
    apply invoke_le
    · exact hword
    · omega
  unfold clock cap
  dsimp only [T] at *
  omega


theorem v42_request_length (L K : Nat)
    (f : Fin (sampleSide L K) → Fin (sampleSide L K) → Bool) :
    (natField (2*B L K+K)++V42RandomPermittedFamily.matrixWord L K f).length ≤ 9*sampleSide L K^2+3 := by
  have hn := V42RandomPermittedFamily.numerator_le_entries L K
  have hh := EncodedGraph.natField_length_upper (2*B L K+K)
  have hm := v42_matrix_length L K f
  simp only [List.length_append]
  dsimp only [V42RandomPermittedFamily.numerator] at hn
  omega

#print axioms v42_public_clock_le
end CurrentAdditive.V40MidpointRequest

