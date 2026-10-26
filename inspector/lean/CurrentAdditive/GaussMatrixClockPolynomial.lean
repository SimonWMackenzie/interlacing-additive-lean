import CurrentAdditive.GaussUniformMatrixActual
import CurrentAdditive.IndexedV2Clock

set_option maxHeartbeats 1000000

/-! Remove binary-header length operators from the fixed full-matrix clock.
The resulting envelopes are literal polynomial expressions in m,k,L,R,T. -/

namespace CurrentAdditive.GaussMatrixClockPolynomial

open CurrentAdditive.GaussNestedMatrixMap
open EthInapproximability.CurrentPaper

noncomputable def polyRowTime (M : BitMachine.Machine)
    (k L R T : Nat) : Nat :=
  5*k+7 + (k*cellEnvelope M L R T + k*(4*k+7)) +
    (4*k + (2*k+1) + k*(3*R+1) + 9)

noncomputable def polyRowFramed (M : BitMachine.Machine)
    (k L R T : Nat) : Nat :=
  polyRowTime M k L R T + 2*listBytes k R+2 +
    (UnaryBinaryEncoding.coefficient+7)*(listBytes k R+1)^2

noncomputable def polyRowEnvelope (M : BitMachine.Machine)
    (k L R T : Nat) : Nat :=
  let F := SourceListMachineOuterFramed.itemMachine (rowMachine M)
  let I := listBytes k L
  let O := 3*listBytes k R+1
  let Q := polyRowFramed M k L R T
  20*(I+1)*(I+1)+Q+4*I+O+
    F.stackCount*(I+Q*F.pushBound+1)+9

noncomputable def polyMatrixTime (M : BitMachine.Machine)
    (m k L R T : Nat) : Nat :=
  5*m+7 +
    (m*polyRowEnvelope M k L R T + m*(4*m+7)) +
    (4*m + (2*m+1) + m*(3*listBytes k R+1)+9)

private theorem bit_length_le (n : Nat) : n.bits.length ≤ n :=
  UnaryBinaryEncoding.bits_length_le n

private theorem nat_field_length_le (n : Nat) :
    (EncodedCommunication.natField n).length ≤ 2*n+1 :=
  EncodedGraph.natField_length_upper n

theorem rowTime_le (M : BitMachine.Machine) (k L R T : Nat) :
    rowTimeEnvelope M k L R T ≤ polyRowTime M k L R T := by
  have hb := bit_length_le k
  have hf := nat_field_length_le k
  unfold rowTimeEnvelope polyRowTime
  gcongr

theorem rowFramed_le (M : BitMachine.Machine) (k L R T : Nat) :
    rowFramedTime M k L R T ≤ polyRowFramed M k L R T := by
  unfold rowFramedTime polyRowFramed
  gcongr
  exact rowTime_le M k L R T

theorem rowEnvelope_le (M : BitMachine.Machine) (k L R T : Nat) :
    rowEnvelope M k L R T ≤ polyRowEnvelope M k L R T := by
  unfold rowEnvelope polyRowEnvelope
  dsimp only
  gcongr
  all_goals exact rowFramed_le M k L R T

theorem matrixTime_le (M : BitMachine.Machine) (m k L R T : Nat) :
    matrixTimeEnvelope M m k L R T ≤
      polyMatrixTime M m k L R T := by
  have hb := bit_length_le m
  have hf := nat_field_length_le m
  unfold matrixTimeEnvelope polyMatrixTime
  gcongr
  all_goals exact rowEnvelope_le M k L R T

theorem actual_pivot_matrix_poly {m k : Nat}
    (A : Matrix (Fin m) (Fin k) ℤ)
    (h01 : ∀ i j, A i j = 0 ∨ A i j = 1)
    (t : Nat) (ht : t < k)
    (hr : (CurrentAdditive.GaussControlTrace.after
      (fun i j => (A i j : ℚ)) t).r < m)
    (hc : (CurrentAdditive.GaussControlTrace.after
      (fun i j => (A i j : ℚ)) t).c < k)
    (pivot : Fin m)
    (hp : CurrentAdditive.SequentialTotality.pivotTyped
      (CurrentAdditive.GaussControlTrace.after
        (fun i j => (A i j : ℚ)) t).B
      (CurrentAdditive.GaussControlTrace.after
        (fun i j => (A i j : ℚ)) t).r
      ⟨(CurrentAdditive.GaussControlTrace.after
        (fun i j => (A i j : ℚ)) t).c, hc⟩ = some pivot) :
    let Aq : Fin m → Fin k → ℚ := fun i j => (A i j : ℚ)
    let s := CurrentAdditive.GaussControlTrace.after Aq t
    ∃ C : Nat,
      (matrixMachine GaussCellSubtractCall.machine).OutputsWithin
        (encodeNested
          (GaussAdaptedMatrixMap.adaptedMatrix
            s.B ⟨s.r, hr⟩ pivot ⟨s.c, hc⟩))
        (CurrentAdditive.GaussPhysical.encodeTypedMatrix
          (CurrentAdditive.GaussControlTrace.step s).B)
        (polyMatrixTime GaussCellSubtractCall.machine m k
          (GaussUniformMatrixActual.requestCap m)
          (GaussUniformMatrixActual.resultCap m)
          (C*(GaussUniformMatrixActual.requestCap m+1)^
            GaussUniformMatrixRun.exponent)) := by
  obtain ⟨C,h⟩ := GaussUniformMatrixActual.actual_pivot_matrix_bound
    A h01 t ht hr hc pivot hp
  refine ⟨C,?_⟩
  exact BitMachine.outputsWithin_mono _ h
    (matrixTime_le GaussCellSubtractCall.machine m k
      (GaussUniformMatrixActual.requestCap m)
      (GaussUniformMatrixActual.resultCap m)
      (C*(GaussUniformMatrixActual.requestCap m+1)^
        GaussUniformMatrixRun.exponent))

#print axioms matrixTime_le
#print axioms actual_pivot_matrix_poly

end CurrentAdditive.GaussMatrixClockPolynomial
