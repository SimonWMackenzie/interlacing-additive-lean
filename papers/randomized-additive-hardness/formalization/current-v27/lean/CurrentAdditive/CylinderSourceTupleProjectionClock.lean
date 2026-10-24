import CurrentAdditive.CylinderSourceTupleProjection

/-! Resource bound for the literal projection of source labels. -/

namespace CurrentAdditive.CylinderSourceTupleProjectionClock

open EthInapproximability.CurrentPaper
open CurrentAdditive.CylinderSourceTupleProjection

def inputMeasure {q : Nat} (source : Array ((Fin q → Nat) × ℚ)) : Nat :=
  (inputItems source).length + SourceListEncoding.totalLength (inputItems source)

def frameEnv (L : Nat) : Nat := 3 * L + 1

noncomputable def timeEnv (L : Nat) : Nat :=
  8 * (L + 1) + 2 * L + 2 +
    (UnaryBinaryEncoding.coefficient + 7) * (L + 1)^2

noncomputable def itemEnv (L : Nat) : Nat :=
  let F := SourceListMachineOuterFramed.itemMachine
    (BankFieldProjection.machine (0 : Fin 2))
  20 * (L + 1) * (L + 1) + timeEnv L + 4 * L + frameEnv L +
    F.stackCount * (L + timeEnv L * F.pushBound + 1) + 9

theorem framed_length_le (item : List Bool) (L : Nat)
    (h : item.length ≤ L) :
    (SourceListMachineOuterFramed.framedOutput projectTuple item).length ≤
      frameEnv L := by
  have hp := BankFieldProjection.result_length (0 : Fin 2) item
  change (projectTuple item).length ≤ item.length at hp
  have hn := EncodedGraph.natField_length_upper (projectTuple item).length
  simp only [SourceListMachineOuterFramed.framedOutput,
    List.length_append] at *
  unfold frameEnv
  omega

theorem framed_time_le (item : List Bool) (L : Nat)
    (h : item.length ≤ L) :
    SourceListMachineOuterFramed.framedBound projectTuple
      (fun item => 8 * (item.length + 1)) item ≤ timeEnv L := by
  have hp := BankFieldProjection.result_length (0 : Fin 2) item
  change (projectTuple item).length ≤ item.length at hp
  have hpow := Nat.pow_le_pow_left (show
    (projectTuple item).length + 1 ≤ L + 1 by omega) 2
  have hcoef := Nat.mul_le_mul_left
    (UnaryBinaryEncoding.coefficient + 7) hpow
  have hfirst := Nat.mul_le_mul_left 8
    (show item.length + 1 ≤ L + 1 by omega)
  change 8 * (item.length + 1) + 2 * (projectTuple item).length + 2 +
      (UnaryBinaryEncoding.coefficient + 7) *
        ((projectTuple item).length + 1)^2 ≤ timeEnv L
  unfold timeEnv
  omega

theorem item_length_le_measure {q : Nat} (source : Array ((Fin q → Nat) × ℚ))
    (item : List Bool) (h : item ∈ inputItems source) :
    item.length ≤ inputMeasure source := by
  have hm : item.length ∈ (inputItems source).map List.length :=
    List.mem_map_of_mem h
  have hs := List.le_sum_of_mem hm
  unfold inputMeasure SourceListEncoding.totalLength
  omega

noncomputable def clockPoly (N : Nat) : Nat :=
  5*N+7 + (N*itemEnv N + N*(4*N+7)) +
    (4*N+(2*N+1)+N*frameEnv N+9)

theorem projection_clock_polynomial {q : Nat} (source : Array ((Fin q → Nat) × ℚ)) :
    projectClock source ≤ clockPoly (inputMeasure source) := by
  let N := inputMeasure source
  let xs := inputItems source
  let F := SourceListMachineOuterFramed.itemMachine
    (BankFieldProjection.machine (0 : Fin 2))
  have hn : xs.length ≤ N := by simp [N, inputMeasure, xs]
  have hbits : xs.length.bits.length ≤ N :=
    (UnaryBinaryEncoding.bits_length_le xs.length).trans hn
  have hfield : (EncodedCommunication.natField xs.length).length ≤ 2*N+1 := by
    have h := EncodedGraph.natField_length_upper xs.length
    omega
  have hout : ∀ item ∈ xs,
      (SourceListMachineOuterFramed.framedOutput projectTuple item).length ≤
        frameEnv N := by
    intro item hi
    exact framed_length_le item N (item_length_le_measure source item hi)
  have hitem : ∀ item ∈ xs,
      SourceListMachineWork.itemCost F item
        (SourceListMachineOuterFramed.framedOutput projectTuple item)
        (SourceListMachineOuterFramed.framedBound projectTuple
          (fun item => 8 * (item.length + 1)) item) ≤ itemEnv N := by
    intro item hi
    exact SourceListMachineWork.itemCost_le_envelope F _ _ _
      N (frameEnv N) (timeEnv N)
      (item_length_le_measure source item hi)
      (framed_length_le item N (item_length_le_measure source item hi))
      (framed_time_le item N (item_length_le_measure source item hi))
  have hb := SourceListMachineOuter.canonicalBound_le_count F xs
    (SourceListMachineOuterFramed.framedOutput projectTuple)
    (SourceListMachineOuterFramed.framedBound projectTuple
      (fun item => 8 * (item.length + 1)))
    (itemEnv N) (frameEnv N) hitem hout
  have hcost := Nat.mul_le_mul_right (itemEnv N) hn
  have hframe := Nat.mul_le_mul_right (frameEnv N) hn
  have hquad := Nat.mul_le_mul hn (by omega :
    4 * xs.length.bits.length + 7 ≤ 4*N+7)
  unfold clockPoly
  change projectClock source ≤
    5*N+7 + (N*itemEnv N+N*(4*N+7)) +
      (4*N+(2*N+1)+N*frameEnv N+9)
  change projectClock source ≤
    5*xs.length.bits.length+7 +
      (xs.length*itemEnv N+xs.length*(4*xs.length.bits.length+7)) +
      (4*xs.length.bits.length+
        (EncodedCommunication.natField xs.length).length+
        xs.length*frameEnv N+9) at hb
  nlinarith

#print axioms projection_clock_polynomial

end CurrentAdditive.CylinderSourceTupleProjectionClock
