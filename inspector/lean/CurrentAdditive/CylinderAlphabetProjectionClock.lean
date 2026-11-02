import CurrentAdditive.CylinderAlphabetProjection

/-! Resource bound for the literal projection of alphabet labels. -/

namespace CurrentAdditive.CylinderAlphabetProjectionClock

open EthInapproximability.CurrentPaper
open CurrentAdditive.CylinderAlphabetProjection

def inputMeasure (alphabet : Array (Nat × ℚ)) : Nat :=
  (inputItems alphabet).length + SourceListEncoding.totalLength (inputItems alphabet)

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
    (SourceListMachineOuterFramed.framedOutput projectLabel item).length ≤
      frameEnv L := by
  have hp := BankFieldProjection.result_length (0 : Fin 2) item
  change (projectLabel item).length ≤ item.length at hp
  have hn := EncodedGraph.natField_length_upper (projectLabel item).length
  simp only [SourceListMachineOuterFramed.framedOutput,
    List.length_append] at *
  unfold frameEnv
  omega

theorem framed_time_le (item : List Bool) (L : Nat)
    (h : item.length ≤ L) :
    SourceListMachineOuterFramed.framedBound projectLabel
      (fun item => 8 * (item.length + 1)) item ≤ timeEnv L := by
  have hp := BankFieldProjection.result_length (0 : Fin 2) item
  change (projectLabel item).length ≤ item.length at hp
  have hpow := Nat.pow_le_pow_left (show
    (projectLabel item).length + 1 ≤ L + 1 by omega) 2
  have hcoef := Nat.mul_le_mul_left
    (UnaryBinaryEncoding.coefficient + 7) hpow
  have hfirst := Nat.mul_le_mul_left 8
    (show item.length + 1 ≤ L + 1 by omega)
  change 8 * (item.length + 1) + 2 * (projectLabel item).length + 2 +
      (UnaryBinaryEncoding.coefficient + 7) *
        ((projectLabel item).length + 1)^2 ≤ timeEnv L
  unfold timeEnv
  omega

theorem item_length_le_measure (alphabet : Array (Nat × ℚ))
    (item : List Bool) (h : item ∈ inputItems alphabet) :
    item.length ≤ inputMeasure alphabet := by
  have hm : item.length ∈ (inputItems alphabet).map List.length :=
    List.mem_map_of_mem h
  have hs := List.le_sum_of_mem hm
  unfold inputMeasure SourceListEncoding.totalLength
  omega

noncomputable def clockPoly (N : Nat) : Nat :=
  5*N+7 + (N*itemEnv N + N*(4*N+7)) +
    (4*N+(2*N+1)+N*frameEnv N+9)

theorem projection_clock_polynomial (alphabet : Array (Nat × ℚ)) :
    projectClock alphabet ≤ clockPoly (inputMeasure alphabet) := by
  let N := inputMeasure alphabet
  let xs := inputItems alphabet
  let F := SourceListMachineOuterFramed.itemMachine
    (BankFieldProjection.machine (0 : Fin 2))
  have hn : xs.length ≤ N := by simp [N, inputMeasure, xs]
  have hbits : xs.length.bits.length ≤ N :=
    (UnaryBinaryEncoding.bits_length_le xs.length).trans hn
  have hfield : (EncodedCommunication.natField xs.length).length ≤ 2*N+1 := by
    have h := EncodedGraph.natField_length_upper xs.length
    omega
  have hout : ∀ item ∈ xs,
      (SourceListMachineOuterFramed.framedOutput projectLabel item).length ≤
        frameEnv N := by
    intro item hi
    exact framed_length_le item N (item_length_le_measure alphabet item hi)
  have hitem : ∀ item ∈ xs,
      SourceListMachineWork.itemCost F item
        (SourceListMachineOuterFramed.framedOutput projectLabel item)
        (SourceListMachineOuterFramed.framedBound projectLabel
          (fun item => 8 * (item.length + 1)) item) ≤ itemEnv N := by
    intro item hi
    exact SourceListMachineWork.itemCost_le_envelope F _ _ _
      N (frameEnv N) (timeEnv N)
      (item_length_le_measure alphabet item hi)
      (framed_length_le item N (item_length_le_measure alphabet item hi))
      (framed_time_le item N (item_length_le_measure alphabet item hi))
  have hb := SourceListMachineOuter.canonicalBound_le_count F xs
    (SourceListMachineOuterFramed.framedOutput projectLabel)
    (SourceListMachineOuterFramed.framedBound projectLabel
      (fun item => 8 * (item.length + 1)))
    (itemEnv N) (frameEnv N) hitem hout
  have hcost := Nat.mul_le_mul_right (itemEnv N) hn
  have hframe := Nat.mul_le_mul_right (frameEnv N) hn
  have hquad := Nat.mul_le_mul hn (by omega :
    4 * xs.length.bits.length + 7 ≤ 4*N+7)
  unfold clockPoly
  change projectClock alphabet ≤
    5*N+7 + (N*itemEnv N+N*(4*N+7)) +
      (4*N+(2*N+1)+N*frameEnv N+9)
  change projectClock alphabet ≤
    5*xs.length.bits.length+7 +
      (xs.length*itemEnv N+xs.length*(4*xs.length.bits.length+7)) +
      (4*xs.length.bits.length+
        (EncodedCommunication.natField xs.length).length+
        xs.length*frameEnv N+9) at hb
  nlinarith

#print axioms projection_clock_polynomial

end CurrentAdditive.CylinderAlphabetProjectionClock
