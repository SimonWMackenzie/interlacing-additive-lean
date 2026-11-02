import CurrentAdditive.CylinderProductionProjection

/-! Polynomial clocks for the physical projections of actual V2 packets. -/

namespace CurrentAdditive.CylinderProductionProjectionClock

open EthInapproximability.CurrentPaper
open CurrentAdditive.CylinderProductionProjection

def inputMeasure (items : List (List Bool)) : Nat :=
  items.length + SourceListEncoding.totalLength items

def frameEnv (L : Nat) : Nat := 3 * L + 1

noncomputable def timeEnv (L : Nat) : Nat :=
  8 * (L + 1) + 2 * L + 2 +
    (UnaryBinaryEncoding.coefficient + 7) * (L + 1)^2

noncomputable def itemEnv (L : Nat) : Nat :=
  let F := SourceListMachineOuterFramed.itemMachine
    (BankFieldProjection.machine (0 : Fin 2))
  20 * (L + 1) * (L + 1) + timeEnv L + 4 * L + frameEnv L +
    F.stackCount * (L + timeEnv L * F.pushBound + 1) + 9

noncomputable def projectionClock (items : List (List Bool)) : Nat :=
  SourceListMachineOuter.canonicalBound
    (SourceListMachineOuterFramed.itemMachine
      (BankFieldProjection.machine (0 : Fin 2)))
    items (SourceListMachineOuterFramed.framedOutput projectWord)
    (SourceListMachineOuterFramed.framedBound projectWord
      (fun item => 8 * (item.length + 1)))

theorem framed_length_le (item : List Bool) (L : Nat)
    (h : item.length ≤ L) :
    (SourceListMachineOuterFramed.framedOutput projectWord item).length ≤
      frameEnv L := by
  have hp := BankFieldProjection.result_length (0 : Fin 2) item
  change (projectWord item).length ≤ item.length at hp
  have hn := EncodedGraph.natField_length_upper (projectWord item).length
  simp only [SourceListMachineOuterFramed.framedOutput,
    List.length_append] at *
  unfold frameEnv
  omega

theorem framed_time_le (item : List Bool) (L : Nat)
    (h : item.length ≤ L) :
    SourceListMachineOuterFramed.framedBound projectWord
      (fun item => 8 * (item.length + 1)) item ≤ timeEnv L := by
  have hp := BankFieldProjection.result_length (0 : Fin 2) item
  change (projectWord item).length ≤ item.length at hp
  have hpow := Nat.pow_le_pow_left (show
    (projectWord item).length + 1 ≤ L + 1 by omega) 2
  have hcoef := Nat.mul_le_mul_left
    (UnaryBinaryEncoding.coefficient + 7) hpow
  have hfirst := Nat.mul_le_mul_left 8
    (show item.length + 1 ≤ L + 1 by omega)
  change 8 * (item.length + 1) + 2 * (projectWord item).length + 2 +
      (UnaryBinaryEncoding.coefficient + 7) *
        ((projectWord item).length + 1)^2 ≤ timeEnv L
  unfold timeEnv
  omega

theorem item_length_le_measure (items : List (List Bool))
    (item : List Bool) (h : item ∈ items) :
    item.length ≤ inputMeasure items := by
  have hm : item.length ∈ items.map List.length :=
    List.mem_map_of_mem h
  have hs := List.le_sum_of_mem hm
  unfold inputMeasure SourceListEncoding.totalLength
  omega

noncomputable def clockPoly (N : Nat) : Nat :=
  5*N+7 + (N*itemEnv N + N*(4*N+7)) +
    (4*N+(2*N+1)+N*frameEnv N+9)

theorem projection_clock_polynomial (items : List (List Bool)) :
    projectionClock items ≤ clockPoly (inputMeasure items) := by
  let N := inputMeasure items
  let F := SourceListMachineOuterFramed.itemMachine
    (BankFieldProjection.machine (0 : Fin 2))
  have hn : items.length ≤ N := by simp [N, inputMeasure]
  have hbits : items.length.bits.length ≤ N :=
    (UnaryBinaryEncoding.bits_length_le items.length).trans hn
  have hfield : (EncodedCommunication.natField items.length).length ≤
      2*N+1 := by
    have h := EncodedGraph.natField_length_upper items.length
    omega
  have hout : ∀ item ∈ items,
      (SourceListMachineOuterFramed.framedOutput projectWord item).length ≤
        frameEnv N := by
    intro item hi
    exact framed_length_le item N (item_length_le_measure items item hi)
  have hitem : ∀ item ∈ items,
      SourceListMachineWork.itemCost F item
        (SourceListMachineOuterFramed.framedOutput projectWord item)
        (SourceListMachineOuterFramed.framedBound projectWord
          (fun item => 8 * (item.length + 1)) item) ≤ itemEnv N := by
    intro item hi
    exact SourceListMachineWork.itemCost_le_envelope F _ _ _
      N (frameEnv N) (timeEnv N)
      (item_length_le_measure items item hi)
      (framed_length_le item N (item_length_le_measure items item hi))
      (framed_time_le item N (item_length_le_measure items item hi))
  have hb := SourceListMachineOuter.canonicalBound_le_count F items
    (SourceListMachineOuterFramed.framedOutput projectWord)
    (SourceListMachineOuterFramed.framedBound projectWord
      (fun item => 8 * (item.length + 1)))
    (itemEnv N) (frameEnv N) hitem hout
  have hcost := Nat.mul_le_mul_right (itemEnv N) hn
  have hframe := Nat.mul_le_mul_right (frameEnv N) hn
  have hquad := Nat.mul_le_mul hn (by omega :
    4 * items.length.bits.length + 7 ≤ 4*N+7)
  unfold clockPoly
  change projectionClock items ≤
    5*N+7 + (N*itemEnv N+N*(4*N+7)) +
      (4*N+(2*N+1)+N*frameEnv N+9)
  change projectionClock items ≤
    5*items.length.bits.length+7 +
      (items.length*itemEnv N+items.length*(4*items.length.bits.length+7)) +
      (4*items.length.bits.length+
        (EncodedCommunication.natField items.length).length+
        items.length*frameEnv N+9) at hb
  nlinarith

theorem tupleClock_poly {q : Nat}
    (source : Array ((Fin q → Nat) × ℚ)) :
    tupleClock source ≤ clockPoly (inputMeasure (sourceItems source)) := by
  exact projection_clock_polynomial (sourceItems source)

theorem alphabetClock_poly (alphabet : Array (Nat × ℚ)) :
    alphabetClock alphabet ≤
      clockPoly (inputMeasure (alphabetItems alphabet)) := by
  exact projection_clock_polynomial (alphabetItems alphabet)

#print axioms tupleClock_poly
#print axioms alphabetClock_poly

end CurrentAdditive.CylinderProductionProjectionClock
