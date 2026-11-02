import CurrentAdditive.CylinderEmptyRowMachine

/-! All canonical retained-source lists have a polynomial physical clock for
the empty-cylinder row. -/

namespace CurrentAdditive.CylinderEmptyRowClock

open EthInapproximability.CurrentPaper
open CurrentAdditive.CylinderEmptyRowMachine
open CurrentAdditive.CylinderFeatureCodec
open CurrentAdditive.CodeDCodec

def frameLength : Nat :=
  (SourceListMachineOuterFramed.framedOutput
    (fun _ => encodeRawRat oneRat) []).length

noncomputable def frameTime : Nat :=
  SourceListMachineOuterFramed.framedBound
    (fun _ => encodeRawRat oneRat) (fun _ => 1) []

noncomputable def itemEnv (L : Nat) : Nat :=
  let F := SourceListMachineOuterFramed.itemMachine oneMachine
  20 * (L+1)*(L+1) + frameTime + 4*L + frameLength +
    F.stackCount*(L+frameTime*F.pushBound+1)+9

def inputMeasure (items : List (List Bool)) : Nat :=
  items.length + SourceListEncoding.totalLength items

noncomputable def clockPoly (N : Nat) : Nat :=
  5*N+7 + (N*itemEnv N+N*(4*N+7)) +
    (4*N+(2*N+1)+N*frameLength+9)

theorem item_length_le_measure (items : List (List Bool))
    (item : List Bool) (h : item ∈ items) :
    item.length ≤ inputMeasure items := by
  have hm : item.length ∈ items.map List.length := List.mem_map_of_mem h
  have hs := List.le_sum_of_mem hm
  unfold inputMeasure SourceListEncoding.totalLength
  omega

theorem rowClock_polynomial (items : List (List Bool)) :
    rowClock items ≤ clockPoly (inputMeasure items) := by
  let N := inputMeasure items
  let F := SourceListMachineOuterFramed.itemMachine oneMachine
  have hn : items.length ≤ N := by simp [N, inputMeasure]
  have hbits : items.length.bits.length ≤ N :=
    (UnaryBinaryEncoding.bits_length_le items.length).trans hn
  have hfield : (EncodedCommunication.natField items.length).length ≤ 2*N+1 := by
    have h := EncodedGraph.natField_length_upper items.length
    omega
  have hout : ∀ x ∈ items,
      (SourceListMachineOuterFramed.framedOutput
        (fun _ => encodeRawRat oneRat) x).length ≤ frameLength := by
    intro x _
    exact le_rfl
  have hitem : ∀ x ∈ items,
      SourceListMachineWork.itemCost F x
        (SourceListMachineOuterFramed.framedOutput
          (fun _ => encodeRawRat oneRat) x)
        (SourceListMachineOuterFramed.framedBound
          (fun _ => encodeRawRat oneRat) (fun _ => 1) x) ≤ itemEnv N := by
    intro x hx
    exact SourceListMachineWork.itemCost_le_envelope F _ _ _
      N frameLength frameTime
      (item_length_le_measure items x hx) le_rfl le_rfl
  have hb := SourceListMachineOuter.canonicalBound_le_count F items
    (SourceListMachineOuterFramed.framedOutput
      (fun _ => encodeRawRat oneRat))
    (SourceListMachineOuterFramed.framedBound
      (fun _ => encodeRawRat oneRat) (fun _ => 1))
    (itemEnv N) frameLength hitem hout
  have hcost := Nat.mul_le_mul_right (itemEnv N) hn
  have hframe := Nat.mul_le_mul_right frameLength hn
  have hquad := Nat.mul_le_mul hn (by omega :
    4*items.length.bits.length+7 ≤ 4*N+7)
  unfold clockPoly
  change rowClock items ≤
    5*N+7 + (N*itemEnv N+N*(4*N+7)) +
      (4*N+(2*N+1)+N*frameLength+9)
  change rowClock items ≤
    5*items.length.bits.length+7 +
      (items.length*itemEnv N+items.length*(4*items.length.bits.length+7)) +
      (4*items.length.bits.length+
        (EncodedCommunication.natField items.length).length+
        items.length*frameLength+9) at hb
  nlinarith

#print axioms rowClock_polynomial

end CurrentAdditive.CylinderEmptyRowClock
