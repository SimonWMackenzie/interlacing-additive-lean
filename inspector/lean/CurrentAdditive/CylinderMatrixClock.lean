import CurrentAdditive.CylinderMatrixSerializer

/-! Explicit resource envelopes for the nested physical matrix writer. -/

namespace CurrentAdditive.CylinderMatrixClock

open EthInapproximability.CurrentPaper
open CurrentAdditive.CylinderFeatureCodec
open CurrentAdditive.CylinderRowSerializer
open CurrentAdditive.CylinderMatrixSerializer

def cellLengthCap : Nat :=
  max (encodedCell false).length (encodedCell true).length

theorem cell_length_le (b : Bool) : (encodedCell b).length ≤ cellLengthCap := by
  cases b
  · exact le_max_left _ _
  · exact le_max_right _ _

def rowSizeEnv (L : Nat) : Nat := 3 * L * (cellLengthCap + 1) + 1
def inputEnv (L : Nat) : Nat := 6 * L + 1
def frameEnv (L : Nat) : Nat := 3 * rowSizeEnv L + 1

noncomputable def timeEnv (L : Nat) : Nat :=
  (cellCostCap + frameLengthCap + 100) * (L + 1)^2 +
    2 * rowSizeEnv L + 2 +
    (UnaryBinaryEncoding.coefficient + 7) * (rowSizeEnv L + 1)^2

noncomputable def itemEnv (L : Nat) : Nat :=
  let F := SourceListMachineOuterFramed.itemMachine rowMachine
  20 * (inputEnv L + 1) * (inputEnv L + 1) + timeEnv L +
    4 * inputEnv L + frameEnv L +
    F.stackCount * (inputEnv L + timeEnv L * F.pushBound + 1) + 9

theorem encodedRow_length_le (bits : List Bool) (L : Nat)
    (h : bits.length ≤ L) : (encodedRow bits).length ≤ rowSizeEnv L := by
  have hc := SourceListEncoding.encode_map_length_le bits encodedCell
    cellLengthCap (by intro b _; exact cell_length_le b)
  unfold encodedRow at hc ⊢
  unfold rowSizeEnv
  nlinarith

theorem rawRow_length_le (bits : List Bool) (L : Nat)
    (h : bits.length ≤ L) : (rawRow bits).length ≤ inputEnv L := by
  have hc := SourceListEncoding.encode_map_length_le bits
    (fun b => [b]) 1 (by intro b _; simp)
  change (SourceListEncoding.encode (bits.map (fun b => [b]))).length ≤ inputEnv L
  unfold inputEnv
  nlinarith

theorem framed_length_le (bits : List Bool) (L : Nat)
    (h : bits.length ≤ L) :
    (SourceListMachineOuterFramed.framedOutput rowOutput (rawRow bits)).length ≤
      frameEnv L := by
  have hs := encodedRow_length_le bits L h
  have hn := EncodedGraph.natField_length_upper (encodedRow bits).length
  simp only [SourceListMachineOuterFramed.framedOutput, rowOutput,
    decodedBits_rawRow, List.length_append] at *
  unfold frameEnv
  omega

theorem framed_time_le (bits : List Bool) (L : Nat)
    (h : bits.length ≤ L) :
    SourceListMachineOuterFramed.framedBound rowOutput rowBound (rawRow bits) ≤
      timeEnv L := by
  have ht := rowClock_quadratic bits
  have hs := encodedRow_length_le bits L h
  have hp := Nat.pow_le_pow_left (show bits.length + 1 ≤ L + 1 by omega) 2
  have hq := Nat.pow_le_pow_left
    (show (encodedRow bits).length + 1 ≤ rowSizeEnv L + 1 by omega) 2
  have hc := Nat.mul_le_mul_left (cellCostCap + frameLengthCap + 100) hp
  have hd := Nat.mul_le_mul_left (UnaryBinaryEncoding.coefficient + 7) hq
  simp only [SourceListMachineOuterFramed.framedBound, rowOutput, rowBound,
    decodedBits_rawRow] at *
  unfold timeEnv
  omega

theorem matrixClock_le_count (rows : List (List Bool)) (L : Nat)
    (hrow : ∀ bits ∈ rows, bits.length ≤ L) :
    matrixClock rows ≤
      5 * rows.length.bits.length + 7 +
      (rows.length * itemEnv L +
        rows.length * (4 * rows.length.bits.length + 7)) +
      (4 * rows.length.bits.length +
        (EncodedCommunication.natField rows.length).length +
        rows.length * frameEnv L + 9) := by
  let xs := rawRows rows
  let F := SourceListMachineOuterFramed.itemMachine rowMachine
  have hout : ∀ x ∈ xs,
      (SourceListMachineOuterFramed.framedOutput rowOutput x).length ≤
        frameEnv L := by
    intro x hx
    obtain ⟨bits, hb, rfl⟩ := List.mem_map.mp hx
    exact framed_length_le bits L (hrow bits hb)
  have hitem : ∀ x ∈ xs,
      SourceListMachineWork.itemCost F x
        (SourceListMachineOuterFramed.framedOutput rowOutput x)
        (SourceListMachineOuterFramed.framedBound rowOutput rowBound x) ≤
          itemEnv L := by
    intro x hx
    obtain ⟨bits, hb, rfl⟩ := List.mem_map.mp hx
    exact SourceListMachineWork.itemCost_le_envelope F _ _ _
      (inputEnv L) (frameEnv L) (timeEnv L)
      (rawRow_length_le bits L (hrow bits hb))
      (framed_length_le bits L (hrow bits hb))
      (framed_time_le bits L (hrow bits hb))
  have h := SourceListMachineOuter.canonicalBound_le_count F xs
    (SourceListMachineOuterFramed.framedOutput rowOutput)
    (SourceListMachineOuterFramed.framedBound rowOutput rowBound)
    (itemEnv L) (frameEnv L) hitem hout
  simpa only [matrixClock, xs, F, rawRows, List.length_map] using h

def inputMeasure (rows : List (List Bool)) : Nat :=
  rows.length + (rows.map List.length).sum

noncomputable def matrixPoly (N : Nat) : Nat :=
  5*N+7 + (N*itemEnv N+N*(4*N+7)) +
    (4*N+(2*N+1)+N*frameEnv N+9)

theorem row_length_le_measure (rows : List (List Bool))
    (bits : List Bool) (h : bits ∈ rows) :
    bits.length ≤ inputMeasure rows := by
  have hm : bits.length ∈ rows.map List.length :=
    List.mem_map_of_mem h
  have hs : bits.length ≤ (rows.map List.length).sum :=
    List.le_sum_of_mem hm
  unfold inputMeasure
  omega

theorem matrixClock_polynomial (rows : List (List Bool)) :
    matrixClock rows ≤ matrixPoly (inputMeasure rows) := by
  let N := inputMeasure rows
  have hn : rows.length ≤ N := by simp [N, inputMeasure]
  have hbits : rows.length.bits.length ≤ N :=
    (UnaryBinaryEncoding.bits_length_le rows.length).trans hn
  have hfield : (EncodedCommunication.natField rows.length).length ≤
      2*N+1 := by
    have h := EncodedGraph.natField_length_upper rows.length
    omega
  have h := matrixClock_le_count rows N
    (fun bits hb => row_length_le_measure rows bits hb)
  have hitem := Nat.mul_le_mul_right (itemEnv N) hn
  have hframe := Nat.mul_le_mul_right (frameEnv N) hn
  have hquad := Nat.mul_le_mul hn (by omega :
    4 * rows.length.bits.length + 7 ≤ 4*N+7)
  unfold matrixPoly
  nlinarith

#print axioms matrixClock_polynomial

end CurrentAdditive.CylinderMatrixClock
