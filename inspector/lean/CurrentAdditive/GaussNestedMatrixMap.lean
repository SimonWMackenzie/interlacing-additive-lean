import CurrentAdditive.GaussPivotPacketJoin
import EthInapproximability.CurrentPaper.SourceListMachineOuterFramed
import CurrentAdditive.GaussCellSpec
import EthInapproximability.CurrentPaper.SourceListMachineWork

set_option maxHeartbeats 1000000

/-!
A physical two-level V2 matrix writer.  Every input row is itself a counted
V2 list of cell-operation packets.  The inherited fixed outer controller
visits the rows; its callback is another fixed controller that visits every
cell and executes the supplied *fixed* cell machine.  Both controllers write
the canonical count and length fields.  Thus the output is the actual full
row-major matrix packet, with no semantic list map used as a machine step.
-/

namespace CurrentAdditive.GaussNestedMatrixMap

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.SourceListMachineOuterFramed

def encodeNested (rows : List (List (List Bool))) : List Bool :=
  SourceListEncoding.encode (rows.map SourceListEncoding.encode)

def mappedNested (f : List Bool → List Bool)
    (rows : List (List (List Bool))) : List Bool :=
  SourceListEncoding.encode
    (rows.map (fun row => SourceListEncoding.encode (row.map f)))

noncomputable def rowMachine (M : BitMachine.Machine) :
    BitMachine.Machine :=
  SourceListMachineOuterFramed.machine M

noncomputable def matrixMachine (M : BitMachine.Machine) :
    BitMachine.Machine :=
  SourceListMachineOuterFramed.machine (rowMachine M)

def rowResult (f : List Bool → List Bool) (row : List (List Bool)) :
    List Bool :=
  SourceListEncoding.encode (row.map f)

noncomputable def rowClock (M : BitMachine.Machine)
    (f : List Bool → List Bool) (bound : List Bool → Nat)
    (row : List (List Bool)) : Nat :=
  SourceListMachineOuter.canonicalBound
    (SourceListMachineOuterFramed.itemMachine M) row
    (SourceListMachineOuterFramed.framedOutput f)
    (SourceListMachineOuterFramed.framedBound f bound)

noncomputable def matrixClock (M : BitMachine.Machine)
    (f : List Bool → List Bool) (bound : List Bool → Nat)
    (rows : List (List (List Bool))) : Nat :=
  SourceListMachineOuter.canonicalBound
    (SourceListMachineOuterFramed.itemMachine (rowMachine M))
    (rows.map SourceListEncoding.encode)
    (SourceListMachineOuterFramed.framedOutput
      (fun encoded =>
        match SourceListEncoding.decode encoded with
        | some row => rowResult f row
        | none => []))
    (SourceListMachineOuterFramed.framedBound
      (fun encoded =>
        match SourceListEncoding.decode encoded with
        | some row => rowResult f row
        | none => [])
      (fun encoded =>
        match SourceListEncoding.decode encoded with
        | some row => rowClock M f bound row
        | none => 0))

theorem physical_nested_map (M : BitMachine.Machine)
    (f : List Bool → List Bool) (bound : List Bool → Nat)
    (rows : List (List (List Bool)))
    (hcell : ∀ row ∈ rows, ∀ cell ∈ row,
      M.OutputsWithin cell (f cell) (bound cell)) :
    (matrixMachine M).OutputsWithin (encodeNested rows)
      (mappedNested f rows) (matrixClock M f bound rows) := by
  let rowWords := rows.map SourceListEncoding.encode
  let rowF : List Bool → List Bool := fun encoded =>
    match SourceListEncoding.decode encoded with
    | some row => rowResult f row
    | none => []
  let rowB : List Bool → Nat := fun encoded =>
    match SourceListEncoding.decode encoded with
    | some row => rowClock M f bound row
    | none => 0
  have hr : ∀ x ∈ rowWords,
      (rowMachine M).OutputsWithin x (rowF x) (rowB x) := by
    intro x hx
    obtain ⟨row, hrow, rfl⟩ := List.mem_map.mp hx
    have hi := SourceListMachineOuterFramed.outputsWithin M row f bound
      (hcell row hrow)
    simpa [rowMachine, rowF, rowB, rowResult, rowClock,
      SourceListEncoding.decode_encode] using hi
  have hm := SourceListMachineOuterFramed.outputsWithin
    (rowMachine M) rowWords rowF rowB hr
  simpa [matrixMachine, encodeNested, mappedNested, matrixClock,
    rowWords, rowF, rowB, rowResult, List.map_map,
    Function.comp_def, SourceListEncoding.decode_encode] using hm

/-- The exact four-operand request for the `i,j` output entry of one clear
operation.  Its values come from the already swapped matrix. -/
def preparedCell {m k : Nat} (B : Fin m → Fin k → ℚ)
    (r : Fin m) (c : Fin k) (i : Fin m) (j : Fin k) : List Bool :=
  CurrentAdditive.GaussPhysical.cellPacket (decide (i = r))
    (CurrentAdditive.GaussPhysical.rawOfRat (B i j))
    (CurrentAdditive.GaussPhysical.rawOfRat (B i c))
    (CurrentAdditive.GaussPhysical.rawOfRat (B r j))
    (CurrentAdditive.GaussPhysical.rawOfRat (B r c))

def preparedMatrix {m k : Nat} (B : Fin m → Fin k → ℚ)
    (r : Fin m) (c : Fin k) : List (List (List Bool)) :=
  (List.finRange m).map fun i =>
    (List.finRange k).map (preparedCell B r c i)

theorem mapped_prepared_exact {m k : Nat}
    (B : Fin m → Fin k → ℚ) (r : Fin m) (c : Fin k)
    (f : List Bool → List Bool)
    (hf : ∀ i j, f (preparedCell B r c i j) =
      CurrentAdditive.CodeDCodec.encodeRawRat
        (CurrentAdditive.GaussPhysical.rawOfRat
          (CurrentAdditive.SequentialTotality.clearTyped B r c i j))) :
    mappedNested f (preparedMatrix B r c) =
      CurrentAdditive.GaussPhysical.encodeTypedMatrix
        (CurrentAdditive.SequentialTotality.clearTyped B r c) := by
  simp [mappedNested, preparedMatrix,
    CurrentAdditive.GaussPhysical.encodeTypedMatrix,
    CurrentAdditive.GaussPhysical.encodeRationalMatrix,
    CurrentAdditive.GaussPhysical.encodeMatrix,
    CurrentAdditive.GaussPhysical.encodeRow,
    CurrentAdditive.GaussPhysical.typedRows,
    CurrentAdditive.CodeDCodecV2.encodeItems,
    List.map_map, Function.comp_def, hf]

/-- Once the arithmetic callback is closed, the nested fixed machine writes
the exact canonical row-major bytes of the materialized clear operation. -/
theorem physical_clearTyped {m k : Nat}
    (B : Fin m → Fin k → ℚ) (r : Fin m) (c : Fin k)
    (M : BitMachine.Machine) (f : List Bool → List Bool)
    (bound : List Bool → Nat)
    (hcell : ∀ i j, M.OutputsWithin (preparedCell B r c i j)
      (f (preparedCell B r c i j))
      (bound (preparedCell B r c i j)))
    (hf : ∀ i j, f (preparedCell B r c i j) =
      CurrentAdditive.CodeDCodec.encodeRawRat
        (CurrentAdditive.GaussPhysical.rawOfRat
          (CurrentAdditive.SequentialTotality.clearTyped B r c i j))) :
    (matrixMachine M).OutputsWithin
      (encodeNested (preparedMatrix B r c))
      (CurrentAdditive.GaussPhysical.encodeTypedMatrix
        (CurrentAdditive.SequentialTotality.clearTyped B r c))
      (matrixClock M f bound (preparedMatrix B r c)) := by
  have hrow : ∀ row ∈ preparedMatrix B r c,
      ∀ cell ∈ row, M.OutputsWithin cell (f cell) (bound cell) := by
    intro row hrow cell hmem
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hrow
    obtain ⟨j, _, rfl⟩ := List.mem_map.mp hmem
    exact hcell i j
  simpa only [mapped_prepared_exact B r c f hf] using
    physical_nested_map M f bound (preparedMatrix B r c) hrow

/-! Uniform clock envelopes.  These are formulas in the row and column
counts and the maximum cell input, output and callback time.  Each level is
the actual inherited TM2 list controller, not a semantic map cost. -/

def listBytes (n L : Nat) : Nat := 3 * n * (L + 1) + 1

noncomputable def cellFramedTime (R T : Nat) : Nat :=
  T + 2 * R + 2 +
    (UnaryBinaryEncoding.coefficient + 7) * (R + 1)^2

noncomputable def cellEnvelope (M : BitMachine.Machine)
    (L R T : Nat) : Nat :=
  let F := SourceListMachineOuterFramed.itemMachine M
  20 * (L + 1) * (L + 1) + cellFramedTime R T +
    4 * L + (3 * R + 1) +
    F.stackCount * (L + cellFramedTime R T * F.pushBound + 1) + 9

noncomputable def rowTimeEnvelope (M : BitMachine.Machine)
    (k L R T : Nat) : Nat :=
  5 * k.bits.length + 7 +
    (k * cellEnvelope M L R T + k * (4 * k.bits.length + 7)) +
    (4 * k.bits.length +
      (EthInapproximability.CurrentPaper.EncodedCommunication.natField k).length +
      k * (3 * R + 1) + 9)

noncomputable def rowFramedTime (M : BitMachine.Machine)
    (k L R T : Nat) : Nat :=
  rowTimeEnvelope M k L R T + 2 * listBytes k R + 2 +
    (UnaryBinaryEncoding.coefficient + 7) * (listBytes k R + 1)^2

noncomputable def rowEnvelope (M : BitMachine.Machine)
    (k L R T : Nat) : Nat :=
  let F := SourceListMachineOuterFramed.itemMachine (rowMachine M)
  let I := listBytes k L
  let O := 3 * listBytes k R + 1
  let Q := rowFramedTime M k L R T
  20 * (I + 1) * (I + 1) + Q + 4 * I + O +
    F.stackCount * (I + Q * F.pushBound + 1) + 9

noncomputable def matrixTimeEnvelope (M : BitMachine.Machine)
    (m k L R T : Nat) : Nat :=
  5 * m.bits.length + 7 +
    (m * rowEnvelope M k L R T + m * (4 * m.bits.length + 7)) +
    (4 * m.bits.length +
      (EthInapproximability.CurrentPaper.EncodedCommunication.natField m).length +
      m * (3 * listBytes k R + 1) + 9)

private theorem framed_length_le (x : List Bool) (R : Nat)
    (h : x.length ≤ R) :
    (SourceListMachineOuterFramed.framedOutput id x).length ≤
      3 * R + 1 := by
  have hn := EthInapproximability.CurrentPaper.EncodedGraph.natField_length_upper x.length
  simp only [SourceListMachineOuterFramed.framedOutput,
    List.length_append, id_eq]
  omega

private theorem cell_item_cost_le (M : BitMachine.Machine)
    (f : List Bool → List Bool) (bound : List Bool → Nat)
    (x : List Bool) (L R T : Nat)
    (hx : x.length ≤ L) (hf : (f x).length ≤ R)
    (ht : bound x ≤ T) :
    SourceListMachineWork.itemCost
      (SourceListMachineOuterFramed.itemMachine M)
      x (SourceListMachineOuterFramed.framedOutput f x)
      (SourceListMachineOuterFramed.framedBound f bound x) ≤
      cellEnvelope M L R T := by
  have hlen : (SourceListMachineOuterFramed.framedOutput f x).length ≤
      3 * R + 1 := by
    simpa only [SourceListMachineOuterFramed.framedOutput,
      List.length_append] using
      framed_length_le (f x) R hf
  have htime : SourceListMachineOuterFramed.framedBound f bound x ≤
      cellFramedTime R T := by
    unfold SourceListMachineOuterFramed.framedBound cellFramedTime
    gcongr
  simpa [cellEnvelope] using
    SourceListMachineWork.itemCost_le_envelope
      (SourceListMachineOuterFramed.itemMachine M)
      x (SourceListMachineOuterFramed.framedOutput f x)
      (SourceListMachineOuterFramed.framedBound f bound x)
      L (3 * R + 1) (cellFramedTime R T) hx hlen htime

theorem rowClock_le (M : BitMachine.Machine)
    (f : List Bool → List Bool) (bound : List Bool → Nat)
    (row : List (List Bool)) (k L R T : Nat)
    (hk : row.length = k)
    (hin : ∀ x ∈ row, x.length ≤ L)
    (hout : ∀ x ∈ row, (f x).length ≤ R)
    (htime : ∀ x ∈ row, bound x ≤ T) :
    rowClock M f bound row ≤ rowTimeEnvelope M k L R T := by
  have hi : ∀ x ∈ row,
      SourceListMachineWork.itemCost
        (SourceListMachineOuterFramed.itemMachine M)
        x (SourceListMachineOuterFramed.framedOutput f x)
        (SourceListMachineOuterFramed.framedBound f bound x) ≤
      cellEnvelope M L R T := by
    intro x hx
    exact cell_item_cost_le M f bound x L R T
      (hin x hx) (hout x hx) (htime x hx)
  have ho : ∀ x ∈ row,
      (SourceListMachineOuterFramed.framedOutput f x).length ≤
      3 * R + 1 := by
    intro x hx
    simpa only [SourceListMachineOuterFramed.framedOutput,
      List.length_append] using framed_length_le (f x) R (hout x hx)
  have h := SourceListMachineOuter.canonicalBound_le_count
    (SourceListMachineOuterFramed.itemMachine M) row
    (SourceListMachineOuterFramed.framedOutput f)
    (SourceListMachineOuterFramed.framedBound f bound)
    (cellEnvelope M L R T) (3 * R + 1) hi ho
  simpa [rowClock, rowTimeEnvelope, hk] using h

theorem matrixClock_le (M : BitMachine.Machine)
    (f : List Bool → List Bool) (bound : List Bool → Nat)
    (rows : List (List (List Bool))) (m k L R T : Nat)
    (hm : rows.length = m)
    (hk : ∀ row ∈ rows, row.length = k)
    (hin : ∀ row ∈ rows, ∀ x ∈ row, x.length ≤ L)
    (hout : ∀ row ∈ rows, ∀ x ∈ row, (f x).length ≤ R)
    (htime : ∀ row ∈ rows, ∀ x ∈ row, bound x ≤ T) :
    matrixClock M f bound rows ≤
      matrixTimeEnvelope M m k L R T := by
  let rowWords := rows.map SourceListEncoding.encode
  let rowF : List Bool → List Bool := fun encoded =>
    match SourceListEncoding.decode encoded with
    | some row => rowResult f row
    | none => []
  let rowB : List Bool → Nat := fun encoded =>
    match SourceListEncoding.decode encoded with
    | some row => rowClock M f bound row
    | none => 0
  have hitem : ∀ x ∈ rowWords,
      SourceListMachineWork.itemCost
        (SourceListMachineOuterFramed.itemMachine (rowMachine M))
        x (SourceListMachineOuterFramed.framedOutput rowF x)
        (SourceListMachineOuterFramed.framedBound rowF rowB x) ≤
      rowEnvelope M k L R T := by
    intro x hx
    obtain ⟨row, hrow, rfl⟩ := List.mem_map.mp hx
    have hrowIn : (SourceListEncoding.encode row).length ≤
        listBytes k L := by
      have h := SourceListEncoding.encode_map_length_le row id L
        (fun y hy => hin row hrow y hy)
      simpa [listBytes, hk row hrow] using h
    have hrowOut : (rowResult f row).length ≤
        listBytes k R := by
      have h := SourceListEncoding.encode_map_length_le row f R
        (fun y hy => hout row hrow y hy)
      simpa [rowResult, listBytes, hk row hrow] using h
    have hrowClock := rowClock_le M f bound row k L R T
      (hk row hrow) (hin row hrow) (hout row hrow)
      (htime row hrow)
    have hrowFeq : rowF (SourceListEncoding.encode row) =
        rowResult f row := by
      dsimp [rowF]
      rw [SourceListEncoding.decode_encode]
    have hrowBeq : rowB (SourceListEncoding.encode row) =
        rowClock M f bound row := by
      dsimp [rowB]
      rw [SourceListEncoding.decode_encode]
    have hframedLen :
        (SourceListMachineOuterFramed.framedOutput rowF
          (SourceListEncoding.encode row)).length ≤
          3 * listBytes k R + 1 := by
      rw [SourceListMachineOuterFramed.framedOutput, hrowFeq]
      simpa only [SourceListMachineOuterFramed.framedOutput, id_eq] using
        framed_length_le (rowResult f row) (listBytes k R) hrowOut
    have hframedTime :
        SourceListMachineOuterFramed.framedBound rowF rowB
          (SourceListEncoding.encode row) ≤
          rowFramedTime M k L R T := by
      unfold SourceListMachineOuterFramed.framedBound rowFramedTime
      rw [hrowFeq, hrowBeq]
      gcongr
    have hi :=
      SourceListMachineWork.itemCost_le_envelope
        (SourceListMachineOuterFramed.itemMachine (rowMachine M))
        (SourceListEncoding.encode row)
        (SourceListMachineOuterFramed.framedOutput rowF
          (SourceListEncoding.encode row))
        (SourceListMachineOuterFramed.framedBound rowF rowB
          (SourceListEncoding.encode row))
        (listBytes k L) (3 * listBytes k R + 1)
        (rowFramedTime M k L R T)
        hrowIn hframedLen hframedTime
    simpa only [rowEnvelope] using hi
  have houtput : ∀ x ∈ rowWords,
      (SourceListMachineOuterFramed.framedOutput rowF x).length ≤
        3 * listBytes k R + 1 := by
    intro x hx
    obtain ⟨row, hrow, rfl⟩ := List.mem_map.mp hx
    have h := SourceListEncoding.encode_map_length_le row f R
      (fun y hy => hout row hrow y hy)
    have ho : (rowResult f row).length ≤ listBytes k R := by
      simpa [rowResult, listBytes, hk row hrow] using h
    have hrowFeq : rowF (SourceListEncoding.encode row) =
        rowResult f row := by
      dsimp [rowF]
      rw [SourceListEncoding.decode_encode]
    rw [SourceListMachineOuterFramed.framedOutput, hrowFeq]
    simpa only [SourceListMachineOuterFramed.framedOutput, id_eq] using
      framed_length_le (rowResult f row) (listBytes k R) ho
  have h := SourceListMachineOuter.canonicalBound_le_count
    (SourceListMachineOuterFramed.itemMachine (rowMachine M))
    rowWords (SourceListMachineOuterFramed.framedOutput rowF)
    (SourceListMachineOuterFramed.framedBound rowF rowB)
    (rowEnvelope M k L R T) (3 * listBytes k R + 1)
    hitem houtput
  change matrixClock M f bound rows ≤ _
  simpa only [matrixClock, matrixTimeEnvelope, rowWords,
    List.length_map, hm] using h

theorem prepared_clear_clock_le {m k : Nat}
    (B : Fin m → Fin k → ℚ) (r : Fin m) (c : Fin k)
    (M : BitMachine.Machine) (f : List Bool → List Bool)
    (bound : List Bool → Nat) (L R T : Nat)
    (hin : ∀ i j, (preparedCell B r c i j).length ≤ L)
    (hout : ∀ i j, (f (preparedCell B r c i j)).length ≤ R)
    (htime : ∀ i j, bound (preparedCell B r c i j) ≤ T) :
    matrixClock M f bound (preparedMatrix B r c) ≤
      matrixTimeEnvelope M m k L R T := by
  apply matrixClock_le M f bound (preparedMatrix B r c)
    m k L R T
  · simp [preparedMatrix]
  · intro row hrow
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hrow
    simp
  · intro row hrow x hx
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hrow
    obtain ⟨j, _, rfl⟩ := List.mem_map.mp hx
    exact hin i j
  · intro row hrow x hx
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hrow
    obtain ⟨j, _, rfl⟩ := List.mem_map.mp hx
    exact hout i j
  · intro row hrow x hx
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hrow
    obtain ⟨j, _, rfl⟩ := List.mem_map.mp hx
    exact htime i j

theorem physical_pivot_matrix {m k : Nat}
    (s : CurrentAdditive.GaussControlTrace.State m k)
    (hr : s.r < m) (hc : s.c < k)
    (pivot : Fin m)
    (hp : CurrentAdditive.SequentialTotality.pivotTyped
      s.B s.r ⟨s.c, hc⟩ = some pivot)
    (M : BitMachine.Machine) (f : List Bool → List Bool)
    (bound : List Bool → Nat)
    (hcell : ∀ i j,
      M.OutputsWithin
        (preparedCell
          (CurrentAdditive.SequentialTotality.swapTyped s.B ⟨s.r, hr⟩ pivot)
          ⟨s.r, hr⟩ ⟨s.c, hc⟩ i j)
        (f (preparedCell
          (CurrentAdditive.SequentialTotality.swapTyped s.B ⟨s.r, hr⟩ pivot)
          ⟨s.r, hr⟩ ⟨s.c, hc⟩ i j))
        (bound (preparedCell
          (CurrentAdditive.SequentialTotality.swapTyped s.B ⟨s.r, hr⟩ pivot)
          ⟨s.r, hr⟩ ⟨s.c, hc⟩ i j)))
    (hf : ∀ i j,
      f (preparedCell
          (CurrentAdditive.SequentialTotality.swapTyped s.B ⟨s.r, hr⟩ pivot)
          ⟨s.r, hr⟩ ⟨s.c, hc⟩ i j) =
      CurrentAdditive.CodeDCodec.encodeRawRat
        (CurrentAdditive.GaussPhysical.rawOfRat
          (CurrentAdditive.SequentialTotality.clearTyped
            (CurrentAdditive.SequentialTotality.swapTyped
              s.B ⟨s.r, hr⟩ pivot) ⟨s.r, hr⟩ ⟨s.c, hc⟩ i j))) :
    let Bswap := CurrentAdditive.SequentialTotality.swapTyped
      s.B ⟨s.r, hr⟩ pivot
    (matrixMachine M).OutputsWithin
      (encodeNested (preparedMatrix Bswap ⟨s.r, hr⟩ ⟨s.c, hc⟩))
      (CurrentAdditive.GaussPhysical.encodeTypedMatrix
        (CurrentAdditive.GaussControlTrace.step s).B)
      (matrixClock M f bound
        (preparedMatrix Bswap ⟨s.r, hr⟩ ⟨s.c, hc⟩)) := by
  dsimp only
  have h := physical_clearTyped
    (CurrentAdditive.SequentialTotality.swapTyped s.B ⟨s.r, hr⟩ pivot)
    ⟨s.r, hr⟩ ⟨s.c, hc⟩ M f bound hcell hf
  simpa [CurrentAdditive.GaussControlTrace.step, hr, hc, hp,
    CurrentAdditive.MaterializedGauss.materialize_eq] using h

#print axioms physical_nested_map
#print axioms mapped_prepared_exact
#print axioms physical_clearTyped
#print axioms rowClock_le
#print axioms matrixClock_le
#print axioms prepared_clear_clock_le
#print axioms physical_pivot_matrix

end CurrentAdditive.GaussNestedMatrixMap
