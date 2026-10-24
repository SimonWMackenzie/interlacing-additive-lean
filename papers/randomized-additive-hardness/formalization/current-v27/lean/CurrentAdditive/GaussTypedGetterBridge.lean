import CurrentAdditive.GaussTypedPacket
import CurrentAdditive.GaussNestedGetterRun
import CurrentAdditive.GaussNestedGetterClock

set_option maxHeartbeats 1000000

/-! Instantiation of the fixed nested V2 getter on a canonical typed matrix. -/

namespace CurrentAdditive.GaussTypedGetterBridge

open CurrentAdditive.GaussPhysical
open CurrentAdditive.CodeDCodec
open EthInapproximability.CurrentPaper

def cellWords {m k : Nat} (B : Fin m → Fin k → ℚ) (i : Fin m) :
    List (List Bool) :=
  (List.finRange k).map (fun j => encodeRawRat (rawOfRat (B i j)))

def rowWords {m k : Nat} (B : Fin m → Fin k → ℚ) :
    List (List Bool) :=
  (List.finRange m).map (fun i => SourceListEncoding.encode (cellWords B i))

theorem encodeTypedMatrix_eq {m k : Nat} (B : Fin m → Fin k → ℚ) :
    encodeTypedMatrix B = SourceListEncoding.encode (rowWords B) := by
  simp [encodeTypedMatrix, encodeRationalMatrix, encodeMatrix, encodeRow,
    rowWords, cellWords, typedRows, CurrentAdditive.CodeDCodecV2.encodeItems,
    List.map_map, Function.comp_def]

theorem cellWords_get {m k : Nat} (B : Fin m → Fin k → ℚ)
    (i : Fin m) (j : Fin k) :
    (cellWords B i)[j.val]'(by simp [cellWords]) =
      encodeRawRat (rawOfRat (B i j)) := by
  simp [cellWords]

theorem rowWords_get {m k : Nat} (B : Fin m → Fin k → ℚ)
    (i : Fin m) :
    (rowWords B)[i.val]'(by simp [rowWords]) =
      SourceListEncoding.encode (cellWords B i) := by
  simp [rowWords]

theorem split_at {α : Type*} (xs : List α) (n : Nat) (hn : n < xs.length) :
    xs = xs.take n ++ xs[n] :: xs.drop (n+1) := by
  conv_lhs => rw [← List.take_append_drop n xs]
  rw [List.drop_eq_getElem_cons hn]

theorem typed_decomposition {m k : Nat} (B : Fin m → Fin k → ℚ)
    (i : Fin m) (j : Fin k) :
    let rows := rowWords B
    let cells := cellWords B i
    let rowPre := rows.take i.val
    let rowSuffix := rows.drop (i.val+1)
    let cellPre := cells.take j.val
    let cellSuffix := cells.drop (j.val+1)
    encodeTypedMatrix B =
        SourceListEncoding.encode
          (rowPre ++ SourceListEncoding.encode
            (cellPre ++ encodeRawRat (rawOfRat (B i j)) :: cellSuffix) :: rowSuffix) ∧
      rowPre.length = i.val ∧ cellPre.length = j.val := by
  dsimp only
  have hrlen : i.val < (rowWords B).length := by simp [rowWords]
  have hclen : j.val < (cellWords B i).length := by simp [cellWords]
  have hr := split_at (rowWords B) i.val hrlen
  have hc := split_at (cellWords B i) j.val hclen
  rw [rowWords_get] at hr
  rw [cellWords_get] at hc
  constructor
  · calc
      encodeTypedMatrix B = SourceListEncoding.encode (rowWords B) :=
        encodeTypedMatrix_eq B
      _ = SourceListEncoding.encode
            ((rowWords B).take i.val ++
              SourceListEncoding.encode (cellWords B i) ::
                (rowWords B).drop (i.val+1)) := congrArg _ hr
      _ = SourceListEncoding.encode
            ((rowWords B).take i.val ++
              SourceListEncoding.encode
                ((cellWords B i).take j.val ++
                  encodeRawRat (rawOfRat (B i j)) ::
                    (cellWords B i).drop (j.val+1)) ::
                (rowWords B).drop (i.val+1)) := by
          rw [← hc]
  · simp [rowWords, cellWords, List.length_take]

def getterClock {m k : Nat} (B : Fin m → Fin k → ℚ)
    (i : Fin m) (j : Fin k) : Nat :=
  let rowPre := (rowWords B).take i.val
  let rowSuffix := (rowWords B).drop (i.val+1)
  let cellPre := (cellWords B i).take j.val
  let cellSuffix := (cellWords B i).drop (j.val+1)
  let cell := encodeRawRat (rawOfRat (B i j))
  let row := SourceListEncoding.encode (cellPre ++ cell :: cellSuffix)
  let matrix := SourceListEncoding.encode (rowPre ++ row :: rowSuffix)
  (2 * rowPre.length + 5 +
    (2 * matrix.length + 5 +
      (4 * (rowPre ++ row :: rowSuffix).length.bits.length + 6 +
        GaussListContext.IndexedFieldProgram.fieldCost (rowPre ++ [row])))) + 1 +
  (2 * row.length + 5 +
    (4 * (cellPre ++ cell :: cellSuffix).length.bits.length + 6 +
      GaussListContext.IndexedFieldProgram.fieldCost (cellPre ++ [cell])))

/-- The checked two-stage physical getter, now on the exact typed matrix
encoding at row `i` and column `j`.  The input matrix remains on bank 8. -/
theorem typed_lookup_cell_and_matrix {m k : Nat}
    (B : Fin m → Fin k → ℚ) (i : Fin m) (j : Fin k) :
    ∃ t ≤ getterClock B i j,
      (GaussNestedGetter.run t
        (GaussNestedGetter.firstFrame
          (GaussNestedGetter.inputForeign j.val)
          (CylinderContextScanStep.initial
            (encodeTypedMatrix B) i.val))).stk 18 =
        encodeRawRat (rawOfRat (B i j)) ∧
      (GaussNestedGetter.run t
        (GaussNestedGetter.firstFrame
          (GaussNestedGetter.inputForeign j.val)
          (CylinderContextScanStep.initial
            (encodeTypedMatrix B) i.val))).stk 8 = encodeTypedMatrix B := by
  let rowPre := (rowWords B).take i.val
  let rowSuffix := (rowWords B).drop (i.val+1)
  let cellPre := (cellWords B i).take j.val
  let cellSuffix := (cellWords B i).drop (j.val+1)
  let cell := encodeRawRat (rawOfRat (B i j))
  have hd := typed_decomposition B i j
  dsimp only at hd
  obtain ⟨hm, hri, hcj⟩ := hd
  have h := GaussNestedGetter.nested_lookup_cell_and_matrix
    rowPre rowSuffix cellPre cellSuffix cell
  dsimp only at h
  obtain ⟨t, ht, hcell, hmatrix⟩ := h
  have hcfg :
      GaussNestedGetter.firstFrame
          (GaussNestedGetter.inputForeign j.val)
          (CylinderContextScanStep.initial (encodeTypedMatrix B) i.val) =
        GaussNestedGetter.firstFrame
          (GaussNestedGetter.inputForeign cellPre.length)
          (CylinderContextScanStep.initial
            (SourceListEncoding.encode
              (rowPre ++ SourceListEncoding.encode
                (cellPre ++ cell :: cellSuffix) :: rowSuffix)) rowPre.length) := by
    simp only [rowPre, rowSuffix, cellPre, cellSuffix, cell,
      hri, hcj, ← hm]
  refine ⟨t, ?_, ?_, ?_⟩
  · exact ht
  · rw [← hcfg] at hcell
    exact hcell
  · rw [← hcfg] at hmatrix
    exact hmatrix.trans hm.symm

theorem getterClock_cubic {m k : Nat}
    (B : Fin m → Fin k → ℚ) (i : Fin m) (j : Fin k) :
    getterClock B i j ≤ 120 * ((encodeTypedMatrix B).length + 1)^3 := by
  let rowPre := (rowWords B).take i.val
  let rowSuffix := (rowWords B).drop (i.val+1)
  let cellPre := (cellWords B i).take j.val
  let cellSuffix := (cellWords B i).drop (j.val+1)
  let cell := encodeRawRat (rawOfRat (B i j))
  have hm := (typed_decomposition B i j).1
  have h := GaussNestedGetterClock.clock_cubic
    rowPre rowSuffix cellPre cellSuffix cell
  dsimp only at h
  rw [← hm] at h
  simpa only [getterClock] using h

#print axioms typed_decomposition
#print axioms typed_lookup_cell_and_matrix
#print axioms getterClock_cubic

end CurrentAdditive.GaussTypedGetterBridge
