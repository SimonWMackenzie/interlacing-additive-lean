import CurrentAdditive.GaussCoefficientProgram

/-! Local decomposition of the canonical typed matrix in the coefficient
controller's frozen codec environment. -/

namespace CurrentAdditive.GaussCoefficientTyped

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

theorem member_length_le_fields (xs : List (List Bool))
    (word : List Bool) (hw : word ∈ xs) :
    word.length ≤ (SourceListEncoding.fields xs).length := by
  induction xs with
  | nil => simp at hw
  | cons x xs ih =>
      rcases List.mem_cons.mp hw with h | h
      · subst word
        simp only [SourceListEncoding.fields, List.length_append]
        omega
      · have hh := ih h
        simp only [SourceListEncoding.fields, List.length_append]
        omega

theorem member_length_le_encode (xs : List (List Bool))
    (word : List Bool) (hw : word ∈ xs) :
    word.length ≤ (SourceListEncoding.encode xs).length := by
  have h := member_length_le_fields xs word hw
  simp only [SourceListEncoding.encode, List.length_append]
  omega

theorem cellWord_length_le_matrix {m k : Nat}
    (B : Fin m → Fin k → ℚ) (i : Fin m) (j : Fin k) :
    (encodeRawRat (rawOfRat (B i j))).length ≤
      (encodeTypedMatrix B).length := by
  have hcell : encodeRawRat (rawOfRat (B i j)) ∈ cellWords B i := by
    rw [← cellWords_get B i j]
    exact List.getElem_mem (by simp [cellWords])
  have hrow : SourceListEncoding.encode (cellWords B i) ∈ rowWords B := by
    rw [← rowWords_get B i]
    exact List.getElem_mem (by simp [rowWords])
  have hc := member_length_le_encode (cellWords B i) _ hcell
  have hr := member_length_le_encode (rowWords B) _ hrow
  rw [encodeTypedMatrix_eq]
  omega

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
                (rowWords B).drop (i.val+1)) := by rw [← hc]
  · simp [rowWords, cellWords, List.length_take]

#print axioms typed_decomposition

end CurrentAdditive.GaussCoefficientTyped
