import CurrentAdditive.GaussUniformMatrixSupport

namespace CurrentAdditive.GaussInitialByteDimensions

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.EncodedCommunication

private theorem natField_nonempty (n : Nat) :
    1 ≤ (natField n).length := by
  simp only [natField, field_length]
  omega

theorem fields_length_ge_count (xs : List (List Bool)) :
    xs.length ≤ (SourceListEncoding.fields xs).length := by
  induction xs with
  | nil => simp [SourceListEncoding.fields]
  | cons x xs ih =>
      have hn := natField_nonempty x.length
      simp only [SourceListEncoding.fields, List.length_cons,
        List.length_append] at *
      omega

theorem encode_length_ge_count (xs : List (List Bool)) :
    xs.length ≤ (SourceListEncoding.encode xs).length := by
  have hf := fields_length_ge_count xs
  simp only [SourceListEncoding.encode, List.length_append]
  omega

theorem fields_length_ge_item (xs : List (List Bool))
    (x : List Bool) (hx : x ∈ xs) :
    x.length ≤ (SourceListEncoding.fields xs).length := by
  induction xs with
  | nil => simp at hx
  | cons y ys ih =>
      simp only [List.mem_cons] at hx
      simp only [SourceListEncoding.fields, List.length_append]
      rcases hx with rfl | hy
      · omega
      · have h := ih hy
        omega

theorem encode_length_ge_item (xs : List (List Bool))
    (x : List Bool) (hx : x ∈ xs) :
    x.length ≤ (SourceListEncoding.encode xs).length := by
  have hf := fields_length_ge_item xs x hx
  simp only [SourceListEncoding.encode, List.length_append]
  omega

theorem rows_le_initial_bytes {m k : Nat}
    (B : Fin m → Fin k → ℚ) :
    m ≤ (GaussPhysical.encodeTypedMatrix B).length := by
  have h := encode_length_ge_count
    ((GaussPhysical.typedRows B).map
      (fun row => GaussPhysical.encodeRow (row.map GaussPhysical.rawOfRat)))
  simpa [GaussPhysical.encodeTypedMatrix,
    GaussPhysical.encodeRationalMatrix,
    GaussPhysical.encodeMatrix,
    GaussPhysical.typedRows_length, List.length_map,
    CurrentAdditive.CodeDCodecV2.encodeItems,
    List.map_map, Function.comp_def] using h

theorem columns_le_initial_bytes {m k : Nat}
    (B : Fin m → Fin k → ℚ) (hm : 0 < m) :
    k ≤ (GaussPhysical.encodeTypedMatrix B).length := by
  let i : Fin m := ⟨0,hm⟩
  let row := (List.finRange k).map (B i)
  let rows := (GaussPhysical.typedRows B).map
    (fun r => GaussPhysical.encodeRow (r.map GaussPhysical.rawOfRat))
  have hi : i ∈ List.finRange m := List.mem_finRange i
  have hr : row ∈ GaussPhysical.typedRows B := by
    exact List.mem_map.mpr ⟨i,hi,rfl⟩
  have hre : GaussPhysical.encodeRow (row.map GaussPhysical.rawOfRat) ∈ rows :=
    List.mem_map.mpr ⟨row,hr,rfl⟩
  have hrow := encode_length_ge_count
    ((row.map GaussPhysical.rawOfRat).map
      CurrentAdditive.CodeDCodec.encodeRawRat)
  have houter := encode_length_ge_item rows
    (GaussPhysical.encodeRow (row.map GaussPhysical.rawOfRat)) hre
  have hk : k ≤ (GaussPhysical.encodeRow
      (row.map GaussPhysical.rawOfRat)).length := by
    simpa only [GaussPhysical.encodeRow,
      CurrentAdditive.CodeDCodecV2.encodeItems,
      List.length_map, row, List.length_finRange] using hrow
  have hmatrix : (SourceListEncoding.encode rows).length =
      (GaussPhysical.encodeTypedMatrix B).length := by
    simp [rows, GaussPhysical.encodeTypedMatrix,
      GaussPhysical.encodeRationalMatrix, GaussPhysical.encodeMatrix,
      CurrentAdditive.CodeDCodecV2.encodeItems,
      List.map_map, Function.comp_def]
  omega

#print axioms rows_le_initial_bytes
#print axioms columns_le_initial_bytes

end CurrentAdditive.GaussInitialByteDimensions
