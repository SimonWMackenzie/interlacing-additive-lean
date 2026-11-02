import CurrentAdditive.GaussAdaptedRequestLayout

/-! Index-tied byte prefixes for the physical m-by-k request scheduler. -/

namespace CurrentAdditive.GaussAdaptedPrefixIndex

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.EncodedCommunication

def cellPrefix {m k : Nat} (B : Fin m → Fin k → ℚ)
    (r pivot : Fin m) (c : Fin k) (i : Fin m) (j : Nat) : List Bool :=
  SourceListEncoding.fields
    (((List.finRange k).take j).map
      (GaussUniformCellAlgebra.adaptedSourceCellPacket B r pivot c i))

def rowPrefix {m k : Nat} (B : Fin m → Fin k → ℚ)
    (r pivot : Fin m) (c : Fin k) (i : Nat) : List Bool :=
  SourceListEncoding.fields
    (((List.finRange m).take i).map
      (GaussAdaptedRequestLayout.rowWord B r pivot c))

theorem cellPrefix_succ {m k : Nat} (B : Fin m → Fin k → ℚ)
    (r pivot i : Fin m) (c : Fin k) (j : Nat) (hj : j < k) :
    cellPrefix B r pivot c i (j+1) =
      cellPrefix B r pivot c i j ++
        natField (GaussUniformCellAlgebra.adaptedSourceCellPacket
          B r pivot c i ⟨j,hj⟩).length ++
        GaussUniformCellAlgebra.adaptedSourceCellPacket
          B r pivot c i ⟨j,hj⟩ := by
  have hlist : j < (List.finRange k).length := by simpa using hj
  rw [cellPrefix, List.take_succ_eq_append_getElem hlist]
  simp [cellPrefix, GaussAdaptedRequestLayout.fields_append,
    SourceListEncoding.fields, List.map_append, List.getElem_finRange,
    List.append_assoc]

theorem rowPrefix_succ {m k : Nat} (B : Fin m → Fin k → ℚ)
    (r pivot : Fin m) (c : Fin k) (i : Nat) (hi : i < m) :
    rowPrefix B r pivot c (i+1) =
      rowPrefix B r pivot c i ++
        natField (GaussAdaptedRequestLayout.rowWord
          B r pivot c ⟨i,hi⟩).length ++
        GaussAdaptedRequestLayout.rowWord B r pivot c ⟨i,hi⟩ := by
  have hlist : i < (List.finRange m).length := by simpa using hi
  rw [rowPrefix, List.take_succ_eq_append_getElem hlist]
  simp [rowPrefix, GaussAdaptedRequestLayout.fields_append,
    SourceListEncoding.fields, List.map_append, List.getElem_finRange,
    List.append_assoc]

theorem cellPrefix_final {m k : Nat} (B : Fin m → Fin k → ℚ)
    (r pivot i : Fin m) (c : Fin k) :
    cellPrefix B r pivot c i k =
      SourceListEncoding.fields
        (GaussAdaptedRequestLayout.cells B r pivot c i) := by
  change SourceListEncoding.fields
    (((List.finRange k).take k).map
      (GaussUniformCellAlgebra.adaptedSourceCellPacket B r pivot c i)) = _
  have hlen : (List.finRange k).length = k := by simp
  have htake : (List.finRange k).take k = List.finRange k := by
    have h := (List.take_length :
      (List.finRange k).take (List.finRange k).length = List.finRange k)
    simpa only [hlen] using h
  rw [htake]
  rfl

theorem rowPrefix_final {m k : Nat} (B : Fin m → Fin k → ℚ)
    (r pivot : Fin m) (c : Fin k) :
    rowPrefix B r pivot c m =
      SourceListEncoding.fields
        (GaussAdaptedRequestLayout.rowWords B r pivot c) := by
  change SourceListEncoding.fields
    (((List.finRange m).take m).map
      (GaussAdaptedRequestLayout.rowWord B r pivot c)) = _
  have hlen : (List.finRange m).length = m := by simp
  have htake : (List.finRange m).take m = List.finRange m := by
    have h := (List.take_length :
      (List.finRange m).take (List.finRange m).length = List.finRange m)
    simpa only [hlen] using h
  rw [htake]
  rfl

theorem encoded_adapted_final {m k : Nat} (B : Fin m → Fin k → ℚ)
    (r pivot : Fin m) (c : Fin k) :
    GaussNestedMatrixMap.encodeNested
      (GaussAdaptedMatrixMap.adaptedMatrix B r pivot c) =
      natField m ++ rowPrefix B r pivot c m := by
  rw [rowPrefix_final]
  have hrows :
      (GaussAdaptedMatrixMap.adaptedMatrix B r pivot c).map
        SourceListEncoding.encode =
        GaussAdaptedRequestLayout.rowWords B r pivot c := by
    simp [GaussAdaptedMatrixMap.adaptedMatrix,
      GaussAdaptedRequestLayout.rowWords,
      GaussAdaptedRequestLayout.rowWord,
      GaussAdaptedRequestLayout.cells]
  simp only [GaussNestedMatrixMap.encodeNested,
    SourceListEncoding.encode, hrows]
  simp [GaussAdaptedRequestLayout.rowWords]

#print axioms cellPrefix_succ
#print axioms rowPrefix_succ
#print axioms encoded_adapted_final

end CurrentAdditive.GaussAdaptedPrefixIndex
