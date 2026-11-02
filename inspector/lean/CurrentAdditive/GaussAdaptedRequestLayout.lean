import CurrentAdditive.GaussRequestSupportLength

/-! Exact byte layout and prefix equations for the row-major adapted
request-list producer. These are semantic codec facts, not physical writes. -/

namespace CurrentAdditive.GaussAdaptedRequestLayout

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.EncodedCommunication

def cells {m k : Nat} (B : Fin m → Fin k → ℚ)
    (r pivot : Fin m) (c : Fin k) (i : Fin m) : List (List Bool) :=
  (List.finRange k).map
    (GaussUniformCellAlgebra.adaptedSourceCellPacket B r pivot c i)

def rowWord {m k : Nat} (B : Fin m → Fin k → ℚ)
    (r pivot : Fin m) (c : Fin k) (i : Fin m) : List Bool :=
  SourceListEncoding.encode (cells B r pivot c i)

def rowWords {m k : Nat} (B : Fin m → Fin k → ℚ)
    (r pivot : Fin m) (c : Fin k) : List (List Bool) :=
  (List.finRange m).map (rowWord B r pivot c)

theorem fields_append (xs ys : List (List Bool)) :
    SourceListEncoding.fields (xs ++ ys) =
      SourceListEncoding.fields xs ++ SourceListEncoding.fields ys := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simp [SourceListEncoding.fields, ih, List.append_assoc]

theorem fields_map {α : Type*} (xs : List α) (f : α → List Bool) :
    SourceListEncoding.fields (xs.map f) =
      ((xs.map fun x => natField (f x).length ++ f x).flatten) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simp [SourceListEncoding.fields, ih, List.append_assoc]

theorem rowWord_exact {m k : Nat} (B : Fin m → Fin k → ℚ)
    (r pivot : Fin m) (c : Fin k) (i : Fin m) :
    rowWord B r pivot c i =
      natField k ++ SourceListEncoding.fields (cells B r pivot c i) := by
  simp [rowWord, SourceListEncoding.encode, cells]

theorem encoded_adapted_exact {m k : Nat} (B : Fin m → Fin k → ℚ)
    (r pivot : Fin m) (c : Fin k) :
    GaussNestedMatrixMap.encodeNested
      (GaussAdaptedMatrixMap.adaptedMatrix B r pivot c) =
    natField m ++
      ((List.finRange m).map fun i =>
        natField (rowWord B r pivot c i).length ++
          rowWord B r pivot c i).flatten := by
  simp [GaussNestedMatrixMap.encodeNested,
    GaussAdaptedMatrixMap.adaptedMatrix,
    SourceListEncoding.encode, rowWord, cells, fields_map]

theorem row_body_prefix {m k : Nat} (B : Fin m → Fin k → ℚ)
    (r pivot : Fin m) (c : Fin k) (i : Fin m) (j : Nat) :
    SourceListEncoding.fields (cells B r pivot c i) =
      SourceListEncoding.fields ((cells B r pivot c i).take j) ++
      SourceListEncoding.fields ((cells B r pivot c i).drop j) := by
  rw [← fields_append, List.take_append_drop]

theorem outer_body_prefix {m k : Nat} (B : Fin m → Fin k → ℚ)
    (r pivot : Fin m) (c : Fin k) (i : Nat) :
    SourceListEncoding.fields (rowWords B r pivot c) =
      SourceListEncoding.fields ((rowWords B r pivot c).take i) ++
      SourceListEncoding.fields ((rowWords B r pivot c).drop i) := by
  rw [← fields_append, List.take_append_drop]

#print axioms encoded_adapted_exact
#print axioms row_body_prefix
#print axioms outer_body_prefix

end CurrentAdditive.GaussAdaptedRequestLayout
