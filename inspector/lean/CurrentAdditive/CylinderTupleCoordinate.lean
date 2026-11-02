import CurrentAdditive.IndexedV2HeaderRun
import CurrentAdditive.CodeDCanonicalSourceV2

/-! Physical variable-coordinate lookup in a retained tuple's V2 counted
word.  It reuses the independently checked counted-field getter, with the
actual Fin-indexed tuple code and no full-product word enumeration. -/

namespace CurrentAdditive.CylinderTupleCoordinate

open EthInapproximability.CurrentPaper
open CurrentAdditive.GaussListContext

private theorem split_at {α : Type*} (xs : List α) (i : Nat)
    (hi : i < xs.length) :
    xs = xs.take i ++ xs[i] :: xs.drop (i+1) := by
  calc
    xs = xs.take i ++ xs.drop i := (List.take_append_drop i xs).symm
    _ = xs.take i ++ xs[i] :: xs.drop (i+1) := by
      rw [List.drop_eq_getElem_cons hi]

theorem select_word (xs : List (List Bool)) (i : Nat)
    (hi : i < xs.length) :
    ∃ t ≤ 4 * xs.length.bits.length + 6 +
        IndexedFieldProgram.fieldCost (xs.take i ++ [xs[i]]),
      IndexedV2Program.run t
        (IndexedV2Program.initial (SourceListEncoding.encode xs) i) =
        ⟨none,
         IndexedV2Program.indexControl
           (SourceListMachineFields.coreControl (some true, false), none),
         IndexedFieldProgram.contents
           (SourceListEncoding.fields (xs.drop (i+1)))
           (List.replicate xs[i].length true) xs[i] 0⟩ := by
  have hsplit := split_at xs i hi
  obtain ⟨t, ht, hr⟩ := IndexedV2Program.select_v2
    (xs.take i) xs[i] (xs.drop (i+1))
  refine ⟨t, ?_, ?_⟩
  · rw [← hsplit] at ht
    simpa only [List.length_take, Nat.min_eq_left (Nat.le_of_lt hi)] using ht
  · rw [← hsplit] at hr
    simpa only [List.length_take, Nat.min_eq_left (Nat.le_of_lt hi)] using hr

theorem select_canonical_coordinate {q : Nat}
    (entry : (Fin q → Nat) × ℚ) (i : Fin q) :
    ∃ t ≤ 4 * q.bits.length + 6 +
        IndexedFieldProgram.fieldCost
          ((List.ofFn (fun j : Fin q => (entry.1 j).bits)).take i.val ++
            [(entry.1 i).bits]),
      (IndexedV2Program.run t
        (IndexedV2Program.initial
          (SourceListEncoding.encode
            (List.ofFn (fun j : Fin q => (entry.1 j).bits))) i.val)).stk 6 =
        (entry.1 i).bits := by
  let xs := List.ofFn (fun j : Fin q => (entry.1 j).bits)
  have hi : i.val < xs.length := by simp [xs, i.isLt]
  obtain ⟨t, ht, hr⟩ := select_word xs i.val hi
  refine ⟨t, ?_, ?_⟩
  · simpa [xs] using ht
  · rw [hr]
    simp [xs, IndexedFieldProgram.contents]

#print axioms select_canonical_coordinate

end CurrentAdditive.CylinderTupleCoordinate
