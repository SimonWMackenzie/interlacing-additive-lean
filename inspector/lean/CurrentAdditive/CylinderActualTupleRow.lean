import CurrentAdditive.CylinderCoordinateRowRun
import CurrentAdditive.CylinderSourceTupleProjection

/-!
Every selected word of the physically projected production source is a
canonical counted tuple.  This supplies the real-source premise for the
coordinate callback; arbitrary malformed words are not claimed to work.
-/

namespace CurrentAdditive.CylinderActualTupleRow

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open CurrentAdditive.GaussListContext
open CurrentAdditive.CylinderSourceTupleProjection
open CurrentAdditive.CylinderCoordinateRowRun
open CurrentAdditive.CylinderCoordinateEqualityCallback

theorem member_canonical_word {q : Nat}
    (source : Array ((Fin q → Nat) × ℚ))
    (word : List Bool) (hmem : word ∈ tupleWords source) :
    ∃ entry ∈ source.toList,
      word = SourceListEncoding.encode
        (List.ofFn (fun j : Fin q => (entry.1 j).bits)) := by
  obtain ⟨entry, he, hw⟩ := List.mem_map.mp hmem
  exact ⟨entry, he, hw.symm⟩

theorem canonical_tuple_split {q : Nat}
    (entry : (Fin q → Nat) × ℚ) (i : Fin q) :
    let xs := List.ofFn (fun j : Fin q => (entry.1 j).bits)
    xs = xs.take i.val ++ (entry.1 i).bits :: xs.drop (i.val + 1) ∧
    (xs.take i.val).length = i.val := by
  dsimp only
  let xs := List.ofFn (fun j : Fin q => (entry.1 j).bits)
  have hi : i.val < xs.length := by simp [xs, i.isLt]
  constructor
  · calc
      xs = xs.take i.val ++ xs.drop i.val :=
        (List.take_append_drop i.val xs).symm
      _ = xs.take i.val ++ (entry.1 i).bits :: xs.drop (i.val + 1) := by
        rw [List.drop_eq_getElem_cons hi]
        simp [xs]
  · simp [List.length_take]

def coordinatePiece (i : Nat) (symbol word : List Bool) : List Bool :=
  [decide ((SourceListEncoding.decode word).bind (fun xs => xs[i]?) =
    some symbol)]

theorem actual_member_selected_run {q : Nat}
    (source : Array ((Fin q → Nat) × ℚ))
    (outerPre : List (List Bool)) (word : List Bool)
    (outerSuffix : List (List Bool))
    (hmem : word ∈ tupleWords source)
    (i : Fin q) (y : Nat)
    (output context : List Bool) :
    ∃ entry ∈ source.toList,
      let xs := List.ofFn (fun j : Fin q => (entry.1 j).bits)
      let S := (selected outerPre word outerSuffix output context
        i.val y.bits).stk
      ∃ (t : Nat) (vFinal : Control)
        (SFinal SBefore : Fin 32 → List Bool),
        t ≤ getterBound (xs.take i.val) (entry.1 i).bits
            (xs.drop (i.val + 1)) + 1 +
            CylinderEqualityAppendCallback.callbackBound
              (entry.1 i).bits y.bits output +
            (∑ k : Fin 15, (SBefore (cleanBank k)).length) + 17 ∧
        run t
          ⟨some (.inl (.inl .scan)),
           getterControl (CylinderContextScanStep.copyControl ((), none)),
           S⟩ = ⟨none, vFinal, SFinal⟩ ∧
        SFinal 9 = output ++ coordinatePiece i.val y.bits word ∧
        (∀ k : Fin 15, SFinal (cleanBank k) = []) ∧
        (∀ k : Fin 32,
          k = 8 ∨ k = 10 ∨ k = 12 ∨ k = 13 ∨ k = 15 ∨ k = 16 →
            SFinal k = S k) := by
  dsimp only
  obtain ⟨entry, he, hw⟩ := member_canonical_word source word hmem
  let xs := List.ofFn (fun j : Fin q => (entry.1 j).bits)
  obtain ⟨hsplit, hlen⟩ := canonical_tuple_split entry i
  have hword : word = SourceListEncoding.encode
      (xs.take i.val ++ (entry.1 i).bits :: xs.drop (i.val + 1)) := by
    rw [← hsplit]
    exact hw
  have ht := canonical_selected_run outerPre word outerSuffix
    (xs.take i.val) (entry.1 i).bits (xs.drop (i.val + 1))
    output context y.bits hword i.val hlen.symm
  refine ⟨entry, he, ?_⟩
  have hpiece : coordinatePiece i.val y.bits word =
      [decide ((entry.1 i).bits = y.bits)] := by
    simp [coordinatePiece, hw, SourceListEncoding.decode_encode]
  simpa only [hpiece] using ht

#print axioms member_canonical_word
#print axioms canonical_tuple_split
#print axioms actual_member_selected_run

end CurrentAdditive.CylinderActualTupleRow
