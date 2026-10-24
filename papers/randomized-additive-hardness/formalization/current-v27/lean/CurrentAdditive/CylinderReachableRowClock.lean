import CurrentAdditive.CylinderCoordinateRowClock
import CurrentAdditive.CylinderActualTupleRow

/-! A charged physical callback for each word of the actual source.  The
bound is expressed in the canonical coordinate fields of that source word. -/

namespace CurrentAdditive.CylinderReachableRowClock

open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open CurrentAdditive.GaussListContext
open CurrentAdditive.CylinderSourceTupleProjection
open CurrentAdditive.CylinderActualTupleRow
open CurrentAdditive.CylinderCoordinateEqualityCallback
open CurrentAdditive.CylinderCoordinateRowClock

theorem actual_member_selected_run_bounded {q : Nat}
    (source : Array ((Fin q → Nat) × ℚ))
    (outerPre : List (List Bool)) (word : List Bool)
    (outerSuffix : List (List Bool))
    (hmem : word ∈ tupleWords source)
    (i : Fin q) (y : Nat)
    (output context : List Bool) :
    ∃ entry ∈ source.toList,
      word = SourceListEncoding.encode
        (List.ofFn (fun j : Fin q => (entry.1 j).bits)) ∧
      let xs := List.ofFn (fun j : Fin q => (entry.1 j).bits)
      let S := (CylinderCoordinateRowRun.selected outerPre word outerSuffix
        output context i.val y.bits).stk
      ∃ (t : Nat) (vFinal : Control) (SFinal : Fin 32 → List Bool),
        t ≤ pairBound (xs.take i.val) (entry.1 i).bits
          (xs.drop (i.val + 1)) y.bits output ∧
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
  obtain ⟨t, v, T, ht, hr, ho, hc, hp⟩ :=
    canonical_selected_run_clock outerPre word outerSuffix
      (xs.take i.val) (entry.1 i).bits (xs.drop (i.val + 1))
      output context y.bits hword i.val hlen.symm
  refine ⟨entry, he, hw, t, v, T, ht, hr, ?_, hc, hp⟩
  have hpiece : coordinatePiece i.val y.bits word =
      [decide ((entry.1 i).bits = y.bits)] := by
    simp [coordinatePiece, hw, SourceListEncoding.decode_encode]
  simpa only [hpiece] using ho

#print axioms actual_member_selected_run_bounded

end CurrentAdditive.CylinderReachableRowClock
