import CurrentAdditive.CylinderActualTupleRow
import CurrentAdditive.SourceContextScheduler

/-!
The one-coordinate callback runs on every source word the fixed-source
scheduler can actually select from the physical production V2 projection.
The outer list and its output accumulator are retained with duplicate words.
-/

namespace CurrentAdditive.CylinderReachableRowCallback

open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open CurrentAdditive.GaussListContext
open CurrentAdditive.CylinderSourceTupleProjection
open CurrentAdditive.CylinderActualTupleRow
open CurrentAdditive.LargeContextListScheduler
open CurrentAdditive.CylinderCoordinateEqualityCallback

theorem reachable_run {q : Nat}
    (source : Array ((Fin q → Nat) × ℚ))
    (i : Fin q) (y : Nat) (initialOutput context : List Bool)
    (pre : List (List Bool)) (word : List Bool)
    (suffix : List (List Bool))
    (hSplit : pre ++ word :: suffix = tupleWords source) :
    let original := tupleWords source
    let piece := coordinatePiece i.val y.bits
    let output := initialOutput ++ joined piece pre
    let selected := LargeContextPreservingScan.frame
      (foreignBank output context suffix.length
        (CylinderCoordinateRowRun.pairExtra i.val y.bits))
      (⟨none,
       CylinderContextScanStep.getterControl
         (PreservingV2Program.v2Control
           (IndexedV2Program.indexControl
             (SourceListMachineFields.coreControl (some true, false), none))),
       CylinderContextScanStep.selectedBank
         (SourceListEncoding.encode original)
         (SourceListEncoding.fields suffix) word pre.length⟩ :
        CylinderContextScanStep.Config)
    ∃ (t : Nat) (vFinal : Control)
      (SFinal : Fin 32 → List Bool),
      run t
        ⟨some (.inl (.inl .scan)),
         getterControl (CylinderContextScanStep.copyControl ((), none)),
         selected.stk⟩ = ⟨none, vFinal, SFinal⟩ ∧
      SFinal 9 = output ++ piece word ∧
      (∀ k : Fin 15, SFinal (cleanBank k) = []) ∧
      (∀ k : Fin 32,
        k = 8 ∨ k = 10 ∨ k = 12 ∨ k = 13 ∨ k = 15 ∨ k = 16 →
          SFinal k = selected.stk k) := by
  dsimp only
  have hmem : word ∈ tupleWords source := by
    rw [← hSplit]
    simp
  obtain ⟨entry, he, t, v, T, B, ht, hr, ho, hc, hp⟩ :=
    actual_member_selected_run source pre word suffix hmem i y
      (initialOutput ++ joined (coordinatePiece i.val y.bits) pre) context
  let output := initialOutput ++ joined (coordinatePiece i.val y.bits) pre
  let selected := CylinderCoordinateRowRun.selected pre word suffix
    output context i.val y.bits
  have hs : selected.stk =
      (LargeContextPreservingScan.frame
        (foreignBank output context suffix.length
          (CylinderCoordinateRowRun.pairExtra i.val y.bits))
        (⟨none,
         CylinderContextScanStep.getterControl
           (PreservingV2Program.v2Control
             (IndexedV2Program.indexControl
               (SourceListMachineFields.coreControl (some true, false), none))),
         CylinderContextScanStep.selectedBank
           (SourceListEncoding.encode (tupleWords source))
           (SourceListEncoding.fields suffix) word pre.length⟩ :
          CylinderContextScanStep.Config)).stk := by
    simp only [selected, CylinderCoordinateRowRun.selected, ← hSplit]
  refine ⟨t, v, T, ?_, ?_, hc, ?_⟩
  · simpa only [output, ← hs] using hr
  · simpa only [output, coordinatePiece] using ho
  · intro k hk
    rw [← hs]
    exact hp k hk

#print axioms reachable_run

end CurrentAdditive.CylinderReachableRowCallback
