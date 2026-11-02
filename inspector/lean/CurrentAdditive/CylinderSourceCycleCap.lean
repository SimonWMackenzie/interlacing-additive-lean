import CurrentAdditive.CylinderSourceClockContract
import EthInapproximability.CurrentPaper.BitMachineStackGrowth

set_option maxRecDepth 1024
set_option maxHeartbeats 1000000

/-! A concrete per-cycle cap computed from the actual selected frame.  The
callback time is bounded by the selected word's canonical coordinate split;
the scheduler cleanup is charged for every bank it clears. -/

noncomputable section

namespace CurrentAdditive.CylinderSourceCycleCap

open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open CurrentAdditive.GaussListContext
open CurrentAdditive.CylinderSourceTupleProjection
open CurrentAdditive.CylinderSourceContractPrep
open CurrentAdditive.CylinderSourceClockContract
open CurrentAdditive.CylinderCanonicalPairBound
open CurrentAdditive.LargeContextListScheduler
open CurrentAdditive.SourceContextScheduler
open CurrentAdditive.CylinderCoordinateEqualityCallback

def splitCap {q : Nat}
    (source : Array ((Fin q → Nat) × ℚ))
    (i : Fin q) (y : Nat) (initialOutput context : List Bool)
    (pre : List (List Bool)) (word : List Bool)
    (suffix : List (List Bool)) : Nat :=
  let out := initialOutput ++ joined (piece i.val y.bits) pre
  let B := wordPairBound i.val y.bits word out
  getterBudget pre word suffix + (B + 1) + 1 +
    ((∑ k : Fin 10,
      ((callbackSelected source i y initialOutput context pre word suffix
        (LargeContextListScheduler.cleanBank k)).length +
        BitMachineStackGrowth.perStep
          CylinderCoordinateEqualityCallback.program * B)) + 11) + 1

theorem cycleBudget_le_splitCap {q : Nat}
    (source : Array ((Fin q → Nat) × ℚ))
    (i : Fin q) (y : Nat) (initialOutput context : List Bool)
    (pre : List (List Bool)) (word : List Bool)
    (suffix : List (List Bool))
    (hSplit : pre ++ word :: suffix = tupleWords source) :
    SourceContextScheduler.cycleBudget
      CylinderCoordinateEqualityCallback.program
      callbackStart callbackInit (piece i.val y.bits)
      initialOutput context (tupleWords source)
      (clockContract source i y initialOutput context)
      pre word suffix ≤
        splitCap source i y initialOutput context pre word suffix := by
  let C := clockContract source i y initialOutput context
  let S := callbackSelected source i y initialOutput context
    pre word suffix
  let B := wordPairBound i.val y.bits word
    (initialOutput ++ joined (piece i.val y.bits) pre)
  have ht : C.time pre word suffix ≤ B :=
    clockContract_time source i y initialOutput context
      pre word suffix hSplit
  have hs : S =
      (LargeContextPreservingScan.frame
        (foreignBank
          (initialOutput ++ joined (piece i.val y.bits) pre)
          context suffix.length C.extra)
        (⟨none,
          CylinderContextScanStep.getterControl
            (PreservingV2Program.v2Control
              (IndexedV2Program.indexControl
                (SourceListMachineFields.coreControl
                  (some true, false), none))),
          CylinderContextScanStep.selectedBank
            (SourceListEncoding.encode (tupleWords source))
            (SourceListEncoding.fields suffix) word pre.length⟩ :
              CylinderContextScanStep.Config)).stk := by
    rfl
  have hr := C.callback_run pre word suffix hSplit
  simp only [← hs] at hr
  have hbank (k : Fin 10) :
      (C.state pre word suffix
        (LargeContextListScheduler.cleanBank k)).length ≤
      (S (LargeContextListScheduler.cleanBank k)).length +
        BitMachineStackGrowth.perStep
          CylinderCoordinateEqualityCallback.program * B := by
    have hg := BitMachineStackGrowth.run_growth
      CylinderCoordinateEqualityCallback.program
      (⟨some callbackStart, callbackInit, S⟩ :
        CylinderCoordinateEqualityCallback.Config)
      (C.time pre word suffix)
      (LargeContextListScheduler.cleanBank k)
    rw [hr] at hg
    exact hg.trans (Nat.add_le_add_left
      (Nat.mul_le_mul_left _ ht) _)
  have hsum :
      (∑ k : Fin 10,
        (C.state pre word suffix
          (LargeContextListScheduler.cleanBank k)).length) ≤
      ∑ k : Fin 10,
        ((S (LargeContextListScheduler.cleanBank k)).length +
          BitMachineStackGrowth.perStep
            CylinderCoordinateEqualityCallback.program * B) := by
    apply Finset.sum_le_sum
    intro k _
    exact hbank k
  change
    getterBudget pre word suffix + (C.time pre word suffix + 1) + 1 +
      ((∑ k : Fin 10,
        (C.state pre word suffix
          (LargeContextListScheduler.cleanBank k)).length) + 11) + 1 ≤
    getterBudget pre word suffix + (B + 1) + 1 +
      ((∑ k : Fin 10,
        ((S (LargeContextListScheduler.cleanBank k)).length +
          BitMachineStackGrowth.perStep
            CylinderCoordinateEqualityCallback.program * B)) + 11) + 1
  omega

#print axioms cycleBudget_le_splitCap

end CurrentAdditive.CylinderSourceCycleCap
