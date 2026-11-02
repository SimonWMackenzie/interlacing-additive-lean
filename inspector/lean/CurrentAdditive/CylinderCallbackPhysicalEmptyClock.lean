import CurrentAdditive.CylinderCallbackPhysicalClock

set_option maxHeartbeats 8000000
set_option maxRecDepth 16384
set_option synthInstance.maxSize 65536

namespace CurrentAdditive.CylinderCoordinateEqualityCallback

open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper.BitMachineStackGrowth
open CurrentAdditive.GaussListContext

theorem physical_coordinate_pair_empty_bounded (pre : List (List Bool))
    (word : List Bool) (suffix : List (List Bool))
    (right out : List Bool) (foreign : Stack → List Bool)
    (h16 : foreign 16 = right) (h9 : foreign 9 = out)
    (h27 : foreign 27 = []) (h28 : foreign 28 = [])
    (h29 : foreign 29 = [])
    (hEmpty : ∀ i : Fin 15,
      (getterFrame foreign
        (CylinderContextScanStep.initial
          (SourceListEncoding.encode (pre ++ word :: suffix))
          pre.length)).stk (cleanBank i) = []) :
    let tuple := SourceListEncoding.encode (pre ++ word :: suffix)
    let start := getterFrame foreign
      (CylinderContextScanStep.initial tuple pre.length)
    ∃ (t : Nat) (vFinal : Control) (SFinal SBefore : Stack → List Bool),
      t ≤ getterBound pre word suffix + 1 +
        CylinderEqualityAppendCallback.callbackBound word right out +
        15 * (BitMachineStackGrowth.perStep program *
          (getterBound pre word suffix + 1 +
            CylinderEqualityAppendCallback.callbackBound word right out)) + 17 ∧
      run t start = ⟨none, vFinal, SFinal⟩ ∧
      SFinal 9 = out ++ [decide (word = right)] ∧
      SFinal = BitMachineClearBank.cleared cleanBank SBefore ∧
      (∀ i : Fin 15, SFinal (cleanBank i) = []) ∧
      (∀ k : Stack,
        k = 8 ∨ k = 10 ∨ k = 12 ∨ k = 13 ∨ k = 15 ∨ k = 16 →
          SFinal k = start.stk k) := by
  dsimp only
  let tuple := SourceListEncoding.encode (pre ++ word :: suffix)
  let start := getterFrame foreign
    (CylinderContextScanStep.initial tuple pre.length)
  obtain ⟨t, vFinal, SFinal, SBefore, _hcap, hrun, h9final, hcleared,
      hblank, hpres, htime, hpoint⟩ :=
    physical_coordinate_pair_bounded pre word suffix right out foreign
      h16 h9 h27 h28 h29
  have hsum := CylinderCallbackCleanupClock.callback_cleanup_sum_le_empty
    pre word suffix right out start.stk SBefore
      (by simpa only [start, tuple] using hEmpty) hpoint
  unfold CylinderCallbackCleanupClock.cleanupCost at hsum
  refine ⟨t, vFinal, SFinal, SBefore, ?_, hrun, h9final,
    hcleared, hblank, hpres⟩
  omega

#print axioms physical_coordinate_pair_empty_bounded

end CurrentAdditive.CylinderCoordinateEqualityCallback
