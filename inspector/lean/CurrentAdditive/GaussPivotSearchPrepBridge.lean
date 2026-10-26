import CurrentAdditive.GaussPivotSearchRun
import CurrentAdditive.GaussPivotPrepRun

set_option maxHeartbeats 1000000

namespace CurrentAdditive.GaussPivotSearchPrepBridge

noncomputable section

open EthInapproximability.CurrentPaper
open CurrentAdditive.GaussPivotCallbackFrame
open CurrentAdditive.GaussPhysical
open CurrentAdditive.LargeContextPreservingScan
open CurrentAdditive.LargeContextListScheduler

abbrev Stack := Fin 32

theorem input_frame (source context r state : List Bool) (m : Nat) :
    (LargeContextPreservingScan.frame
      (foreignBank [] context m (extra r state))
      (CylinderContextScanStep.initial source 0)).stk =
      fun j : Stack =>
        if j = 8 then source
        else if j = 12 then context
        else if j = 13 then List.replicate m true
        else if j = 30 then r
        else if j = 31 then state
        else [] := by
  funext j
  by_cases hj : ∃ z : CylinderContextScanStep.Stack,
      LargeContextPreservingScan.locate z = j
  · obtain ⟨z, rfl⟩ := hj
    rw [LargeContextPreservingScan.frame_bank]
    fin_cases z <;>
      simp [LargeContextPreservingScan.locate,
        CylinderContextScanStep.initial,
        CylinderContextScanStep.initialBank]
  · rw [LargeContextPreservingScan.frame_foreign _ _ j hj]
    fin_cases j <;>
      first
      | exact (hj (by decide)).elim
      | simp [foreignBank, extra]

theorem prepared_frame {m k : Nat}
    (s : GaussControlTrace.State m k) (hc : s.c < k) :
    let j : Fin k := ⟨s.c, hc⟩
    (LargeContextPreservingScan.frame
      (foreignBank [] (List.replicate j.val true) m
        (extra (List.replicate s.r true)
          (GaussControlTrace.statePacket s)))
      (CylinderContextScanStep.initial
        (encodeTypedMatrix s.B) 0)).stk =
      GaussPivotPrepBank.prepared s := by
  dsimp only
  rw [input_frame]
  funext x
  exact (GaussPivotPrepBank.prepared_exact s x).symm

#print axioms prepared_frame

end
end CurrentAdditive.GaussPivotSearchPrepBridge
