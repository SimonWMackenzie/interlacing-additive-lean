import CurrentAdditive.GaussPivotTypedContract

set_option maxHeartbeats 1000000

namespace CurrentAdditive.GaussPivotScanRun

open EthInapproximability.CurrentPaper
open CurrentAdditive.GaussPivotTypedScan
open CurrentAdditive.GaussPivotTypedContract
open CurrentAdditive.GaussPivotTypedRows
open CurrentAdditive.GaussTypedGetterBridge
open CurrentAdditive.GaussPhysical
open CurrentAdditive.GaussPivotCallbackFrame
open CurrentAdditive.LargeContextListScheduler
open CurrentAdditive.LargeContextPreservingScan

noncomputable section

noncomputable instance : DecidableEq GaussRowZeroCallback.Label :=
  Classical.decEq _

theorem row_flags {m k : Nat} (B : Fin m → Fin k → ℚ)
    (j : Fin k) :
    (rowWords B).map (piece j.val) =
      (List.finRange m).map (fun i => decide (B i j ≠ 0)) := by
  simp [rowWords, List.map_map, piece_typed]

theorem scan_full {m k : Nat} (B : Fin m → Fin k → ℚ)
    (j : Fin k) (r state : List Bool)
    (v : LargeContextListScheduler.Control
      GaussRowZeroCallback.Control) :
    ∃ t ≤ GaussPivotTypedScan.remainingBudget
        GaussRowZeroCallback.program (GaussRowZeroCallback.bLabel .scan)
        (GaussRowZeroCallback.bControl ((), none))
        (rowWords B) (piece j.val) [] (List.replicate j.val true)
        (contract B j r state) [] (rowWords B),
      ∃ vFinal,
      LargeContextListScheduler.run GaussRowZeroCallback.program
        (GaussRowZeroCallback.bLabel .scan)
        (GaussRowZeroCallback.bControl ((), none)) t
        ⟨some (.inr (.inr .check)), v,
         (LargeContextPreservingScan.frame
           (foreignBank [] (List.replicate j.val true) m
             (extra r state))
           (CylinderContextScanStep.initial
             (encodeTypedMatrix B) 0)).stk⟩ =
        ⟨none, vFinal,
         (LargeContextPreservingScan.frame
           (foreignBank
             ((List.finRange m).map
               (fun i => decide (B i j ≠ 0))).reverse
             (List.replicate j.val true) 0 (extra r state))
           (CylinderContextScanStep.initial
             (encodeTypedMatrix B) m)).stk⟩ := by
  have h := GaussPivotTypedScan.run_remaining
    GaussRowZeroCallback.program (GaussRowZeroCallback.bLabel .scan)
    (GaussRowZeroCallback.bControl ((), none))
    (rowWords B) (piece j.val) [] (List.replicate j.val true)
    (contract B j r state) [] (rowWords B) v (by simp)
  have hlen : (rowWords B).length = m := by simp [rowWords]
  simpa only [reversed, List.map_nil, List.reverse_nil, List.nil_append,
    encodeTypedMatrix_eq, row_flags, hlen, List.append_nil] using h

#print axioms scan_full

end
end CurrentAdditive.GaussPivotScanRun
