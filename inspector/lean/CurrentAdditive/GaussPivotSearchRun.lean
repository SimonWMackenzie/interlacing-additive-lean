import CurrentAdditive.GaussPivotSearchStages

set_option maxHeartbeats 1000000

namespace CurrentAdditive.GaussPivotSearchRun

noncomputable section

open EthInapproximability.CurrentPaper
open CurrentAdditive.GaussPivotSearchController
open CurrentAdditive.GaussPivotSearchStages
open CurrentAdditive.GaussPivotCallbackFrame
open CurrentAdditive.GaussPivotTypedRows
open CurrentAdditive.GaussPivotTypedContract
open CurrentAdditive.GaussTypedGetterBridge
open CurrentAdditive.GaussPhysical
open CurrentAdditive.LargeContextListScheduler
open CurrentAdditive.LargeContextPreservingScan

abbrev Stack := Fin 32

theorem search_run {m k : Nat} (B : Fin m → Fin k → ℚ)
    (j : Fin k) (r : Nat) (state : List Bool) :
    let flags := (List.finRange m).map (fun i => decide (B i j ≠ 0))
    let S0 := (LargeContextPreservingScan.frame
      (foreignBank [] (List.replicate j.val true) m
        (extra (List.replicate r true) state))
      (CylinderContextScanStep.initial (encodeTypedMatrix B) 0)).stk
    ∃ t ≤ GaussPivotTypedScan.remainingBudget
        GaussRowZeroCallback.program (GaussRowZeroCallback.bLabel .scan)
        (GaussRowZeroCallback.bControl ((), none))
        (rowWords B) (piece j.val) [] (List.replicate j.val true)
        (contract B j (List.replicate r true) state) [] (rowWords B) +
        2 * m + 6,
      ∃ vFinal : GaussFlagSearch.Control,
      ∃ Sf : Stack → List Bool,
        GaussPivotSearchController.run t
          (GaussPivotSearchController.initial S0) =
          ⟨some .done, .choose vFinal, Sf⟩ ∧
        Sf 19 = List.replicate (GaussFlagSearch.firstHit flags r).2 true ∧
        Sf 20 = [(GaussFlagSearch.firstHit flags r).1] ∧
        Sf 31 = state ∧ Sf 8 = encodeTypedMatrix B := by
  dsimp only
  let flags := (List.finRange m).map (fun i => decide (B i j ≠ 0))
  let S0 := (LargeContextPreservingScan.frame
      (foreignBank [] (List.replicate j.val true) m
        (extra (List.replicate r true) state))
      (CylinderContextScanStep.initial (encodeTypedMatrix B) 0)).stk
  let Sscan := (LargeContextPreservingScan.frame
      (foreignBank flags.reverse (List.replicate j.val true) 0
        (extra (List.replicate r true) state))
      (CylinderContextScanStep.initial (encodeTypedMatrix B) m)).stk
  obtain ⟨t, ht, vf, hscan⟩ :=
    scan_embedded B j (List.replicate r true) state
  have h9 : Sscan 9 = flags.reverse := by
    simpa [Sscan, flags, foreignBank] using
      LargeContextPreservingScan.output_preserved
        (foreignBank flags.reverse (List.replicate j.val true) 0
          (extra (List.replicate r true) state))
        (CylinderContextScanStep.initial (encodeTypedMatrix B) m)
  have h15 : Sscan 15 = [] := by
    simpa [Sscan, extra] using
      frame_extra (encodeTypedMatrix B) flags.reverse
        (List.replicate j.val true) m 0
        (extra (List.replicate r true) state) 15 (by decide)
  have h30 : Sscan 30 = List.replicate r true := by
    simpa [Sscan, extra] using
      frame_extra (encodeTypedMatrix B) flags.reverse
        (List.replicate j.val true) m 0
        (extra (List.replicate r true) state) 30 (by decide)
  have h31 : Sscan 31 = state := by
    simpa [Sscan, extra] using
      frame_extra (encodeTypedMatrix B) flags.reverse
        (List.replicate j.val true) m 0
        (extra (List.replicate r true) state) 31 (by decide)
  have h19 : Sscan 19 = [] := by
    simpa [Sscan, extra] using
      frame_extra (encodeTypedMatrix B) flags.reverse
        (List.replicate j.val true) m 0
        (extra (List.replicate r true) state) 19 (by decide)
  have h20 : Sscan 20 = [] := by
    simpa [Sscan, extra] using
      frame_extra (encodeTypedMatrix B) flags.reverse
        (List.replicate j.val true) m 0
        (extra (List.replicate r true) state) 20 (by decide)
  have h8 : Sscan 8 = encodeTypedMatrix B := by
    simpa [Sscan, CylinderContextScanStep.initial,
      CylinderContextScanStep.initialBank] using
      LargeContextPreservingScan.frame_bank
        (foreignBank flags.reverse (List.replicate j.val true) 0
          (extra (List.replicate r true) state))
        (CylinderContextScanStep.initial (encodeTypedMatrix B) m)
        (8 : CylinderContextScanStep.Stack)
  obtain ⟨u, hu, hreverse⟩ :=
    reverse_embedded flags.reverse Sscan h9 h15
  let Sreverse := Function.update (Function.update Sscan 9 []) 15 flags
  have h15' : Sreverse 15 = flags := by simp [Sreverse]
  have h30' : Sreverse 30 = List.replicate r true := by
    simp [Sreverse, h30]
  have h19' : Sreverse 19 = [] := by simp [Sreverse, h19]
  have h20' : Sreverse 20 = [] := by simp [Sreverse, h20]
  have h31' : Sreverse 31 = state := by simp [Sreverse, h31]
  have h8' : Sreverse 8 = encodeTypedMatrix B := by
    simp [Sreverse, h8]
  obtain ⟨w, hw, vFinal, Sf, hchoose, hout, htag, hsaved, hmatrix⟩ :=
    choose_embedded flags r state Sreverse
      h15' h30' h19' h20' h31'
  have hscan' : GaussPivotSearchController.run t
      (GaussPivotSearchController.initial S0) =
      ⟨some .toReverse, .scan vf, Sscan⟩ := by
    simpa only [S0, Sscan, flags] using hscan
  have hreversed : GaussPivotSearchController.run (t + 1 + u)
      (GaussPivotSearchController.initial S0) =
      ⟨some .toChoose, .reverse none, Sreverse⟩ := by
    have hstep := run_add hscan' 1
    rw [to_reverse_step] at hstep
    have hjoined := run_add hstep u
    simpa [Sreverse, List.reverse_reverse] using hjoined.trans hreverse
  have hchoice : GaussPivotSearchController.run
      (t + 1 + u + 1 + w)
      (GaussPivotSearchController.initial S0) =
      ⟨some .done, .choose vFinal, Sf⟩ := by
    have hstep := run_add hreversed 1
    rw [to_choose_step] at hstep
    exact (run_add hstep w).trans hchoose
  refine ⟨t + 1 + u + 1 + w, ?_, vFinal, Sf,
    hchoice, hout, htag, hsaved, ?_⟩
  · have hlen : flags.length = m := by simp [flags]
    have hrev : flags.reverse.length = m := by simpa using hlen
    omega
  · exact hmatrix.trans h8'

#print axioms search_run

end
end CurrentAdditive.GaussPivotSearchRun
