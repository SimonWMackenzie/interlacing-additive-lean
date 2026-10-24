import CurrentAdditive.GaussPhysicalSearchClock
import CurrentAdditive.GaussPivotPrepClock
import CurrentAdditive.GaussPivotPrepSearchHigh64

set_option maxHeartbeats 1000000

namespace CurrentAdditive.GaussPhysicalPrepSearchClock

noncomputable section

open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open CurrentAdditive.GaussPivotPrepSearchHigh64

noncomputable def polynomialClock (N : Nat) : Nat :=
  GaussPivotPrepClock.polynomialClock N +
    GaussSearchRuntime.polynomialClock N + 20 * (N + 1)

theorem physical_prep_search_clock {m k : Nat}
    (s : GaussControlTrace.State m k) (hc : s.c < k) :
    let j : Fin k := ⟨s.c,hc⟩
    let flags := (List.finRange m).map (fun i => decide (s.B i j ≠ 0))
    ∃ t ≤ polynomialClock (GaussControlTrace.statePacket s).length,
      ∃ vf : GaussFlagSearch.Control,
      ∃ Sf : Fin 32 → List Bool,
      ((advance GaussPivotPrepSearchHigh64.program)^[t])
        (⟨some (BitMachineRawSequence.leftLabel
          (BitMachineRawSequence.leftLabel (.copy .scan))),
          (GaussPivotPrepSearchHigh64.prepControl,
            GaussPivotPrepSearchHigh64.searchControl),
          (GaussPivotPrepHigh64.start s).stk⟩ :
          TM2.Cfg (fun _ : Fin 64 => Bool) _ _) =
        ⟨none, (GaussPivotPrepSearchHigh64.prepControl,.choose vf),
          GaussPivotSearchHigh64.searched s Sf⟩ ∧
      (GaussPivotSearchHigh64.searched s Sf) 19 =
        List.replicate (GaussFlagSearch.firstHit flags s.r).2 true ∧
      (GaussPivotSearchHigh64.searched s Sf) 20 =
        [(GaussFlagSearch.firstHit flags s.r).1] ∧
      (GaussPivotSearchHigh64.searched s Sf) 8 =
        GaussPhysical.encodeTypedMatrix s.B ∧
      (GaussPivotSearchHigh64.searched s Sf) 53 =
        List.replicate s.r true ∧
      (GaussPivotSearchHigh64.searched s Sf) 55 =
        List.replicate s.c true ∧
      (GaussPivotSearchHigh64.searched s Sf) 56 =
        GaussControlTrace.statePacket s ∧
      (GaussPivotSearchHigh64.searched s Sf) 58 =
        List.replicate m true := by
  dsimp only
  let N := (GaussControlTrace.statePacket s).length
  obtain ⟨a, ha, hp⟩ := GaussPivotPrepSave64.physical_prep_save s
  obtain ⟨b, hb, vf, Sf, hs, h19, h20, h8, h53, h55, h56, h58⟩ :=
    GaussPhysicalSearchClock.physical_search_clock s hc
  have hprep := GaussPivotPrepClock.clock_le_polynomial s
  have hr : s.r ≤ N := by
    have h := GaussControlTrace.statePacket_length s
    dsimp [N]
    omega
  have hcol : s.c ≤ N := by
    have h := GaussControlTrace.statePacket_length s
    dsimp [N]
    omega
  have hm : m ≤ N := by
    have hrow : (GaussTypedGetterBridge.rowWords s.B).length = m := by
      simp [GaussTypedGetterBridge.rowWords]
    have hcode := GaussSearchClock.rows_le_code
      (GaussTypedGetterBridge.rowWords s.B)
    have heq := congrArg List.length
      (GaussTypedGetterBridge.encodeTypedMatrix_eq s.B)
    have hpacket := GaussControlTrace.statePacket_length s
    dsimp [N]
    omega
  have ha' : a ≤ GaussPivotPrepClock.polynomialClock N + 8 * N + 17 := by
    change GaussPivotPrepRun.clock s ≤
      GaussPivotPrepClock.polynomialClock N at hprep
    omega
  obtain ⟨t, ht, he⟩ := BitMachineRawSequence.runs
    GaussPivotPrepSave64.program GaussPivotSearchHigh64.program
    (BitMachineRawSequence.leftLabel (.copy .scan))
    GaussPivotPrepSearchHigh64.searchLabel
    GaussPivotPrepSearchHigh64.prepControl
    GaussPivotPrepSearchHigh64.prepControl
    GaussPivotPrepSearchHigh64.searchControl (.choose vf)
    (GaussPivotPrepHigh64.start s).stk
    (GaussPivotPrepSave64.saved s)
    (GaussPivotSearchHigh64.searched s Sf)
    a b (by simpa only [GaussPivotPrepSearchHigh64.prepControl] using hp)
    (by simpa only [GaussPivotPrepSearchHigh64.searchLabel,
      GaussPivotPrepSearchHigh64.searchControl] using hs)
  refine ⟨t, ?_, vf, Sf, ?_, h19, h20, h8, h53, h55, h56, h58⟩
  · unfold polynomialClock
    dsimp [N] at ha' hr hcol hm
    omega
  · simpa only [GaussPivotPrepSearchHigh64.program] using he

#print axioms physical_prep_search_clock

end
end CurrentAdditive.GaussPhysicalPrepSearchClock
