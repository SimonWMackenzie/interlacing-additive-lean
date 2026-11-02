import CurrentAdditive.GaussPivotSearchHigh64

/-! One fixed Fin64 prep, backup, and pivot-search machine from the raw
Gauss state packet. -/

namespace CurrentAdditive.GaussPivotPrepSearchHigh64

noncomputable section

open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding

abbrev Bank := Fin 64

abbrev BC := Unit × Option Bool
abbrev PrepControl := GaussPivotPrepController32.Control ×
  ((((BC × BC) × BC) × BC))

def prepControl : PrepControl :=
  ((.copy ((),none),
    (((((),none),((),none)),((),none)),((),none))))

def searchLabel : GaussPivotSearchController.Label :=
  .scan (.inr (.inr .check))

def searchControl : GaussPivotSearchController.Control :=
  .scan (LargeContextListScheduler.getterControl
    (GaussRowZeroCallback.bControl ((), none))
    (CylinderContextScanStep.copyControl ((), none)))

def program := BitMachineRawSequence.program
  GaussPivotPrepSave64.program GaussPivotSearchHigh64.program
  searchLabel prepControl searchControl

theorem physical_prep_search {m k : Nat}
    (s : GaussControlTrace.State m k) (hc : s.c < k) :
    let j : Fin k := ⟨s.c,hc⟩
    let flags := (List.finRange m).map (fun i => decide (s.B i j ≠ 0))
    ∃ t, ∃ vf : GaussFlagSearch.Control,
      ∃ Sf : Fin 32 → List Bool,
      ((advance program)^[t])
        (⟨some (BitMachineRawSequence.leftLabel
          (BitMachineRawSequence.leftLabel (.copy .scan))),
          (prepControl,searchControl),
          (GaussPivotPrepHigh64.start s).stk⟩ :
          TM2.Cfg (fun _ : Bank => Bool) _ _) =
        ⟨none, (prepControl,.choose vf),
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
  obtain ⟨a, ha, hp⟩ := GaussPivotPrepSave64.physical_prep_save s
  obtain ⟨b, vf, Sf, hs, h19, h20, h8, h53, h55, h56, h58⟩ :=
    GaussPivotSearchHigh64.physical_search s hc
  obtain ⟨t, ht, he⟩ := BitMachineRawSequence.runs
    GaussPivotPrepSave64.program GaussPivotSearchHigh64.program
    (BitMachineRawSequence.leftLabel (.copy .scan)) searchLabel
    prepControl prepControl searchControl (.choose vf)
    (GaussPivotPrepHigh64.start s).stk
    (GaussPivotPrepSave64.saved s)
    (GaussPivotSearchHigh64.searched s Sf)
    a b (by simpa only [prepControl] using hp)
    (by simpa only [searchLabel, searchControl] using hs)
  exact ⟨t,vf,Sf,by simpa only [program] using he,
    h19,h20,h8,h53,h55,h56,h58⟩

#print axioms physical_prep_search

end
end CurrentAdditive.GaussPivotPrepSearchHigh64
