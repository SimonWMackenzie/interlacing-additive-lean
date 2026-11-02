import CurrentAdditive.GaussPivotPrepRun
import CurrentAdditive.GaussPivotSearchPrepBridge
import EthInapproximability.CurrentPaper.BitMachineRawSequence

/-! A single fixed Fin32 program that prepares and searches for a Gauss pivot
from the raw state packet. -/

namespace CurrentAdditive.GaussPivotPrepSearch32

noncomputable section

open Turing Turing.TM2
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open CurrentAdditive.GaussPhysical

abbrev Stack := Fin 32

noncomputable def program := BitMachineRawSequence.program
  GaussPivotPrepController32.program GaussPivotSearchController.program
  (.scan (.inr (.inr .check)))
  (.copy ((), none))
  (GaussPivotSearchController.initial (fun _ => [])).var

theorem outputs {m k : Nat} (s : GaussControlTrace.State m k)
    (hc : s.c < k) :
    let j : Fin k := ⟨s.c,hc⟩
    let flags := (List.finRange m).map (fun i => decide (s.B i j ≠ 0))
    ∃ t, ∃ v : GaussPivotSearchController.Control, ∃ S : Stack → List Bool,
      ((advance program)^[t])
        (⟨some (BitMachineRawSequence.leftLabel (.copy .scan)),
          ((.copy ((), none)), (GaussPivotSearchController.initial (fun _ => [])).var),
          (GaussPivotPrepController32.initial
            (GaussControlTrace.statePacket s)).stk⟩ :
          TM2.Cfg (fun _ : Stack => Bool) _ _) =
        ⟨none, (.copy ((), none),v), S⟩ ∧
      S 19 = List.replicate (GaussFlagSearch.firstHit flags s.r).2 true ∧
      S 20 = [(GaussFlagSearch.firstHit flags s.r).1] ∧
      S 31 = GaussControlTrace.statePacket s ∧
      S 8 = encodeTypedMatrix s.B := by
  dsimp only
  let j : Fin k := ⟨s.c,hc⟩
  let flags := (List.finRange m).map (fun i => decide (s.B i j ≠ 0))
  obtain ⟨a, ha, hp⟩ := GaussPivotPrepRun.outputs s
  obtain ⟨b, hb, vf, Sf, hs, h19, h20, h31, h8⟩ :=
    GaussPivotSearchRun.search_run s.B j s.r
      (GaussControlTrace.statePacket s)
  have hframe := GaussPivotSearchPrepBridge.prepared_frame s hc
  have hs0 : GaussPivotSearchController.run b
      (GaussPivotSearchController.initial (GaussPivotPrepBank.prepared s)) =
      ⟨some .done, .choose vf, Sf⟩ := by
    rw [← hframe]
    exact hs
  have hp' : GaussPivotPrepController32.run (a+1)
        (GaussPivotPrepController32.initial (GaussControlTrace.statePacket s)) =
        ⟨none, .fields ((), none), GaussPivotPrepBank.prepared s⟩ := by
    have hbase : GaussPivotPrepController32.run (a+1)
        (GaussPivotPrepController32.initial (GaussPivotPrepBank.packet s)) =
        ⟨none, .fields ((), none), GaussPivotPrepBank.prepared s⟩ := by
      rw [GaussPivotPrepController32.run_add hp 1]
      rfl
    simpa only [GaussPivotPrepBank.packet] using hbase
  have hs' : GaussPivotSearchController.run (b+1)
        (GaussPivotSearchController.initial (GaussPivotPrepBank.prepared s)) =
        ⟨none, .choose vf, Sf⟩ := by
    rw [show b+1 = 1+b by omega,
      GaussPivotSearchController.run, Function.iterate_add_apply]
    rw [show ((advance GaussPivotSearchController.program)^[b])
      (GaussPivotSearchController.initial (GaussPivotPrepBank.prepared s)) =
      ⟨some .done, .choose vf, Sf⟩ from hs0]
    rfl
  obtain ⟨t, ht, hseq⟩ := BitMachineRawSequence.runs
      GaussPivotPrepController32.program GaussPivotSearchController.program
      (.copy .scan)
      (.scan (.inr (.inr .check)))
      (.copy ((), none)) (.fields ((), none))
      (GaussPivotSearchController.initial (fun _ => [])).var (.choose vf)
      (GaussPivotPrepController32.initial (GaussControlTrace.statePacket s)).stk
      (GaussPivotPrepBank.prepared s) Sf
      (a+1) (b+1) hp' hs'
  refine ⟨t, (.choose vf), Sf, ?_, h19, h20, h31, h8⟩
  simpa only [program] using hseq

#print axioms outputs

end
end CurrentAdditive.GaussPivotPrepSearch32
