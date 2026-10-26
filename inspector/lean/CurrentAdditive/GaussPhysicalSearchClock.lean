import CurrentAdditive.GaussSearchRuntime
import CurrentAdditive.GaussPivotSearchHigh64

set_option maxHeartbeats 1000000

namespace CurrentAdditive.GaussPhysicalSearchClock

noncomputable section

open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open CurrentAdditive.GaussPivotSearchHigh64

private theorem stmt_id {K L V : Type*} [DecidableEq K]
    (q : TM2.Stmt (fun _ : K => Bool) L V) :
    BitMachineInline.stmt id id id none q = q := by
  induction q <;> simp [BitMachineInline.stmt, *]

theorem physical_search_clock {m k : Nat}
    (s : GaussControlTrace.State m k) (hc : s.c < k) :
    let j : Fin k := ⟨s.c,hc⟩
    let flags := (List.finRange m).map (fun i => decide (s.B i j ≠ 0))
    ∃ t ≤ GaussSearchRuntime.polynomialClock (GaussControlTrace.statePacket s).length + 1,
      ∃ vf : GaussFlagSearch.Control,
      ∃ Sf : Fin 32 → List Bool,
      ((advance program)^[t])
        (⟨some (.scan (.inr (.inr .check))),
          .scan (LargeContextListScheduler.getterControl
            (GaussRowZeroCallback.bControl ((), none))
            (CylinderContextScanStep.copyControl ((), none))),
          GaussPivotPrepSave64.saved s⟩ :
          TM2.Cfg (fun _ : Bank => Bool) _ _) =
        ⟨none, .choose vf, searched s Sf⟩ ∧
      (searched s Sf) 19 =
        List.replicate (GaussFlagSearch.firstHit flags s.r).2 true ∧
      (searched s Sf) 20 =
        [(GaussFlagSearch.firstHit flags s.r).1] ∧
      (searched s Sf) 8 = GaussPhysical.encodeTypedMatrix s.B ∧
      (searched s Sf) 53 = List.replicate s.r true ∧
      (searched s Sf) 55 = List.replicate s.c true ∧
      (searched s Sf) 56 = GaussControlTrace.statePacket s ∧
      (searched s Sf) 58 = List.replicate m true := by
  dsimp only
  let j : Fin k := ⟨s.c,hc⟩
  let flags := (List.finRange m).map (fun i => decide (s.B i j ≠ 0))
  obtain ⟨b, hb, vf, Sf, hs, h19, h20, h31, h8⟩ :=
    GaussSearchRuntime.search_run_clock s.B j s.r
      (GaussControlTrace.statePacket s)
  have hframe := GaussPivotSearchPrepBridge.prepared_frame s hc
  have hs0 : GaussPivotSearchController.run b
      (GaussPivotSearchController.initial (GaussPivotPrepBank.prepared s)) =
      ⟨some .done, .choose vf, Sf⟩ := by
    rw [← hframe]
    exact hs
  have hs' : GaussPivotSearchController.run (b+1)
      (GaussPivotSearchController.initial (GaussPivotPrepBank.prepared s)) =
      ⟨none, .choose vf, Sf⟩ := by
    rw [show b+1 = 1+b by omega,
      GaussPivotSearchController.run, Function.iterate_add_apply]
    rw [show ((advance GaussPivotSearchController.program)^[b])
      (GaussPivotSearchController.initial (GaussPivotPrepBank.prepared s)) =
      ⟨some .done, .choose vf, Sf⟩ from hs0]
    rfl
  have hstart : BitMachineStackEmbedding.stackCfg
      GaussPivotPrepHigh64.low (GaussPivotPrepSave64.saved s)
      (GaussPivotSearchController.initial (GaussPivotPrepBank.prepared s)) =
      ⟨some (.scan (.inr (.inr .check))),
        .scan (LargeContextListScheduler.getterControl
          (GaussRowZeroCallback.bControl ((), none))
          (CylinderContextScanStep.copyControl ((), none))),
        GaussPivotPrepSave64.saved s⟩ := by
    have hbanks : BitMachineStackEmbedding.bank
        GaussPivotPrepHigh64.low (GaussPivotPrepSave64.saved s)
        (GaussPivotPrepBank.prepared s) =
        GaussPivotPrepSave64.saved s := by
      apply BitMachineStackEmbedding.bank_eq_self
      intro i
      exact (GaussPivotPrepSave64.saved_low s i).symm
    simpa only [BitMachineStackEmbedding.stackCfg,
      GaussPivotSearchController.initial, hbanks]
  have hhalt : (((advance GaussPivotSearchController.program)^[b+1])
      (GaussPivotSearchController.initial
        (GaussPivotPrepBank.prepared s))).l = none := by
    change (GaussPivotSearchController.run (b+1)
      (GaussPivotSearchController.initial
        (GaussPivotPrepBank.prepared s))).l = none
    rw [hs']
  obtain ⟨t, ht, he⟩ := BitMachineStackEmbedding.outputs
    GaussPivotPrepHigh64.low (GaussPivotPrepSave64.saved s)
    id id id (by intro v; rfl) none
    GaussPivotSearchController.program program
    (by intro l; simp [program, BitMachineStackEmbedding.stmt, stmt_id])
    (GaussPivotSearchController.initial (GaussPivotPrepBank.prepared s))
    (b+1) hhalt
  rw [show ((advance GaussPivotSearchController.program)^[b+1])
    (GaussPivotSearchController.initial (GaussPivotPrepBank.prepared s)) =
    ⟨none, .choose vf, Sf⟩ from hs'] at he
  have hbudget := GaussSearchRuntime.search_budget_input_le s
  refine ⟨t, by omega, vf,Sf,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · change ((advance program)^[t])
      (BitMachineStackEmbedding.stackCfg
        GaussPivotPrepHigh64.low (GaussPivotPrepSave64.saved s)
        (GaussPivotSearchController.initial
          (GaussPivotPrepBank.prepared s))) =
      BitMachineStackEmbedding.stackCfg
        GaussPivotPrepHigh64.low (GaussPivotPrepSave64.saved s)
        ⟨none, .choose vf, Sf⟩ at he
    rw [hstart] at he
    simpa only [BitMachineStackEmbedding.stackCfg,
      searched] using he
  · change searched s Sf (GaussPivotPrepHigh64.low (19 : Fin 32)) = _
    rw [searched_low]
    exact h19
  · change searched s Sf (GaussPivotPrepHigh64.low (20 : Fin 32)) = _
    rw [searched_low]
    exact h20
  · change searched s Sf (GaussPivotPrepHigh64.low (8 : Fin 32)) = _
    rw [searched_low]
    exact h8
  · rw [searched_high s Sf 53 (by decide)]
    exact GaussPivotPrepSave64.saved_row s
  · rw [searched_high s Sf 55 (by decide)]
    exact GaussPivotPrepSave64.saved_column s
  · rw [searched_high s Sf 56 (by decide)]
    exact GaussPivotPrepSave64.saved_packet s
  · rw [searched_high s Sf 58 (by decide)]
    exact GaussPivotPrepSave64.saved_backup_count s

#print axioms physical_search_clock

end
end CurrentAdditive.GaussPhysicalSearchClock
