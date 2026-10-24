import CurrentAdditive.GaussPivotPrepSave64
import CurrentAdditive.GaussPivotSearchRun
import CurrentAdditive.GaussPivotSearchPrepBridge

/-! Run the actual pivot search on the saved Fin64 frame. Every high backup
made by `GaussPivotPrepSave64` survives the destructive low-bank search. -/

namespace CurrentAdditive.GaussPivotSearchHigh64

noncomputable section

open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding

abbrev Bank := Fin 64

def program (l : GaussPivotSearchController.Label) :
    TM2.Stmt (fun _ : Bank => Bool)
      GaussPivotSearchController.Label
      GaussPivotSearchController.Control :=
  BitMachineStackEmbedding.stackStmt GaussPivotPrepHigh64.low
    (GaussPivotSearchController.program l)

noncomputable def searched {m k : Nat}
    (s : GaussControlTrace.State m k)
    (Sf : Fin 32 → List Bool) : Bank → List Bool :=
  BitMachineStackEmbedding.bank GaussPivotPrepHigh64.low
    (GaussPivotPrepSave64.saved s) Sf

theorem searched_low {m k : Nat}
    (s : GaussControlTrace.State m k)
    (Sf : Fin 32 → List Bool) (i : Fin 32) :
    searched s Sf (GaussPivotPrepHigh64.low i) = Sf i :=
  BitMachineStackEmbedding.bank_at _ _ _ i

theorem searched_high {m k : Nat}
    (s : GaussControlTrace.State m k)
    (Sf : Fin 32 → List Bool) (j : Bank)
    (hj : 32 ≤ j.val) :
    searched s Sf j = GaussPivotPrepSave64.saved s j := by
  apply BitMachineStackEmbedding.bank_outside
  rintro ⟨i,hi⟩
  have hv : i.val = j.val := by
    simpa [GaussPivotPrepHigh64.low] using
      congrArg (fun x : Bank => x.val) hi
  omega

private theorem stmt_id {K L V : Type*} [DecidableEq K]
    (q : TM2.Stmt (fun _ : K => Bool) L V) :
    BitMachineInline.stmt id id id none q = q := by
  induction q <;> simp [BitMachineInline.stmt, *]

theorem physical_search {m k : Nat}
    (s : GaussControlTrace.State m k) (hc : s.c < k) :
    let j : Fin k := ⟨s.c,hc⟩
    let flags := (List.finRange m).map (fun i => decide (s.B i j ≠ 0))
    ∃ t, ∃ vf : GaussFlagSearch.Control,
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
    GaussPivotSearchRun.search_run s.B j s.r
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
  refine ⟨t,vf,Sf,?_,?_,?_,?_,?_,?_,?_,?_⟩
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

#print axioms physical_search

end
end CurrentAdditive.GaussPivotSearchHigh64
