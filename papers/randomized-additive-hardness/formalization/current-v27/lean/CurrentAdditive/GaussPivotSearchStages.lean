import CurrentAdditive.GaussPivotSearchController

set_option maxHeartbeats 1000000

namespace CurrentAdditive.GaussPivotSearchStages

noncomputable section

open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open CurrentAdditive.GaussPivotSearchController
open CurrentAdditive.GaussPivotScanRun
open CurrentAdditive.GaussPivotTypedRows
open CurrentAdditive.GaussPivotTypedContract
open CurrentAdditive.GaussTypedGetterBridge
open CurrentAdditive.GaussPhysical
open CurrentAdditive.GaussPivotCallbackFrame
open CurrentAdditive.LargeContextListScheduler
open CurrentAdditive.LargeContextPreservingScan

abbrev Stack := Fin 32
abbrev Config := GaussPivotSearchController.Config
abbrev Control := GaussPivotSearchController.Control

theorem run_add {c c' : Config} {t : Nat}
    (h : GaussPivotSearchController.run t c = c')
    (u : Nat) : GaussPivotSearchController.run (t + u) c =
      GaussPivotSearchController.run u c' := by
  rw [Nat.add_comm, GaussPivotSearchController.run,
    Function.iterate_add_apply]
  exact congrArg (GaussPivotSearchController.run u) h

theorem to_reverse_step (S : Stack → List Bool) (v : Control) :
    GaussPivotSearchController.run 1 ⟨some .toReverse, v, S⟩ =
      ⟨some (.reverse .scan), .reverse none, S⟩ := rfl

theorem to_choose_step (S : Stack → List Bool) (v : Control) :
    GaussPivotSearchController.run 1 ⟨some .toChoose, v, S⟩ =
      ⟨some (.choose .skip), .choose (none, none), S⟩ := rfl

noncomputable instance : DecidableEq GaussRowZeroCallback.Label :=
  Classical.decEq _

theorem scan_embedded {m k : Nat} (B : Fin m → Fin k → ℚ)
    (j : Fin k) (r state : List Bool) :
    let source := encodeTypedMatrix B
    let flags := ((List.finRange m).map
      (fun i => decide (B i j ≠ 0))).reverse
    let S0 := (LargeContextPreservingScan.frame
      (foreignBank [] (List.replicate j.val true) m (extra r state))
      (CylinderContextScanStep.initial source 0)).stk
    let Sf := (LargeContextPreservingScan.frame
      (foreignBank flags (List.replicate j.val true) 0 (extra r state))
      (CylinderContextScanStep.initial source m)).stk
    ∃ t ≤ GaussPivotTypedScan.remainingBudget
        GaussRowZeroCallback.program (GaussRowZeroCallback.bLabel .scan)
        (GaussRowZeroCallback.bControl ((), none))
        (rowWords B) (piece j.val) [] (List.replicate j.val true)
        (contract B j r state) [] (rowWords B),
      ∃ vFinal : ScanControl,
        GaussPivotSearchController.run t
          (GaussPivotSearchController.initial S0) =
          ⟨some .toReverse, .scan vFinal, Sf⟩ := by
  dsimp only
  let S0 := (LargeContextPreservingScan.frame
      (foreignBank [] (List.replicate j.val true) m (extra r state))
      (CylinderContextScanStep.initial (encodeTypedMatrix B) 0)).stk
  let Sf := (LargeContextPreservingScan.frame
      (foreignBank (((List.finRange m).map
        (fun i => decide (B i j ≠ 0))).reverse)
        (List.replicate j.val true) 0 (extra r state))
      (CylinderContextScanStep.initial (encodeTypedMatrix B) m)).stk
  let v0 := LargeContextListScheduler.getterControl
    (GaussRowZeroCallback.bControl ((), none))
      (CylinderContextScanStep.copyControl ((), none))
  obtain ⟨t, ht, vf, hr⟩ := scan_full B j r state v0
  have hhalt : (((advance scanProgram)^[t])
      (⟨some (.inr (.inr .check)), v0, S0⟩ :
        TM2.Cfg (fun _ : Stack => Bool) ScanLabel ScanControl)).l = none := by
    simpa only [scanProgram, LargeContextListScheduler.run] using congrArg
      (fun c => c.l) hr
  obtain ⟨u, hu, hembed⟩ := BitMachineInline.outputs
    Label.scan Control.scan readScan (by intro v; rfl)
    (some Label.toReverse) scanProgram GaussPivotSearchController.program
      (by intro l; rfl)
    ⟨some (.inr (.inr .check)), v0, S0⟩ t hhalt
  refine ⟨u, hu.trans ht, vf, ?_⟩
  simpa [GaussPivotSearchController.run, GaussPivotSearchController.initial,
    BitMachineInline.cfg, scanProgram,
    LargeContextListScheduler.run, S0, Sf, v0] using hembed.trans
      (congrArg (BitMachineInline.cfg Label.scan Control.scan
        (some Label.toReverse)) hr)

theorem reverse_embedded (bs : List Bool) (S : Stack → List Bool)
    (h9 : S 9 = bs) (h15 : S 15 = []) :
    ∃ u ≤ bs.length + 1,
      GaussPivotSearchController.run u
        ⟨some (.reverse .scan), .reverse none, S⟩ =
      ⟨some .toChoose, .reverse none,
        Function.update (Function.update S 9 []) 15 bs.reverse⟩ := by
  let c : GaussPivotReverse32.Config := ⟨some .scan, none, S⟩
  have hr := GaussPivotReverse32.run_with_output bs [] S h9 h15
  have hhalt : (((advance GaussPivotReverse32.program)^[bs.length+1]) c).l = none := by
    simpa [GaussPivotReverse32.run, c] using congrArg (fun x => x.l) hr
  obtain ⟨u, hu, he⟩ := BitMachineInline.outputs
    Label.reverse Control.reverse readReverse (by intro v; rfl)
    (some Label.toChoose) GaussPivotReverse32.program
    GaussPivotSearchController.program (by intro l; rfl)
    c (bs.length+1) hhalt
  refine ⟨u, hu, ?_⟩
  simpa [GaussPivotSearchController.run, BitMachineInline.cfg,
    GaussPivotReverse32.run, c] using he.trans
      (congrArg (BitMachineInline.cfg Label.reverse Control.reverse
        (some Label.toChoose)) hr)

theorem selector_input (flags : List Bool) (r : Nat)
    (state : List Bool) (S : Stack → List Bool)
    (h15 : S 15 = flags) (h30 : S 30 = List.replicate r true)
    (h19 : S 19 = []) (h20 : S 20 = []) (h31 : S 31 = state) :
    (BitMachineStackEmbedding.stackCfg selectSlot S
      (GaussFlagSearch.initial flags r state)).stk = S := by
  apply BitMachineStackEmbedding.bank_eq_self
  intro i
  fin_cases i <;>
    simp [selectSlot, GaussFlagSearch.initial, GaussFlagSearch.cfg,
      GaussFlagSearch.bank, h15, h30, h19, h20, h31]

theorem choose_embedded (flags : List Bool) (r : Nat)
    (state : List Bool) (S : Stack → List Bool)
    (h15 : S 15 = flags) (h30 : S 30 = List.replicate r true)
    (h19 : S 19 = []) (h20 : S 20 = []) (h31 : S 31 = state) :
    ∃ t ≤ flags.length + 2, ∃ vFinal : GaussFlagSearch.Control,
      ∃ Sf : Stack → List Bool,
        GaussPivotSearchController.run t
          ⟨some (.choose .skip), .choose (none, none), S⟩ =
          ⟨some .done, .choose vFinal, Sf⟩ ∧
        Sf 19 = List.replicate (GaussFlagSearch.firstHit flags r).2 true ∧
        Sf 20 = [(GaussFlagSearch.firstHit flags r).1] ∧
        Sf 31 = state ∧ Sf 8 = S 8 := by
  let c := GaussFlagSearch.initial flags r state
  obtain ⟨t, ht, hl, hrow, htag, hsaved⟩ :=
    GaussFlagSearch.outputs flags r state
  let cFinal := GaussFlagSearch.run t c
  have hstack := BitMachineStackRun.run selectSlot S
    GaussFlagSearch.program c t
  have hhalt :
      (((advance (fun l => BitMachineStackEmbedding.stackStmt
        selectSlot (GaussFlagSearch.program l)))^[t])
          (BitMachineStackEmbedding.stackCfg selectSlot S c)).l = none := by
    rw [hstack]
    simpa [BitMachineStackEmbedding.stackCfg, cFinal] using hl
  let P := fun l => BitMachineStackEmbedding.stackStmt
    selectSlot (GaussFlagSearch.program l)
  obtain ⟨u, hu, he⟩ := BitMachineInline.outputs
    Label.choose Control.choose readChoose (by intro v; rfl)
    (some Label.done) P GaussPivotSearchController.program
    (by intro l; rfl)
    (BitMachineStackEmbedding.stackCfg selectSlot S c) t hhalt
  refine ⟨u, hu.trans ht, cFinal.var,
    (BitMachineStackEmbedding.stackCfg selectSlot S cFinal).stk,
    ?_, ?_, ?_, ?_, ?_⟩
  · have hstart :
        BitMachineInline.cfg Label.choose Control.choose
          (some Label.done)
          (BitMachineStackEmbedding.stackCfg selectSlot S c) =
        (⟨some (.choose .skip), .choose (none, none), S⟩ : Config) := by
      change (⟨some (.choose .skip), .choose (none, none),
        (BitMachineStackEmbedding.stackCfg selectSlot S c).stk⟩ : Config) = _
      rw [selector_input flags r state S h15 h30 h19 h20 h31]
    have hcomb := he.trans
      (congrArg (BitMachineInline.cfg Label.choose Control.choose
        (some Label.done)) hstack)
    rw [hstart] at hcomb
    have hl' : (((advance GaussFlagSearch.program)^[t]) c).l = none := by
      simpa [GaussFlagSearch.run, c] using hl
    simpa [GaussPivotSearchController.run, BitMachineInline.cfg,
      BitMachineStackEmbedding.stackCfg, cFinal, P, hl'] using hcomb
  · change (BitMachineStackEmbedding.bank selectSlot S cFinal.stk) 19 = _
    rw [show (19 : Stack) = selectSlot 2 by decide,
      BitMachineStackEmbedding.bank_at]
    exact hrow
  · change (BitMachineStackEmbedding.bank selectSlot S cFinal.stk) 20 = _
    rw [show (20 : Stack) = selectSlot 3 by decide,
      BitMachineStackEmbedding.bank_at]
    exact htag
  · change (BitMachineStackEmbedding.bank selectSlot S cFinal.stk) 31 = _
    rw [show (31 : Stack) = selectSlot 4 by decide,
      BitMachineStackEmbedding.bank_at]
    exact hsaved
  · have hout : ¬ ∃ x : Fin 5, selectSlot x = (8 : Stack) := by
      intro h
      obtain ⟨x, hx⟩ := h
      fin_cases x <;> cases hx
    exact BitMachineStackEmbedding.bank_outside selectSlot S cFinal.stk 8 hout

end
end CurrentAdditive.GaussPivotSearchStages
