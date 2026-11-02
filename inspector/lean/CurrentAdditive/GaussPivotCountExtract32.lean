import CurrentAdditive.GaussPivotCount32
import EthInapproximability.CurrentPaper.SourceClausePreservingBroadcast
import EthInapproximability.CurrentPaper.BitMachineClearBank

/-! Physically route the row-count output into scheduler bank 13, then drain
every scratch bank touched by the row-count subroutine. -/

namespace CurrentAdditive.GaussPivotCountExtract32

noncomputable section
set_option maxHeartbeats 800000

open EthInapproximability.CurrentPaper
open Turing Turing.TM2.Stmt BitMachineEncoding

abbrev Stack := Fin 32
abbrev Control := Unit × Option Bool
noncomputable abbrev M := GaussPivotCount32.M
def zero : Fin M.stackCount := ⟨0, by have h := M.input.isLt; omega⟩
noncomputable def source : Stack := GaussPivotCount32.slot M.output
def temp : Stack := 31

inductive Label where
  | copy (l : SourceClausePreservingBroadcast.Label)
  | clear (j : Fin M.stackCount)
  | finishClear | done
  deriving DecidableEq, Fintype

abbrev Config := TM2.Cfg (fun _ : Stack => Bool) Label Control

noncomputable def nextClear (j : Fin M.stackCount) : Label :=
  if h : j.val + 1 < M.stackCount then .clear ⟨j.val + 1, h⟩
  else .finishClear

noncomputable def program : Label → TM2.Stmt (fun _ : Stack => Bool) Label Control
  | .copy l => BitMachineInline.stmt Label.copy id id
      (some (.clear zero))
      (SourceClausePreservingBroadcast.program source temp [13] l)
  | .clear j => BitMachineClearBank.clearStep (GaussPivotCount32.slot j)
      (.clear j) (nextClear j)
  | .finishClear => BitMachineClearBank.finishStep id .done
  | .done => .halt

noncomputable def run (t : Nat) (c : Config) : Config := ((advance program)^[t]) c

noncomputable def afterCopy (S : Stack → List Bool) : Stack → List Bool :=
  SourceClausePreservingBroadcast.result source temp [13] (S source) S

theorem source_ne_temp : source ≠ temp := GaussPivotCount32.slot_not_31 _
theorem source_not_dest : source ∉ ([13] : List Stack) := by
  simpa using GaussPivotCount32.slot_not_13 M.output
theorem temp_not_dest : temp ∉ ([13] : List Stack) := by decide

theorem copy_count (S : Stack → List Bool) (htemp : S temp = []) :
    ∃ t ≤ 2 * (S source).length + 3,
      run t ⟨some (.copy .scan), ((), none), S⟩ =
        ⟨some (.clear zero), ((), none), afterCopy S⟩ := by
  have hcore := SourceClausePreservingBroadcast.run_halt source temp [13]
    source_ne_temp (by simp) source_not_dest temp_not_dest
    (S source) S rfl htemp
  obtain ⟨u, hu, hr⟩ := BitMachineInline.outputs
    Label.copy id id (by intro v; rfl) (some (.clear zero))
    (SourceClausePreservingBroadcast.program source temp [13])
    program (by intro l; rfl)
    (⟨some .scan, ((), none), S⟩ :
      TM2.Cfg (fun _ : Stack => Bool)
        SourceClausePreservingBroadcast.Label Control)
    (2 * (S source).length + 3) (by rw [hcore])
  refine ⟨u, hu, ?_⟩
  change run u _ = _ at hr
  rw [hcore] at hr
  simpa only [BitMachineInline.cfg, afterCopy] using hr

noncomputable def clearLabel : Fin (M.stackCount + 1) → Label
  | ⟨n, _hn⟩ => if h : n < M.stackCount then .clear ⟨n, h⟩ else .finishClear

theorem clearLabel_step (i : Fin M.stackCount) :
    clearLabel i.castSucc = .clear i ∧
    clearLabel i.succ = nextClear i := by
  have hi := i.isLt
  simp [clearLabel, nextClear, hi]

theorem clearLabel_finish : clearLabel (Fin.last M.stackCount) = .finishClear := by
  simp [clearLabel]

theorem clear_run (S : Stack → List Bool) :
    run ((∑ j : Fin M.stackCount,
      (S (GaussPivotCount32.slot j)).length) + M.stackCount + 1)
      ⟨some (.clear zero), ((), none), S⟩ =
      ⟨some .done, ((), none),
        BitMachineClearBank.cleared GaussPivotCount32.slot S⟩ := by
  change ((advance program)^[(∑ j : Fin M.stackCount,
    (S (GaussPivotCount32.slot j)).length) + M.stackCount + 1])
    ⟨some (clearLabel 0), ((), none), S⟩ = _
  apply BitMachineClearBank.clear_bank_run program id .done
    M.stackCount GaussPivotCount32.slot GaussPivotCount32.slot_injective
    clearLabel
  · intro i
    obtain ⟨hi, hn⟩ := clearLabel_step i
    rw [hi, hn]
    rfl
  · rw [clearLabel_finish]
    rfl

theorem extract_and_cleanup (S : Stack → List Bool) (htemp : S temp = []) :
    ∃ t ≤ (2 * (S source).length + 3) +
      (∑ j : Fin M.stackCount,
        ((afterCopy S) (GaussPivotCount32.slot j)).length) +
        M.stackCount + 1,
      run t ⟨some (.copy .scan), ((), none), S⟩ =
        ⟨some .done, ((), none),
          BitMachineClearBank.cleared GaussPivotCount32.slot
            (afterCopy S)⟩ := by
  obtain ⟨u, hu, hr⟩ := copy_count S htemp
  let v := (∑ j : Fin M.stackCount,
    ((afterCopy S) (GaussPivotCount32.slot j)).length) + M.stackCount + 1
  refine ⟨u + v, by dsimp [v]; omega, ?_⟩
  rw [Nat.add_comm, run, Function.iterate_add_apply]
  exact (congrArg (run v) hr).trans (clear_run (afterCopy S))

theorem final_count (S : Stack → List Bool) (h13 : S 13 = []) :
    (BitMachineClearBank.cleared GaussPivotCount32.slot (afterCopy S)) 13 =
      S source := by
  rw [BitMachineClearBank.cleared_foreign]
  · have h := SourceClausePreservingBroadcast.target_written
      source temp [13] temp_not_dest source_not_dest source_ne_temp
      (S source) S 13 (by simp)
    simpa [afterCopy, h13] using h
  · intro j
    exact GaussPivotCount32.slot_not_13 j

theorem final_ambient (S : Stack → List Bool) (j : Stack)
    (hj : j = 28 ∨ j = 30) :
    (BitMachineClearBank.cleared GaussPivotCount32.slot (afterCopy S)) j =
      S j := by
  rw [BitMachineClearBank.cleared_foreign]
  · apply SourceClausePreservingBroadcast.other_preserved
    · rcases hj with rfl | rfl
      · exact (GaussPivotCount32.slot_not_28 _).symm
      · exact (GaussPivotCount32.slot_not_30 _).symm
    · rcases hj with rfl | rfl <;> decide
    · rcases hj with rfl | rfl <;> decide
  · intro q
    rcases hj with rfl | rfl
    · exact GaussPivotCount32.slot_not_28 q
    · exact GaussPivotCount32.slot_not_30 q

#print axioms extract_and_cleanup
#print axioms final_count
#print axioms final_ambient

end
end CurrentAdditive.GaussPivotCountExtract32
