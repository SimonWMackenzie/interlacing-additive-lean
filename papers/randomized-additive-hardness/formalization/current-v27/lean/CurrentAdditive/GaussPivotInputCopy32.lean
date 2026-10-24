import CurrentAdditive.GaussPivotCount32
import EthInapproximability.CurrentPaper.SourceClausePreservingBroadcast

/-! Starting with only the actual encoded Gauss state on bank 30, physically
copy it to the saved-source bank and the row-count machine's input bank. -/

namespace CurrentAdditive.GaussPivotInputCopy32

open EthInapproximability.CurrentPaper
open Turing BitMachineEncoding

abbrev Stack := Fin 32
abbrev Control := Unit × Option Bool
abbrev Label := SourceClausePreservingBroadcast.Label
abbrev Config := TM2.Cfg (fun _ : Stack => Bool) Label Control

def startBank (word : List Bool) : Stack → List Bool :=
  fun j => if j = 30 then word else []

noncomputable def target : Stack := GaussPivotCount32.slot GaussPivotCount32.M.input

noncomputable def program : Label → TM2.Stmt (fun _ : Stack => Bool) Label Control :=
  SourceClausePreservingBroadcast.program 30 31 [28, target]

noncomputable def run (t : Nat) (c : Config) : Config := ((advance program)^[t]) c

noncomputable def result (word : List Bool) : Stack → List Bool :=
  SourceClausePreservingBroadcast.result 30 31 [28, target]
    word (startBank word)

theorem source_ne_temp : (30 : Stack) ≠ 31 := by decide
theorem targets_nodup : ([28, target] : List Stack).Nodup := by
  simp [show (28 : Stack) ≠ target from
    (GaussPivotCount32.slot_not_28 _).symm]
theorem source_not_target : (30 : Stack) ∉ [28, target] := by
  simp [show (30 : Stack) ≠ target from
    (GaussPivotCount32.slot_not_30 _).symm]
theorem temp_not_target : (31 : Stack) ∉ [28, target] := by
  simp [show (31 : Stack) ≠ target from
    (GaussPivotCount32.slot_not_31 _).symm]

theorem physical_start (word : List Bool) :
    run (2 * word.length + 3)
      ⟨some .scan, ((), none), startBank word⟩ =
      ⟨none, ((), none), result word⟩ := by
  exact SourceClausePreservingBroadcast.run_halt
    30 31 [28, target] source_ne_temp targets_nodup
    source_not_target temp_not_target word (startBank word)
    (by simp [startBank]) (by simp [startBank])

theorem source_preserved (word : List Bool) : result word 30 = word := by
  exact SourceClausePreservingBroadcast.source_restored
    30 31 [28, target] source_ne_temp word (startBank word)

theorem saved_source (word : List Bool) : result word 28 = word := by
  have h := SourceClausePreservingBroadcast.target_written
    30 31 [28, target] temp_not_target source_not_target
    source_ne_temp word (startBank word) 28 (by simp)
  simpa [result, startBank] using h

theorem count_input (word : List Bool) : result word target = word := by
  have h := SourceClausePreservingBroadcast.target_written
    30 31 [28, target] temp_not_target source_not_target
    source_ne_temp word (startBank word) target (by simp)
  have hne : target ≠ (30 : Stack) := by
    exact GaussPivotCount32.slot_not_30 _
  simpa [result, startBank, hne] using h

theorem temp_empty (word : List Bool) : result word 31 = [] :=
  SourceClausePreservingBroadcast.temp_empty 30 31 [28, target]
    word (startBank word)

theorem count_ready (word : List Bool) (j : Fin GaussPivotCount32.M.stackCount) :
    result word (GaussPivotCount32.slot j) =
      (GaussPivotCount32.M.init word).stk j := by
  by_cases hj : j = GaussPivotCount32.M.input
  · subst j
    simpa [BitMachine.Machine.init, target] using count_input word
  · have hs : GaussPivotCount32.slot j ≠ (30 : Stack) :=
      GaussPivotCount32.slot_not_30 j
    have ht : GaussPivotCount32.slot j ≠ (31 : Stack) :=
      GaussPivotCount32.slot_not_31 j
    have h28 : GaussPivotCount32.slot j ≠ (28 : Stack) :=
      GaussPivotCount32.slot_not_28 j
    have htarget : GaussPivotCount32.slot j ≠ target := by
      intro he
      exact hj (GaussPivotCount32.slot_injective he)
    have h := SourceClausePreservingBroadcast.other_preserved
      30 31 [28, target] word (startBank word)
      (GaussPivotCount32.slot j) hs ht (by simp [h28, htarget])
    simpa [result, startBank, hs, BitMachine.Machine.init, hj] using h

#print axioms physical_start
#print axioms count_ready

end CurrentAdditive.GaussPivotInputCopy32
