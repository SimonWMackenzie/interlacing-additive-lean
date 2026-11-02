import CurrentAdditive.GaussRowZeroCallbackRun
import CurrentAdditive.GaussTypedGetterBridge

set_option maxHeartbeats 1000000

namespace CurrentAdditive.GaussPivotCallbackFrame

open EthInapproximability.CurrentPaper
open CurrentAdditive.GaussListContext
open CurrentAdditive.LargeContextListScheduler
open CurrentAdditive.GaussRowZeroCallback

abbrev Stack := Fin 32

def extra (r : List Bool) (state : List Bool) : Stack → List Bool :=
  fun j => if j = 30 then r else if j = 31 then state else []

noncomputable def selected (pre : List (List Bool)) (word : List Bool)
    (suffix : List (List Bool)) (output context r state : List Bool) :=
  LargeContextPreservingScan.frame
    (foreignBank output context suffix.length (extra r state))
    (⟨none,
      CylinderContextScanStep.getterControl
        (PreservingV2Program.v2Control
          (IndexedV2Program.indexControl
            (SourceListMachineFields.coreControl (some true, false), none))),
      CylinderContextScanStep.selectedBank
        (SourceListEncoding.encode (pre ++ word :: suffix))
        (SourceListEncoding.fields suffix) word pre.length⟩ :
      CylinderContextScanStep.Config)

theorem selected_word (pre : List (List Bool)) (word : List Bool)
    (suffix : List (List Bool)) (output context r state : List Bool) :
    (selected pre word suffix output context r state).stk 6 = word := by
  exact LargeContextPreservingScan.selected_word _ _ _ _ _

theorem selected_context (pre : List (List Bool)) (word : List Bool)
    (suffix : List (List Bool)) (output context r state : List Bool) :
    (selected pre word suffix output context r state).stk 12 = context := by
  unfold selected
  rw [LargeContextPreservingScan.frame_foreign]
  · simp [foreignBank]
  · rintro ⟨k, hk⟩
    fin_cases k <;> cases hk

theorem selected_scratch (pre : List (List Bool)) (word : List Bool)
    (suffix : List (List Bool)) (output context r state : List Bool)
    (j : Stack) (hj : 15 ≤ j.val) (hu : j.val < 30) :
    (selected pre word suffix output context r state).stk j = [] := by
  unfold selected
  rw [LargeContextPreservingScan.frame_foreign]
  · rw [foreignBank_extra output context suffix.length (extra r state) j hj]
    have h30 : j ≠ 30 := by intro h; have hv := congrArg Fin.val h; omega
    have h31 : j ≠ 31 := by intro h; have hv := congrArg Fin.val h; omega
    simp [extra, h30, h31]
  · rintro ⟨k, hk⟩
    have hsmall : (LargeContextPreservingScan.locate k).val < 15 := by
      fin_cases k <;> decide
    have hv := congrArg Fin.val hk
    omega

theorem selected_output (pre : List (List Bool)) (word : List Bool)
    (suffix : List (List Bool)) (output context r state : List Bool) :
    (selected pre word suffix output context r state).stk 9 = output := by
  unfold selected
  rw [LargeContextPreservingScan.output_preserved]
  simp [foreignBank]

theorem selected_extra30 (pre : List (List Bool)) (word : List Bool)
    (suffix : List (List Bool)) (output context r state : List Bool) :
    (selected pre word suffix output context r state).stk 30 = r := by
  unfold selected
  rw [LargeContextPreservingScan.frame_foreign]
  · rw [foreignBank_extra output context suffix.length (extra r state) 30 (by decide)]
    simp [extra]
  · rintro ⟨k, hk⟩
    fin_cases k <;> cases hk

theorem selected_extra31 (pre : List (List Bool)) (word : List Bool)
    (suffix : List (List Bool)) (output context r state : List Bool) :
    (selected pre word suffix output context r state).stk 31 = state := by
  unfold selected
  rw [LargeContextPreservingScan.frame_foreign]
  · rw [foreignBank_extra output context suffix.length (extra r state) 31 (by decide)]
    simp [extra]
  · rintro ⟨k, hk⟩
    fin_cases k <;> cases hk

theorem selected_cell_run (rowPre : List (List Bool)) (word : List Bool)
    (rowSuffix : List (List Bool)) (output r state : List Bool)
    (cellPre : List (List Bool)) (cell : List Bool)
    (cellSuffix : List (List Bool))
    (hword : word = SourceListEncoding.encode
      (cellPre ++ cell :: cellSuffix)) :
    let S := (selected rowPre word rowSuffix output
      (List.replicate cellPre.length true) r state).stk
    ∃ t ≤ callbackCost cellPre cell cellSuffix S,
      ∃ v : GaussRowZeroCallback.Control,
        GaussRowZeroCallback.run t
          ⟨some (bLabel .scan), bControl ((), none), S⟩ =
          ⟨none, v, finalState cellPre cell cellSuffix S⟩ ∧
        (finalState cellPre cell cellSuffix S) 9 =
          ((CurrentAdditive.GaussRawZeroCheck.numeratorWord cell).any id) :: output ∧
        (∀ i : Fin 15,
          (finalState cellPre cell cellSuffix S) (clearBank i) = []) ∧
        (∀ k : Stack,
          k = 8 ∨ k = 10 ∨ k = 12 ∨ k = 13 ∨ k = 30 ∨ k = 31 →
          (finalState cellPre cell cellSuffix S) k = S k) := by
  dsimp only
  let S := (selected rowPre word rowSuffix output
    (List.replicate cellPre.length true) r state).stk
  have hrow : S 6 = SourceListEncoding.encode
      (cellPre ++ cell :: cellSuffix) := by
    rw [← hword]
    exact selected_word rowPre word rowSuffix output
      (List.replicate cellPre.length true) r state
  have hcontext : S 12 = List.replicate cellPre.length true :=
    selected_context rowPre word rowSuffix output
      (List.replicate cellPre.length true) r state
  have hscratch : ∀ k : Stack, 15 ≤ k.val → k.val < 30 → S k = [] := by
    intro k hk hu
    exact selected_scratch rowPre word rowSuffix output
      (List.replicate cellPre.length true) r state k hk hu
  obtain ⟨t, ht, v, hr, ho, hs, hp⟩ :=
    callback_run_clean cellPre cell cellSuffix S hrow hcontext hscratch
  refine ⟨t, ht, v, hr, ?_, hs, hp⟩
  rw [ho]
  congr 1
  exact selected_output rowPre word rowSuffix output
    (List.replicate cellPre.length true) r state

end CurrentAdditive.GaussPivotCallbackFrame
