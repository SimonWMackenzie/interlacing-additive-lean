import CurrentAdditive.GaussPivotCallbackFrame

set_option maxHeartbeats 1000000

namespace CurrentAdditive.GaussPivotCallbackPost

open EthInapproximability.CurrentPaper
open CurrentAdditive.GaussListContext
open CurrentAdditive.LargeContextListScheduler
open CurrentAdditive.GaussPivotCallbackFrame
open CurrentAdditive.GaussRowZeroCallback

abbrev Stack := Fin 32

def cleanToLocate : Fin 10 → Fin 12 :=
  ![0, 1, 2, 3, 4, 5, 6, 7, 11, 9]

theorem cleanToLocate_eq (i : Fin 10) :
    LargeContextPreservingScan.locate (cleanToLocate i) =
      LargeContextListScheduler.cleanBank i := by
  fin_cases i <;> decide

theorem locate_clean (j : Fin 12) (h8 : j ≠ 8) (h10 : j ≠ 10) :
    ∃ i : Fin 10, LargeContextListScheduler.cleanBank i =
      LargeContextPreservingScan.locate j := by
  fin_cases j <;> simp_all [LargeContextPreservingScan.locate,
    LargeContextListScheduler.cleanBank] <;> decide

theorem selected_source (pre : List (List Bool)) (word : List Bool)
    (suffix : List (List Bool)) (output context r state : List Bool) :
    (selected pre word suffix output context r state).stk 8 =
      SourceListEncoding.encode (pre ++ word :: suffix) := by
  exact LargeContextPreservingScan.selected_source _ _ _ _ _

theorem selected_index (pre : List (List Bool)) (word : List Bool)
    (suffix : List (List Bool)) (output context r state : List Bool) :
    (selected pre word suffix output context r state).stk 10 =
      List.replicate pre.length true := by
  unfold selected
  simpa [CylinderContextScanStep.selectedBank,
    LargeContextPreservingScan.locate] using
    LargeContextPreservingScan.frame_bank
      (foreignBank output context suffix.length (extra r state))
      (⟨none,
        CylinderContextScanStep.getterControl
          (PreservingV2Program.v2Control
            (IndexedV2Program.indexControl
              (SourceListMachineFields.coreControl (some true, false), none))),
        CylinderContextScanStep.selectedBank
          (SourceListEncoding.encode (pre ++ word :: suffix))
          (SourceListEncoding.fields suffix) word pre.length⟩ :
        CylinderContextScanStep.Config) 10

theorem selected_fuel (pre : List (List Bool)) (word : List Bool)
    (suffix : List (List Bool)) (output context r state : List Bool) :
    (selected pre word suffix output context r state).stk 13 =
      List.replicate suffix.length true := by
  unfold selected
  rw [LargeContextPreservingScan.frame_foreign]
  · simp [foreignBank]
  · rintro ⟨k, hk⟩
    fin_cases k <;> cases hk

theorem post_clean (pre : List (List Bool)) (word : List Bool)
    (suffix : List (List Bool)) (output context r state : List Bool)
    (T : Stack → List Bool) (b : Bool)
    (hout : T 9 = b :: output)
    (hclean : ∀ i : Fin 15, T (clearBank i) = [])
    (hpres : ∀ k : Stack,
      k = 8 ∨ k = 10 ∨ k = 12 ∨ k = 13 ∨ k = 30 ∨ k = 31 →
      T k = (selected pre word suffix output context r state).stk k) :
    Function.update
      (BitMachineClearBank.cleared LargeContextListScheduler.cleanBank T) 10
      (true :: (BitMachineClearBank.cleared
        LargeContextListScheduler.cleanBank T) 10) =
    (LargeContextPreservingScan.frame
      (foreignBank (b :: output) context suffix.length (extra r state))
      (CylinderContextScanStep.initial
        (SourceListEncoding.encode (pre ++ word :: suffix))
        (pre.length + 1))).stk := by
  have h8 : T 8 = SourceListEncoding.encode (pre ++ word :: suffix) := by
    rw [hpres 8 (by decide)]
    exact selected_source pre word suffix output context r state
  have h10 : T 10 = List.replicate pre.length true := by
    rw [hpres 10 (by decide)]
    exact selected_index pre word suffix output context r state
  have h12 : T 12 = context := by
    rw [hpres 12 (by decide)]
    exact selected_context pre word suffix output context r state
  have h13 : T 13 = List.replicate suffix.length true := by
    rw [hpres 13 (by decide)]
    exact selected_fuel pre word suffix output context r state
  have h30 : T 30 = r := by
    rw [hpres 30 (by decide)]
    exact selected_extra30 pre word suffix output context r state
  have h31 : T 31 = state := by
    rw [hpres 31 (by decide)]
    exact selected_extra31 pre word suffix output context r state
  have htail (k : Stack) (hl : 15 ≤ k.val) (hu : k.val < 30) :
      T k = [] := by
    obtain ⟨i, hi⟩ := clearBank_cover k hl hu
    rw [← hi]
    exact hclean i
  let F := LargeContextPreservingScan.frame
      (foreignBank (b :: output) context suffix.length (extra r state))
      (CylinderContextScanStep.initial
        (SourceListEncoding.encode (pre ++ word :: suffix))
        (pre.length + 1))
  funext k
  change (Function.update
    (BitMachineClearBank.cleared LargeContextListScheduler.cleanBank T) 10
    (true :: (BitMachineClearBank.cleared
      LargeContextListScheduler.cleanBank T) 10)) k =
    (LargeContextPreservingScan.frame
      (foreignBank (b :: output) context suffix.length (extra r state))
      (CylinderContextScanStep.initial
        (SourceListEncoding.encode (pre ++ word :: suffix))
        (pre.length + 1))).stk k
  by_cases himage : ∃ j : Fin 12, LargeContextPreservingScan.locate j = k
  · obtain ⟨j, rfl⟩ := himage
    rw [LargeContextPreservingScan.frame_bank]
    by_cases hj8 : j = 8
    · subst j
      have hnot : ∀ i : Fin 10,
          LargeContextListScheduler.cleanBank i ≠
            LargeContextPreservingScan.locate (8 : Fin 12) := by
        intro i; fin_cases i <;> decide
      have hnot8 : ∀ i : Fin 10,
          LargeContextListScheduler.cleanBank i ≠ (8 : Stack) := by
        simpa [LargeContextPreservingScan.locate] using hnot
      have hclean8 := BitMachineClearBank.cleared_foreign
        LargeContextListScheduler.cleanBank T 8 hnot8
      simpa [LargeContextPreservingScan.locate,
        CylinderContextScanStep.initial,
        CylinderContextScanStep.initialBank, hclean8, h8]
    · by_cases hj10 : j = 10
      · subst j
        have hnot : ∀ i : Fin 10,
            LargeContextListScheduler.cleanBank i ≠
              LargeContextPreservingScan.locate (10 : Fin 12) := by
          intro i; fin_cases i <;> decide
        have hnot10 : ∀ i : Fin 10,
            LargeContextListScheduler.cleanBank i ≠ (10 : Stack) := by
          simpa [LargeContextPreservingScan.locate] using hnot
        have hclean10 := BitMachineClearBank.cleared_foreign
          LargeContextListScheduler.cleanBank T 10 hnot10
        simpa [LargeContextPreservingScan.locate,
          CylinderContextScanStep.initial,
          CylinderContextScanStep.initialBank, hclean10, h10,
          List.replicate_succ]
      · have hclean : ∃ i : Fin 10,
            LargeContextListScheduler.cleanBank i =
              LargeContextPreservingScan.locate j := by
          exact locate_clean j hj8 hj10
        obtain ⟨i, hi⟩ := hclean
        have hne : LargeContextPreservingScan.locate j ≠ (10 : Stack) := by
          intro he
          have hj := LargeContextPreservingScan.locate.injective
            (he.trans (by decide : (10 : Stack) =
              LargeContextPreservingScan.locate (10 : Fin 12)))
          exact hj10 hj
        rw [Function.update_of_ne hne, ← hi,
          BitMachineClearBank.cleared_bank]
        fin_cases j <;>
          first
          | exact (hj8 rfl).elim
          | exact (hj10 rfl).elim
          | simp [CylinderContextScanStep.initial,
              CylinderContextScanStep.initialBank]
  · rw [LargeContextPreservingScan.frame_foreign _ _ k himage]
    have hnot : ∀ i : Fin 10,
        LargeContextListScheduler.cleanBank i ≠ k := by
      intro i hi
      exact himage ⟨cleanToLocate i, (cleanToLocate_eq i).trans hi⟩
    have hne : k ≠ (10 : Stack) := by
      intro he
      exact himage ⟨10, by simpa [LargeContextPreservingScan.locate] using he.symm⟩
    rw [Function.update_of_ne hne,
      BitMachineClearBank.cleared_foreign _ _ _ hnot]
    fin_cases k <;>
      first
      | exact (himage (by decide)).elim
      | simp [foreignBank, extra, htail, hout, h12, h13, h30, h31]

end CurrentAdditive.GaussPivotCallbackPost
