import CurrentAdditive.CylinderActualTupleRow
import CurrentAdditive.SourceContextScheduler

/-! The coordinate callback's physical terminal stack matches the Fin32
scheduler's full-bank next-item frame after its cleanup and index increment. -/

namespace CurrentAdditive.CylinderSchedulerPost

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open CurrentAdditive.GaussListContext
open CurrentAdditive.LargeContextListScheduler
open CurrentAdditive.CylinderCoordinateRowRun

theorem selected_bank8 (pre : List (List Bool)) (word : List Bool)
    (suffix : List (List Bool)) (output context : List Bool)
    (index : Nat) (symbol : List Bool) :
    (selected pre word suffix output context index symbol).stk 8 =
      SourceListEncoding.encode (pre ++ word :: suffix) := by
  simpa [selected, CylinderContextScanStep.selectedBank,
    LargeContextPreservingScan.locate] using
    LargeContextPreservingScan.frame_bank
      (foreignBank output context suffix.length (pairExtra index symbol))
      (⟨none,
       CylinderContextScanStep.getterControl
         (PreservingV2Program.v2Control
           (IndexedV2Program.indexControl
             (SourceListMachineFields.coreControl (some true, false), none))),
       CylinderContextScanStep.selectedBank
         (SourceListEncoding.encode (pre ++ word :: suffix))
         (SourceListEncoding.fields suffix) word pre.length⟩ :
        CylinderContextScanStep.Config) 8

theorem selected_bank10 (pre : List (List Bool)) (word : List Bool)
    (suffix : List (List Bool)) (output context : List Bool)
    (index : Nat) (symbol : List Bool) :
    (selected pre word suffix output context index symbol).stk 10 =
      List.replicate pre.length true := by
  simpa [selected, CylinderContextScanStep.selectedBank,
    LargeContextPreservingScan.locate] using
    LargeContextPreservingScan.frame_bank
      (foreignBank output context suffix.length (pairExtra index symbol))
      (⟨none,
       CylinderContextScanStep.getterControl
         (PreservingV2Program.v2Control
           (IndexedV2Program.indexControl
             (SourceListMachineFields.coreControl (some true, false), none))),
       CylinderContextScanStep.selectedBank
         (SourceListEncoding.encode (pre ++ word :: suffix))
         (SourceListEncoding.fields suffix) word pre.length⟩ :
        CylinderContextScanStep.Config) 10

theorem selected_bank12 (pre : List (List Bool)) (word : List Bool)
    (suffix : List (List Bool)) (output context : List Bool)
    (index : Nat) (symbol : List Bool) :
    (selected pre word suffix output context index symbol).stk 12 =
      context := by
  rw [selected_foreign pre word suffix output context index symbol 12
    (by decide)]
  simp [foreignBank]

theorem selected_bank13 (pre : List (List Bool)) (word : List Bool)
    (suffix : List (List Bool)) (output context : List Bool)
    (index : Nat) (symbol : List Bool) :
    (selected pre word suffix output context index symbol).stk 13 =
      List.replicate suffix.length true := by
  rw [selected_foreign pre word suffix output context index symbol 13
    (by decide)]
  simp [foreignBank]

theorem callback_post (pre : List (List Bool)) (word : List Bool)
    (suffix : List (List Bool)) (output context : List Bool)
    (index : Nat) (symbol : List Bool)
    (T : Fin 32 → List Bool) (b : Bool)
    (hout : T 9 = output ++ [b])
    (hclean : ∀ i : Fin 15,
      T (CylinderCoordinateEqualityCallback.cleanBank i) = [])
    (hpres : ∀ k : Fin 32,
      k = 8 ∨ k = 10 ∨ k = 12 ∨ k = 13 ∨ k = 15 ∨ k = 16 →
        T k = (selected pre word suffix output context index symbol).stk k) :
    Function.update
      (BitMachineClearBank.cleared LargeContextListScheduler.cleanBank T) 10
      (true :: (BitMachineClearBank.cleared
        LargeContextListScheduler.cleanBank T) 10) =
    (LargeContextPreservingScan.frame
      (foreignBank (output ++ [b]) context suffix.length
        (pairExtra index symbol))
      (CylinderContextScanStep.initial
        (SourceListEncoding.encode (pre ++ word :: suffix))
        (pre.length + 1))).stk := by
  have h8 : T 8 = SourceListEncoding.encode (pre ++ word :: suffix) := by
    rw [hpres 8 (by decide)]
    exact selected_bank8 pre word suffix output context index symbol
  have h10 : T 10 = List.replicate pre.length true := by
    rw [hpres 10 (by decide)]
    exact selected_bank10 pre word suffix output context index symbol
  have h12 : T 12 = context := by
    rw [hpres 12 (by decide)]
    exact selected_bank12 pre word suffix output context index symbol
  have h13 : T 13 = List.replicate suffix.length true := by
    rw [hpres 13 (by decide)]
    exact selected_bank13 pre word suffix output context index symbol
  have h15 : T 15 = List.replicate index true := by
    rw [hpres 15 (by decide)]
    simpa [pairExtra] using selected_extra pre word suffix output
      context index symbol 15 (by decide)
  have h16 : T 16 = symbol := by
    rw [hpres 16 (by decide)]
    simpa [pairExtra] using selected_extra pre word suffix output
      context index symbol 16 (by decide)
  have htail (k : Fin 32) (hk : 17 ≤ k.val) : T k = [] := by
    let i : Fin 15 := ⟨k.val - 17, by omega⟩
    have hi : CylinderCoordinateEqualityCallback.cleanBank i = k := by
      apply Fin.ext
      simp [CylinderCoordinateEqualityCallback.cleanBank, i]
      omega
    rw [← hi]
    exact hclean i
  let F := LargeContextPreservingScan.frame
      (foreignBank (output ++ [b]) context suffix.length
        (pairExtra index symbol))
      (CylinderContextScanStep.initial
        (SourceListEncoding.encode (pre ++ word :: suffix))
        (pre.length + 1))
  have himage (j : Fin 12) :
      F.stk (LargeContextPreservingScan.locate j) =
        (CylinderContextScanStep.initial
          (SourceListEncoding.encode (pre ++ word :: suffix))
          (pre.length + 1)).stk j := by
    exact LargeContextPreservingScan.frame_bank _ _ j
  have hforeign (k : Fin 32)
      (hk : ¬ ∃ j : Fin 12, LargeContextPreservingScan.locate j = k) :
      F.stk k =
        (foreignBank (output ++ [b]) context suffix.length
          (pairExtra index symbol)) k := by
    exact LargeContextPreservingScan.frame_foreign _ _ k hk
  have hclean_locate (j : Fin 12) :
      (∃ i : Fin 10, LargeContextListScheduler.cleanBank i =
        LargeContextPreservingScan.locate j) ↔ j ≠ 8 ∧ j ≠ 10 := by
    fin_cases j <;> decide
  have hclean_subimage (i : Fin 10) :
      ∃ j : Fin 12,
        LargeContextPreservingScan.locate j =
          LargeContextListScheduler.cleanBank i := by
    fin_cases i <;> decide
  have hclear_image (j : Fin 12) :
      BitMachineClearBank.cleared LargeContextListScheduler.cleanBank T
          (LargeContextPreservingScan.locate j) =
        if j ≠ 8 ∧ j ≠ 10 then [] else
          T (LargeContextPreservingScan.locate j) := by
    by_cases hp : ∃ i : Fin 10,
        LargeContextListScheduler.cleanBank i =
          LargeContextPreservingScan.locate j
    · have hq := (hclean_locate j).mp hp
      simp [BitMachineClearBank.cleared, hp, hq]
    · have hq : ¬ (j ≠ 8 ∧ j ≠ 10) := by
        intro h
        exact hp ((hclean_locate j).mpr h)
      simp [BitMachineClearBank.cleared, hp, hq]
  have hclear10 :
      BitMachineClearBank.cleared LargeContextListScheduler.cleanBank T 10 =
        T 10 := by
    have hn : ¬ ∃ i : Fin 10,
        LargeContextListScheduler.cleanBank i = (10 : Fin 32) := by decide
    simp [BitMachineClearBank.cleared, hn]
  have hresult (k : Fin 32) :
      (Function.update
        (BitMachineClearBank.cleared LargeContextListScheduler.cleanBank T) 10
        (true :: (BitMachineClearBank.cleared
          LargeContextListScheduler.cleanBank T) 10)) k =
      if k = 10 then true :: T 10 else
        BitMachineClearBank.cleared LargeContextListScheduler.cleanBank T k := by
    by_cases heq : k = 10 <;>
      simp [Function.update_apply, heq, hclear10]
  funext k
  change (Function.update
    (BitMachineClearBank.cleared LargeContextListScheduler.cleanBank T) 10
    (true :: (BitMachineClearBank.cleared
      LargeContextListScheduler.cleanBank T) 10)) k = F.stk k
  by_cases hk : ∃ j : Fin 12, LargeContextPreservingScan.locate j = k
  · obtain ⟨j, rfl⟩ := hk
    rw [hresult, himage, hclear_image]
    fin_cases j <;>
      simp [LargeContextPreservingScan.locate,
        CylinderContextScanStep.initial,
        CylinderContextScanStep.initialBank,
        h8, h10, List.replicate_succ]
  · rw [hforeign k hk]
    have hnc : ¬ ∃ i : Fin 10,
        LargeContextListScheduler.cleanBank i = k := by
      rintro ⟨i, hi⟩
      obtain ⟨j, hj⟩ := hclean_subimage i
      exact hk ⟨j, hj.trans hi⟩
    have hclear_outside :
        BitMachineClearBank.cleared LargeContextListScheduler.cleanBank T k =
          T k := by
      simp [BitMachineClearBank.cleared, hnc]
    rw [hresult, hclear_outside]
    fin_cases k <;>
      (first
        | (exfalso; exact hk (by decide))
        | (simp [foreignBank, pairExtra,
             hout, h12, h13, h15, h16])) <;>
      exact htail _ (by decide)

#print axioms callback_post

end CurrentAdditive.CylinderSchedulerPost
