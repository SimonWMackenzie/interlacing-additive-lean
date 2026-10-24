import CurrentAdditive.SourceContextScheduler96

/-! Full-bank Fin96 postcondition after the outer scheduler clears its ten
working banks and advances the tuple index.  The callback may use the higher
banks internally but must restore their fixed baseline before returning. -/

namespace CurrentAdditive.CylinderSchedulerPost96

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open CurrentAdditive.GaussListContext
open CurrentAdditive.Wide96ContextListScheduler

theorem callback_post (pre : List (List Bool)) (word : List Bool)
    (suffix : List (List Bool)) (output context : List Bool)
    (extra : Fin 96 → List Bool) (T : Fin 96 → List Bool)
    (piece : List Bool)
    (h8 : T 8 = SourceListEncoding.encode (pre ++ word :: suffix))
    (h9 : T 9 = output ++ piece)
    (h10 : T 10 = List.replicate pre.length true)
    (h12 : T 12 = context)
    (h13 : T 13 = List.replicate suffix.length true)
    (hExtra : ∀ k : Fin 96, 15 ≤ k.val → T k = extra k) :
    Function.update
      (BitMachineClearBank.cleared Wide96ContextListScheduler.cleanBank T) 10
      (true :: (BitMachineClearBank.cleared
        Wide96ContextListScheduler.cleanBank T) 10) =
    (Wide96ContextPreservingScan.frame
      (foreignBank (output ++ piece) context suffix.length extra)
      (CylinderContextScanStep.initial
        (SourceListEncoding.encode (pre ++ word :: suffix))
        (pre.length + 1))).stk := by
  let F := Wide96ContextPreservingScan.frame
      (foreignBank (output ++ piece) context suffix.length extra)
      (CylinderContextScanStep.initial
        (SourceListEncoding.encode (pre ++ word :: suffix))
        (pre.length + 1))
  have himage (j : Fin 12) :
      F.stk (Wide96ContextPreservingScan.locate j) =
        (CylinderContextScanStep.initial
          (SourceListEncoding.encode (pre ++ word :: suffix))
          (pre.length + 1)).stk j := by
    exact Wide96ContextPreservingScan.frame_bank _ _ j
  have hforeign (k : Fin 96)
      (hk : ¬ ∃ j : Fin 12, Wide96ContextPreservingScan.locate j = k) :
      F.stk k =
        (foreignBank (output ++ piece) context suffix.length extra) k := by
    exact Wide96ContextPreservingScan.frame_foreign _ _ k hk
  have hclean_locate (j : Fin 12) :
      (∃ i : Fin 10, Wide96ContextListScheduler.cleanBank i =
        Wide96ContextPreservingScan.locate j) ↔ j ≠ 8 ∧ j ≠ 10 := by
    fin_cases j <;> decide
  have hclean_subimage (i : Fin 10) :
      ∃ j : Fin 12,
        Wide96ContextPreservingScan.locate j =
          Wide96ContextListScheduler.cleanBank i := by
    fin_cases i <;> decide
  have hclear_image (j : Fin 12) :
      BitMachineClearBank.cleared Wide96ContextListScheduler.cleanBank T
          (Wide96ContextPreservingScan.locate j) =
        if j ≠ 8 ∧ j ≠ 10 then [] else
          T (Wide96ContextPreservingScan.locate j) := by
    by_cases hp : ∃ i : Fin 10,
        Wide96ContextListScheduler.cleanBank i =
          Wide96ContextPreservingScan.locate j
    · have hq := (hclean_locate j).mp hp
      simp [BitMachineClearBank.cleared, hp, hq]
    · have hq : ¬ (j ≠ 8 ∧ j ≠ 10) := by
        intro h
        exact hp ((hclean_locate j).mpr h)
      simp [BitMachineClearBank.cleared, hp, hq]
  have hclear10 :
      BitMachineClearBank.cleared Wide96ContextListScheduler.cleanBank T 10 =
        T 10 := by
    have hn : ¬ ∃ i : Fin 10,
        Wide96ContextListScheduler.cleanBank i = (10 : Fin 96) := by decide
    simp [BitMachineClearBank.cleared, hn]
  have hresult (k : Fin 96) :
      (Function.update
        (BitMachineClearBank.cleared Wide96ContextListScheduler.cleanBank T) 10
        (true :: (BitMachineClearBank.cleared
          Wide96ContextListScheduler.cleanBank T) 10)) k =
      if k = 10 then true :: T 10 else
        BitMachineClearBank.cleared Wide96ContextListScheduler.cleanBank T k := by
    by_cases heq : k = 10 <;>
      simp [Function.update_apply, heq, hclear10]
  funext k
  change (Function.update
    (BitMachineClearBank.cleared Wide96ContextListScheduler.cleanBank T) 10
    (true :: (BitMachineClearBank.cleared
      Wide96ContextListScheduler.cleanBank T) 10)) k = F.stk k
  by_cases hk : ∃ j : Fin 12, Wide96ContextPreservingScan.locate j = k
  · obtain ⟨j, rfl⟩ := hk
    rw [hresult, himage, hclear_image]
    fin_cases j <;>
      simp [Wide96ContextPreservingScan.locate,
        CylinderContextScanStep.initial,
        CylinderContextScanStep.initialBank,
        h8, h10, List.replicate_succ]
  · rw [hforeign k hk]
    have hnc : ¬ ∃ i : Fin 10,
        Wide96ContextListScheduler.cleanBank i = k := by
      rintro ⟨i, hi⟩
      obtain ⟨j, hj⟩ := hclean_subimage i
      exact hk ⟨j, hj.trans hi⟩
    have hclear_outside :
        BitMachineClearBank.cleared Wide96ContextListScheduler.cleanBank T k =
          T k := by
      simp [BitMachineClearBank.cleared, hnc]
    rw [hresult, hclear_outside]
    by_cases hsmall : k.val < 15
    · fin_cases k <;> norm_num at hsmall <;>
        (first
          | (exfalso; exact hk (by decide))
          | (simp [foreignBank, h9, h12, h13]))
    · have hk15 : 15 ≤ k.val := by omega
      have hk10 : k ≠ 10 := by intro h; subst k; omega
      rw [if_neg hk10, hExtra k hk15]
      exact (foreignBank_extra (output ++ piece) context
        suffix.length extra k hk15).symm

#print axioms callback_post

end CurrentAdditive.CylinderSchedulerPost96
