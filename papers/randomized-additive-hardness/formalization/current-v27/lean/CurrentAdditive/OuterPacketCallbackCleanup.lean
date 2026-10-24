import CurrentAdditive.OuterPacketPhysicalJoin
import EthInapproximability.CurrentPaper.RegionClear

/-! Fixed cell numbering for clearing the outer packet builder's low work
region. Cells 0 and 6 retain the framed request and the next coordinate;
every other low cell is charged to a physical pop loop. -/

namespace CurrentAdditive.IndexedExecutableStepRecovery

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open CurrentAdditive.MinimumRatioContext.MachineInvokeCore
open Turing

def callbackCleanupBank : Fin 30 → StackN contextTwoSize :=
  fun i => ⟨if i.val < 5 then i.val + 1 else i.val + 2, by
    split_ifs <;> omega⟩

theorem callbackCleanupBank_injective : Function.Injective callbackCleanupBank := by
  intro i j h
  apply Fin.ext
  have hv := congrArg Fin.val h
  dsimp [callbackCleanupBank] at hv
  split_ifs at hv <;> omega

theorem callbackCleanupBank_covers (k : StackN contextTwoSize)
    (hlo : 1 ≤ k.val) (hhi : k.val < 32) (h6 : k.val ≠ 6) :
    ∃ i : Fin 30, callbackCleanupBank i = k := by
  by_cases h : k.val < 6
  · refine ⟨⟨k.val - 1, by omega⟩, ?_⟩
    apply Fin.ext
    have hh : k.val - 1 < 5 := by omega
    simp only [callbackCleanupBank, Fin.val_mk, if_pos hh]
    omega
  · refine ⟨⟨k.val - 2, by omega⟩, ?_⟩
    apply Fin.ext
    have hh : ¬ k.val - 2 < 5 := by omega
    simp only [callbackCleanupBank, Fin.val_mk, if_neg hh]
    omega

theorem callbackCleanupBank_avoids_zero_six (i : Fin 30) :
    callbackCleanupBank i ≠ (0 : StackN contextTwoSize) ∧
    callbackCleanupBank i ≠ (6 : StackN contextTwoSize) := by
  have hval0 : (0 : StackN contextTwoSize).val = 0 := by
    simp [StackN]
  have hval6 : (6 : StackN contextTwoSize).val = 6 := by
    simp [StackN, Nat.mod_eq_of_lt (by omega : 6 < 32 + contextTwoSize)]
  constructor <;> intro h
  all_goals
    have hv := congrArg Fin.val h
    simp only [callbackCleanupBank, Fin.val_mk, hval0, hval6] at hv
    split_ifs at hv <;> omega

theorem callback_cleanup_run
    (S : StackN contextTwoSize → List Bool) (B : ℕ)
    (hB : ∀ i : Fin 30, (S (callbackCleanupBank i)).length ≤ B) :
    ∃ t ≤ 30*B + 32,
      ((advance (RegionClear.prog 30 callbackCleanupBank))^[t])
        (⟨some 0, ((), none), S⟩ :
          TM2.Cfg (fun _ : StackN contextTwoSize => Bool) _ _) =
      ⟨none, ((), none),
        BitMachineClearBank.cleared callbackCleanupBank S⟩ :=
  RegionClear.clear_run 30 callbackCleanupBank
    callbackCleanupBank_injective S B hB

theorem callback_cleanup_retains
    (S : StackN contextTwoSize → List Bool) :
    let T := BitMachineClearBank.cleared callbackCleanupBank S
    T 0 = S 0 ∧ T 6 = S 6 ∧
      (∀ k : StackN contextTwoSize,
        1 ≤ k.val → k.val < 32 → k.val ≠ 6 → T k = []) := by
  dsimp only
  constructor
  · simp [BitMachineClearBank.cleared,
      fun i => (callbackCleanupBank_avoids_zero_six i).1]
  constructor
  · simp [BitMachineClearBank.cleared,
      fun i => (callbackCleanupBank_avoids_zero_six i).2]
  · intro k hlo hhi h6
    obtain ⟨i, hi⟩ := callbackCleanupBank_covers k hlo hhi h6
    simp [BitMachineClearBank.cleared, ← hi]

theorem callback_cleanup_high_preserved
    (S : StackN contextTwoSize → List Bool)
    (k : StackN contextTwoSize) (hk : 32 ≤ k.val) :
    BitMachineClearBank.cleared callbackCleanupBank S k = S k := by
  simp only [BitMachineClearBank.cleared]
  split_ifs with h
  · obtain ⟨i, hi⟩ := h
    have hv := congrArg Fin.val hi
    dsimp [callbackCleanupBank] at hv
    split_ifs at hv <;> omega
  · rfl

#print axioms callbackCleanupBank_injective
#print axioms callback_cleanup_run
#print axioms callback_cleanup_retains
#print axioms callback_cleanup_high_preserved

end CurrentAdditive.IndexedExecutableStepRecovery
