import CurrentAdditive.V2ItemFrameCore

/-! Full-bank preservation outside the ten disposable banks. -/

namespace CurrentAdditive.V2ItemFrameForeign

open EthInapproximability.CurrentPaper
open CurrentAdditive.MinimumRatioContext
open CurrentAdditive.V2ItemFrameCore

theorem clearBank_foreign {N : ℕ} (C : Slots N)
    (k : MachineInvokeCore.StackN N)
    (ht : k ≠ C.target) (hs : k ≠ C.scratch)
    (hm : ∀ i, k ≠ C.machine i) :
    ∀ j, clearBank C j ≠ k := by
  intro j
  by_cases h0 : j.val = 0
  · simpa [clearBank, h0] using ht.symm
  by_cases h1 : j.val = 1
  · simpa [clearBank, h0, h1] using hs.symm
  simpa [clearBank, h0, h1] using
    (hm ⟨j.val-2, by
      have hj := j.isLt
      have hw : (SourceListMachineWriter.framingMachine true).stackCount = 8 := rfl
      rw [hw]
      omega⟩).symm

theorem cleared_foreign {N : ℕ} (C : Slots N)
    (S : MachineInvokeCore.StackN N → List Bool)
    (k : MachineInvokeCore.StackN N)
    (ht : k ≠ C.target) (hs : k ≠ C.scratch)
    (hm : ∀ i, k ≠ C.machine i) :
    cleared C S k = S k := by
  exact BitMachineClearBank.cleared_foreign (clearBank C) S k
    (clearBank_foreign C k ht hs hm)

theorem framed_foreign {N : ℕ} (C : Slots N)
    (S : MachineInvokeCore.StackN N → List Bool) (raw : List Bool)
    (k : MachineInvokeCore.StackN N)
    (ht : k ≠ C.target) (hs : k ≠ C.scratch)
    (hm : ∀ i, k ≠ C.machine i) :
    (Function.update (cleared C S) C.target
      (EncodedCommunication.natField raw.length ++ raw)) k = S k := by
  rw [Function.update_of_ne ht, cleared_foreign C S k ht hs hm]

#print axioms framed_foreign

end CurrentAdditive.V2ItemFrameForeign
