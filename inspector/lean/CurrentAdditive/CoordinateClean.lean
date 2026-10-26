import CurrentAdditive.CoordinatePayload

namespace CurrentAdditive.FiniteFieldCoordinate

set_option maxHeartbeats 2000000

open Turing EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper.BitMachineStackEmbedding
open CurrentAdditive.FiniteFieldConstructor.CanonicalTable

def clearProgram := RegionClear.prog 32 scratchSlots

def scratchBound (W : Stack → List Bool) : ℕ :=
  Finset.univ.sup (fun i : Fin 32 => (W (scratchSlots i)).length)

theorem clear_run (W : Stack → List Bool) :
    ∃ steps ≤ 32 * scratchBound W + 34,
      ((advance clearProgram)^[steps])
        (⟨some 0, ((), none), W⟩ : TM2.Cfg (fun _ : Stack => Bool) _ _) =
      ⟨none, ((), none), BitMachineClearBank.cleared scratchSlots W⟩ := by
  have hlen (i : Fin 32) : (W (scratchSlots i)).length ≤ scratchBound W := by
    unfold scratchBound
    exact Finset.le_sup (s := Finset.univ)
      (f := fun j : Fin 32 => (W (scratchSlots j)).length) (Finset.mem_univ i)
  simpa [clearProgram] using
    (RegionClear.clear_run 32 scratchSlots scratchSlots.injective W
      (scratchBound W) hlen)

theorem payloadOutput_public (H K : ℕ) (α : Fin H) (p : Fin (K + 1))
    (S : Stack → List Bool) (F : Fin 12 → List Bool)
    (k : Fin 7) :
    payloadOutput H K α p S F ⟨k.val, by omega⟩ = S ⟨k.val, by omega⟩ := by
  have hp : ¬ ∃ i : Fin 6, payloadSlots i = (⟨k.val, by omega⟩ : Stack) := by
    fin_cases k <;> decide
  have hs : ¬ ∃ i : Fin 12, selectorSlots i = (⟨k.val, by omega⟩ : Stack) := by
    fin_cases k <;> decide
  simp only [payloadOutput, bank_outside payloadSlots _ _ _ hp,
    widthReady, positioned]
  have hn33 : (⟨k.val, by omega⟩ : Stack) ≠ 33 := by fin_cases k <;> decide
  have hn29 : (⟨k.val, by omega⟩ : Stack) ≠ 29 := by fin_cases k <;> decide
  simp only [Function.update_of_ne hn33, Function.update_of_ne hn29,
    selected, bank_outside selectorSlots _ _ _ hs]
  exact staged_at_public S k

theorem payloadOutput_seven (H K : ℕ) (α : Fin H) (p : Fin (K + 1))
    (S : Stack → List Bool) (F : Fin 12 → List Bool) :
    payloadOutput H K α p S F 7 =
      List.replicate (α.val * (K + 1) + p.val) true := by
  have h := bank_at payloadSlots (widthReady S F p.val K)
    (Function.update
      (Function.update
        (Function.update (fun k => (widthReady S F p.val K) (payloadSlots k)) 0 []) 1 [])
      2 (List.replicate (α.val * (K + 1) + p.val) true))
    (2 : Fin 6)
  simpa [payloadOutput, payloadSlots] using h

theorem clear_payload (H K : ℕ) (α : Fin H) (p : Fin (K + 1))
    (S : Stack → List Bool) (F : Fin 12 → List Bool)
    (hblank : ∀ k : Stack, 7 ≤ k.val → S k = []) :
    BitMachineClearBank.cleared scratchSlots (payloadOutput H K α p S F) =
      Function.update S 7
        (List.replicate (α.val * (K + 1) + p.val) true) := by
  funext k
  by_cases hlarge : 8 ≤ k.val
  · have hk : ∃ i : Fin 32, scratchSlots i = k := by
      refine ⟨⟨k.val - 8, by omega⟩, ?_⟩
      apply Fin.ext
      simp only [scratchSlots_val, Fin.val_mk]
      omega
    have hk7 : k ≠ (7 : Stack) := by
      intro he
      subst k
      omega
    simp [BitMachineClearBank.cleared, hk, Function.update_of_ne hk7]
    exact hblank k (by omega)
  · have hsmall : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨
        k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 := by
      simp only [Fin.ext_iff]
      omega
    have hnot : ¬ ∃ i : Fin 32, scratchSlots i = k := by
      rintro ⟨i, hi⟩
      have hv := congrArg Fin.val hi
      rw [scratchSlots_val] at hv
      omega
    simp only [BitMachineClearBank.cleared, hnot, if_false]
    rcases hsmall with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | simpa using payloadOutput_seven H K α p S F
      | simpa using payloadOutput_public H K α p S F 0
      | simpa using payloadOutput_public H K α p S F 1
      | simpa using payloadOutput_public H K α p S F 2
      | simpa using payloadOutput_public H K α p S F 3
      | simpa using payloadOutput_public H K α p S F 4
      | simpa using payloadOutput_public H K α p S F 5
      | simpa using payloadOutput_public H K α p S F 6

end CurrentAdditive.FiniteFieldCoordinate
