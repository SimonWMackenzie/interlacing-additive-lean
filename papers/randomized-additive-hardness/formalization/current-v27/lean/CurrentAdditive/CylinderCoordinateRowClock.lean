import CurrentAdditive.CylinderCoordinateRowRun
import CurrentAdditive.CylinderCallbackPhysicalEmptyClock

/-! An input-dependent clock for the actual canonical selected tuple callback.
All 15 scratch banks start empty in the scheduler's selected frame. -/

namespace CurrentAdditive.CylinderCoordinateRowClock

open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open CurrentAdditive.GaussListContext
open CurrentAdditive.CylinderCoordinateEqualityCallback
open CurrentAdditive.CylinderCoordinateRowRun

def pairBound (pre : List (List Bool)) (word : List Bool)
    (suffix : List (List Bool)) (right out : List Bool) : Nat :=
  let base := getterBound pre word suffix + 1 +
    CylinderEqualityAppendCallback.callbackBound word right out
  base + 15 * (BitMachineStackGrowth.perStep program * base) + 17

theorem canonical_selected_run_clock (outerPre : List (List Bool))
    (outerWord : List Bool) (outerSuffix : List (List Bool))
    (coordPre : List (List Bool)) (coordWord : List Bool)
    (coordSuffix : List (List Bool))
    (output context symbol : List Bool)
    (hword : outerWord = SourceListEncoding.encode
      (coordPre ++ coordWord :: coordSuffix))
    (index : Nat) (hindex : index = coordPre.length) :
    let S := (selected outerPre outerWord outerSuffix output
      context index symbol).stk
    ∃ (t : Nat) (vFinal : Control)
      (SFinal : Fin 32 → List Bool),
      t ≤ pairBound coordPre coordWord coordSuffix symbol output ∧
      run t
        ⟨some (.inl (.inl .scan)),
         getterControl (CylinderContextScanStep.copyControl ((), none)),
         S⟩ = ⟨none, vFinal, SFinal⟩ ∧
      SFinal 9 = output ++ [decide (coordWord = symbol)] ∧
      (∀ i : Fin 15, SFinal (cleanBank i) = []) ∧
      (∀ k : Fin 32,
        k = 8 ∨ k = 10 ∨ k = 12 ∨ k = 13 ∨ k = 15 ∨ k = 16 →
          SFinal k = S k) := by
  dsimp only
  let S := (selected outerPre outerWord outerSuffix output
    context index symbol).stk
  have h16 : S 16 = symbol := by
    simpa [S, pairExtra] using selected_extra outerPre outerWord
      outerSuffix output context index symbol 16 (by decide)
  have h9 : S 9 = output :=
    selected_output outerPre outerWord outerSuffix output context
      index symbol
  have hs (k : Fin 32) (hk : 17 ≤ k.val) : S k = [] := by
    simpa [S, pairExtra, show k ≠ (15 : Fin 32) by omega,
      show k ≠ (16 : Fin 32) by omega]
      using selected_extra outerPre outerWord outerSuffix
        output context index symbol k (by omega)
  have hstart := getter_match outerPre outerWord outerSuffix
    output context index symbol
  change getterFrame S
    (CylinderContextScanStep.initial outerWord index) =
    ⟨some (.inl (.inl .scan)),
     getterControl (CylinderContextScanStep.copyControl ((), none)),
     S⟩ at hstart
  rw [hword, hindex] at hstart
  have hEmpty : ∀ i : Fin 15,
      (getterFrame S
        (CylinderContextScanStep.initial
          (SourceListEncoding.encode
            (coordPre ++ coordWord :: coordSuffix))
          coordPre.length)).stk (cleanBank i) = [] := by
    intro i
    rw [hstart]
    exact hs (cleanBank i) (by simp [cleanBank])
  have h27 := hs 27 (by decide)
  have h28 := hs 28 (by decide)
  have h29 := hs 29 (by decide)
  obtain ⟨t, v, T, B, ht, hr, ho, _, hclean, hpres⟩ :=
    physical_coordinate_pair_empty_bounded
      coordPre coordWord coordSuffix symbol output S
      h16 h9 h27 h28 h29 hEmpty
  rw [hstart] at hr
  refine ⟨t, v, T, ?_, hr, ho, hclean, ?_⟩
  · simpa [pairBound] using ht
  · intro k hk
    rw [hpres k hk]
    exact congrArg (fun c => c.stk k) hstart

#print axioms canonical_selected_run_clock

end CurrentAdditive.CylinderCoordinateRowClock
