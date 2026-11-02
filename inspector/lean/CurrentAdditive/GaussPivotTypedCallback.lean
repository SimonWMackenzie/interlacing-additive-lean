import CurrentAdditive.GaussPivotTypedRows
import CurrentAdditive.GaussPivotCallbackFrame

set_option maxHeartbeats 1000000

namespace CurrentAdditive.GaussPivotTypedCallback

open EthInapproximability.CurrentPaper
open CurrentAdditive.GaussPivotCallbackFrame
open CurrentAdditive.GaussPivotTypedRows
open CurrentAdditive.GaussPivotTypedScan
open CurrentAdditive.GaussTypedGetterBridge
open CurrentAdditive.GaussPhysical
open CurrentAdditive.CodeDCodec
open CurrentAdditive.GaussRowZeroCallback

abbrev Stack := Fin 32

theorem witness {m k : Nat} (B : Fin m → Fin k → ℚ)
    (j : Fin k) (pre : List (List Bool)) (word : List Bool)
    (suffix : List (List Bool)) (r state : List Bool)
    (h : pre ++ word :: suffix = rowWords B) :
    let output := reversed (piece j.val) pre
    let S := (selected pre word suffix output
      (List.replicate j.val true) r state).stk
    ∃ t v T,
      (∃ i : Fin m, ∃ cellPre cellSuffix : List (List Bool),
        cellPre.length = j.val ∧
        word = SourceListEncoding.encode
          (cellPre ++ encodeRawRat (rawOfRat (B i j)) :: cellSuffix) ∧
        t ≤ callbackCost cellPre
          (encodeRawRat (rawOfRat (B i j))) cellSuffix S) ∧
      GaussRowZeroCallback.run t
        ⟨some (bLabel .scan), bControl ((), none), S⟩ =
          ⟨none, v, T⟩ ∧
      T 9 = piece j.val word :: output ∧
      (∀ i : Fin 15, T (clearBank i) = []) ∧
      (∀ x : Stack,
        x = 8 ∨ x = 10 ∨ x = 12 ∨ x = 13 ∨ x = 30 ∨ x = 31 →
        T x = S x) := by
  dsimp only
  obtain ⟨i, cellPre, cellSuffix, hi, hj, hw⟩ :=
    row_cell_split B j pre word suffix h
  obtain ⟨i', hi', hw'⟩ := row_split B pre word suffix h
  have heq : i' = i := Fin.ext (hi'.trans hi.symm)
  have hpiece : piece j.val word = decide (B i j ≠ 0) := by
    simpa only [hw', heq] using piece_typed B i j
  let cell := encodeRawRat (rawOfRat (B i j))
  let output := reversed (piece j.val) pre
  obtain ⟨t, ht, v, hr, ho, hs, hp⟩ :=
    selected_cell_run pre word suffix output r state
      cellPre cell cellSuffix (by simpa only [cell] using hw)
  refine ⟨t, v, finalState cellPre cell cellSuffix
    (selected pre word suffix output (List.replicate j.val true) r state).stk,
    ?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨i, cellPre, cellSuffix, hj, hw, ?_⟩
    simpa only [output, hj, cell] using ht
  · simpa only [output, hj, cell] using hr
  · simpa only [output, hj, cell, hpiece,
      numerator_nonzero (B i j)] using ho
  · simpa only [output, hj, cell] using hs
  · simpa only [output, hj, cell] using hp

end CurrentAdditive.GaussPivotTypedCallback
