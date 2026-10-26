import CurrentAdditive.GaussCallbackClock
import CurrentAdditive.GaussControlTrace

set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

namespace CurrentAdditive.GaussSearchRuntime

open EthInapproximability.CurrentPaper
open CurrentAdditive.GaussRowZeroCallback
open CurrentAdditive.GaussPivotTypedScan
open CurrentAdditive.GaussPivotTypedContract
open CurrentAdditive.GaussTypedGetterBridge

noncomputable def cycleClock (rows : List (List Bool)) : Nat :=
  let Q := (SourceListEncoding.encode rows).length + 1
  let K := 1000 * (Z.pushBound + 1)
  let p := BitMachineStackGrowth.perStep GaussRowZeroCallback.program
  50 * Q^3 + K * Q^3 + 10 * (Q + p * (K * Q^3)) + 14

theorem typed_cycle_bound {m k : Nat}
    (B : Fin m → Fin k → ℚ) (j : Fin k)
    (r : List Bool) (state : List Bool)
    (pre : List (List Bool)) (word : List Bool)
    (suffix : List (List Bool))
    (hsplit : pre ++ word :: suffix = rowWords B) :
    cycleBudget GaussRowZeroCallback.program (bLabel .scan)
      (bControl ((),none)) (rowWords B)
      (CurrentAdditive.GaussPivotTypedRows.piece j.val) []
      (List.replicate j.val true)
      (contract B j r state) pre word suffix ≤
      cycleClock (rowWords B) := by
  have hg := GaussSearchClock.getter_bound pre word suffix
  have hsrc : SourceListEncoding.encode (pre ++ word :: suffix) =
      SourceListEncoding.encode (rowWords B) := by rw [hsplit]
  rw [hsrc] at hg
  have ht := GaussCallbackClock.typed_callback_time_bound
    B j r state pre word suffix hsplit
  have ht' : (contract B j r state).time pre word suffix ≤
      1000 * (Z.pushBound + 1) *
        ((SourceListEncoding.encode (rowWords B)).length + 1)^3 := by
    simpa only [contract] using ht
  have hs := GaussCallbackClock.typed_callback_clean_sum_bound
    B j r state pre word suffix hsplit
  dsimp only at hs
  unfold cycleBudget cycleClock
  dsimp only
  omega

theorem typed_remaining_bound {m k : Nat}
    (B : Fin m → Fin k → ℚ) (j : Fin k)
    (r : List Bool) (state : List Bool) :
    remainingBudget GaussRowZeroCallback.program (bLabel .scan)
      (bControl ((),none)) (rowWords B)
      (CurrentAdditive.GaussPivotTypedRows.piece j.val) []
      (List.replicate j.val true)
      (contract B j r state) [] (rowWords B) ≤
      ((rowWords B).length + 1) * (cycleClock (rowWords B) + 2) := by
  apply GaussSearchClock.remainingBudget_le_of_cycle
  · intro pre word suffix hsplit
    exact typed_cycle_bound B j r state pre word suffix hsplit
  · simp

theorem search_run_clock {m k : Nat}
    (B : Fin m → Fin k → ℚ) (j : Fin k)
    (r : Nat) (state : List Bool) :
    let flags := (List.finRange m).map (fun i => decide (B i j ≠ 0))
    let S0 := (LargeContextPreservingScan.frame
      (LargeContextListScheduler.foreignBank []
        (List.replicate j.val true) m
        (CurrentAdditive.GaussPivotCallbackFrame.extra
          (List.replicate r true) state))
      (CylinderContextScanStep.initial
        (CurrentAdditive.GaussPhysical.encodeTypedMatrix B) 0)).stk
    ∃ t ≤ ((rowWords B).length + 1) *
        (cycleClock (rowWords B) + 2) + 2 * m + 6,
      ∃ vf : CurrentAdditive.GaussFlagSearch.Control,
      ∃ Sf : Fin 32 → List Bool,
      GaussPivotSearchController.run t
        (GaussPivotSearchController.initial S0) =
        ⟨some .done, .choose vf, Sf⟩ ∧
      Sf 19 = List.replicate
        (CurrentAdditive.GaussFlagSearch.firstHit flags r).2 true ∧
      Sf 20 = [(CurrentAdditive.GaussFlagSearch.firstHit flags r).1] ∧
      Sf 31 = state ∧ Sf 8 =
        CurrentAdditive.GaussPhysical.encodeTypedMatrix B := by
  dsimp only
  obtain ⟨t, ht, vf, Sf, hr, h19, h20, h31, h8⟩ :=
    GaussPivotSearchRun.search_run B j r state
  have hb := typed_remaining_bound B j
    (List.replicate r true) state
  exact ⟨t, by omega, vf, Sf, hr, h19, h20, h31, h8⟩

noncomputable def polynomialClock (N : Nat) : Nat :=
  let Q := N + 1
  let K := 1000 * (Z.pushBound + 1)
  let p := BitMachineStackGrowth.perStep GaussRowZeroCallback.program
  Q * (50 * Q^3 + K * Q^3 + 10 * (Q + p * (K * Q^3)) + 16) +
    2 * N + 6

theorem search_budget_input_le {m k : Nat}
    (s : GaussControlTrace.State m k) :
    ((rowWords s.B).length + 1) *
      (cycleClock (rowWords s.B) + 2) + 2 * m + 6 ≤
      polynomialClock (GaussControlTrace.statePacket s).length := by
  have hm : m ≤ (GaussControlTrace.statePacket s).length := by
    have hrow : (rowWords s.B).length = m := by simp [rowWords]
    have hcode := GaussSearchClock.rows_le_code (rowWords s.B)
    have heq := congrArg List.length (encodeTypedMatrix_eq s.B)
    have hp := GaussControlTrace.statePacket_length s
    omega
  have hrow : (rowWords s.B).length ≤
      (GaussControlTrace.statePacket s).length := by
    simp only [rowWords, List.length_map, List.length_finRange]
    exact hm
  have hcode : (SourceListEncoding.encode (rowWords s.B)).length ≤
      (GaussControlTrace.statePacket s).length := by
    have heq := congrArg List.length (encodeTypedMatrix_eq s.B)
    have hp := GaussControlTrace.statePacket_length s
    omega
  unfold cycleClock polynomialClock
  dsimp only
  gcongr

#print axioms typed_cycle_bound
#print axioms typed_remaining_bound
#print axioms search_run_clock
#print axioms search_budget_input_le

end CurrentAdditive.GaussSearchRuntime
