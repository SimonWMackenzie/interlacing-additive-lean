import CurrentAdditive.CylinderSourceContractPrep
import CurrentAdditive.CylinderCanonicalPairBound

/-! The charged callback witness is chosen only at real splits of the fixed
production source.  Its numerical bound is a function of the selected word
and the current output prefix. -/

noncomputable section

namespace CurrentAdditive.CylinderSourceContractClockPrep

open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open CurrentAdditive.GaussListContext
open CurrentAdditive.CylinderSourceTupleProjection
open CurrentAdditive.CylinderActualTupleRow
open CurrentAdditive.CylinderSourceContractPrep
open CurrentAdditive.CylinderCoordinateEqualityCallback
open CurrentAdditive.CylinderCanonicalPairBound

theorem witness_exists_clock {q : Nat}
    (source : Array ((Fin q → Nat) × ℚ))
    (i : Fin q) (y : Nat) (initialOutput context : List Bool)
    (pre : List (List Bool)) (word : List Bool)
    (suffix : List (List Bool))
    (hSplit : pre ++ word :: suffix = tupleWords source) :
    ∃ w : Witness,
      w.1 ≤ wordPairBound i.val y.bits word
        (initialOutput ++ LargeContextListScheduler.joined
          (piece i.val y.bits) pre) ∧
      callbackRun w.1
        (callbackSelected source i y initialOutput context pre word suffix) =
          ⟨none, w.2.1, w.2.2⟩ ∧
      w.2.2 9 =
        (initialOutput ++ LargeContextListScheduler.joined
          (piece i.val y.bits) pre) ++ piece i.val y.bits word ∧
      (∀ k : Fin 15, w.2.2 (cleanBank k) = []) ∧
      (∀ k : Fin 32,
        k = 8 ∨ k = 10 ∨ k = 12 ∨ k = 13 ∨ k = 15 ∨ k = 16 →
          w.2.2 k =
            callbackSelected source i y initialOutput context
              pre word suffix k) := by
  have hmem : word ∈ tupleWords source := by
    rw [← hSplit]
    simp
  obtain ⟨entry, he, hw, t, v, T, ht, hr, ho, hc, hp⟩ :=
    CurrentAdditive.CylinderReachableRowClock.actual_member_selected_run_bounded
      source pre word suffix hmem i y
      (initialOutput ++ LargeContextListScheduler.joined
        (piece i.val y.bits) pre) context
  let output := initialOutput ++ LargeContextListScheduler.joined
    (piece i.val y.bits) pre
  have hb : t ≤ wordPairBound i.val y.bits word output := by
    rw [hw, wordPairBound_canonical]
    exact ht
  have hs : callbackSelected source i y initialOutput context
      pre word suffix =
      (CylinderCoordinateRowRun.selected pre word suffix output
        context i.val y.bits).stk := by
    simp only [callbackSelected, CylinderCoordinateRowRun.selected,
      output, ← hSplit]
  refine ⟨(t, v, T), hb, ?_, ?_, hc, ?_⟩
  · simpa only [callbackRun, callbackStart, callbackInit,
      output, ← hs] using hr
  · simpa only [output] using ho
  · intro k hk
    rw [hs]
    exact hp k hk

def chosenClockWitness {q : Nat}
    (source : Array ((Fin q → Nat) × ℚ))
    (i : Fin q) (y : Nat) (initialOutput context : List Bool)
    (pre : List (List Bool)) (word : List Bool)
    (suffix : List (List Bool)) : Witness :=
  if h : pre ++ word :: suffix = tupleWords source then
    Classical.choose (witness_exists_clock source i y initialOutput
      context pre word suffix h)
  else defaultWitness

theorem chosenClockWitness_spec {q : Nat}
    (source : Array ((Fin q → Nat) × ℚ))
    (i : Fin q) (y : Nat) (initialOutput context : List Bool)
    (pre : List (List Bool)) (word : List Bool)
    (suffix : List (List Bool))
    (hSplit : pre ++ word :: suffix = tupleWords source) :
    let w := chosenClockWitness source i y initialOutput context
      pre word suffix
    w.1 ≤ wordPairBound i.val y.bits word
      (initialOutput ++ LargeContextListScheduler.joined
        (piece i.val y.bits) pre) ∧
    callbackRun w.1
      (callbackSelected source i y initialOutput context pre word suffix) =
        ⟨none, w.2.1, w.2.2⟩ ∧
    w.2.2 9 =
      (initialOutput ++ LargeContextListScheduler.joined
        (piece i.val y.bits) pre) ++ piece i.val y.bits word ∧
    (∀ k : Fin 15, w.2.2 (cleanBank k) = []) ∧
    (∀ k : Fin 32,
      k = 8 ∨ k = 10 ∨ k = 12 ∨ k = 13 ∨ k = 15 ∨ k = 16 →
        w.2.2 k =
          callbackSelected source i y initialOutput context
            pre word suffix k) := by
  dsimp only [chosenClockWitness]
  rw [dif_pos hSplit]
  exact Classical.choose_spec (witness_exists_clock source i y
    initialOutput context pre word suffix hSplit)

#print axioms witness_exists_clock
#print axioms chosenClockWitness_spec

end CurrentAdditive.CylinderSourceContractClockPrep
