import CurrentAdditive.CylinderSourceContractPrep
import CurrentAdditive.CylinderSchedulerPost

/-! One uniform physical callback contract for scanning every retained tuple
against a fixed coordinate and symbol. Invalid source words are outside its
premise; the source is the actual projected production V2 tuple list. -/

noncomputable section

namespace CurrentAdditive.CylinderSourceContract

open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open CurrentAdditive.GaussListContext
open CurrentAdditive.CylinderSourceTupleProjection
open CurrentAdditive.CylinderActualTupleRow
open CurrentAdditive.CylinderSourceContractPrep
open CurrentAdditive.LargeContextListScheduler
open CurrentAdditive.SourceContextScheduler
open CurrentAdditive.CylinderCoordinateEqualityCallback

def singletonContract {q : Nat}
    (source : Array ((Fin q → Nat) × ℚ))
    (i : Fin q) (y : Nat) (initialOutput context : List Bool) :
    SourceCallbackContract
      CylinderCoordinateEqualityCallback.program
      CylinderSourceContractPrep.callbackStart
      CylinderSourceContractPrep.callbackInit
      (piece i.val y.bits) initialOutput context (tupleWords source) := by
  refine {
    extra := CylinderCoordinateRowRun.pairExtra i.val y.bits
    time := fun pre word suffix =>
      (chosenWitness source i y initialOutput context pre word suffix).1
    control := fun pre word suffix =>
      (chosenWitness source i y initialOutput context pre word suffix).2.1
    state := fun pre word suffix =>
      (chosenWitness source i y initialOutput context pre word suffix).2.2
    callback_run := ?_
    post := ?_
  }
  · intro pre word suffix hSplit
    have hw := chosenWitness_spec source i y initialOutput context
      pre word suffix hSplit
    exact hw.1
  · intro pre word suffix hSplit
    let output := initialOutput ++ joined (piece i.val y.bits) pre
    let w := chosenWitness source i y initialOutput context pre word suffix
    have hw := chosenWitness_spec source i y initialOutput context
      pre word suffix hSplit
    have hs : callbackSelected source i y initialOutput context
        pre word suffix =
        (CylinderCoordinateRowRun.selected pre word suffix output
          context i.val y.bits).stk := by
      simp only [callbackSelected, CylinderCoordinateRowRun.selected,
        output, piece, ← hSplit]
    have hp : ∀ k : Fin 32,
        k = 8 ∨ k = 10 ∨ k = 12 ∨ k = 13 ∨ k = 15 ∨ k = 16 →
          w.2.2 k =
            (CylinderCoordinateRowRun.selected pre word suffix output
              context i.val y.bits).stk k := by
      intro k hk
      rw [← hs]
      exact hw.2.2.2 k hk
    have hpost := CurrentAdditive.CylinderSchedulerPost.callback_post
      pre word suffix output context i.val y.bits w.2.2
      (decide ((SourceListEncoding.decode word).bind
        (fun xs => xs[i.val]?) = some y.bits))
      (by simpa only [piece, coordinatePiece, output] using hw.2.1)
      hw.2.2.1 hp
    simpa only [output, piece,
      LargeContextListScheduler.joined_append_one,
      List.append_assoc, ← hSplit] using hpost

#print axioms singletonContract

end CurrentAdditive.CylinderSourceContract
