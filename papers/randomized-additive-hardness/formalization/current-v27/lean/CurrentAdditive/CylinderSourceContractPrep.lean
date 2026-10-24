import CurrentAdditive.CylinderReachableRowCallback

/-! Uniform choice of actual callback runs at the reachable splits of one
fixed production source. The full scheduler contract additionally needs the
separate full-bank postcondition. -/

noncomputable section

namespace CurrentAdditive.CylinderSourceContractPrep

open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open CurrentAdditive.GaussListContext
open CurrentAdditive.CylinderSourceTupleProjection
open CurrentAdditive.CylinderActualTupleRow
open CurrentAdditive.LargeContextListScheduler
open CurrentAdditive.CylinderCoordinateEqualityCallback

abbrev Witness := Nat × Control × (Fin 32 → List Bool)

def piece (i : Nat) (symbol : List Bool) : List Bool → List Bool :=
  coordinatePiece i symbol

def callbackSelected {q : Nat}
    (source : Array ((Fin q → Nat) × ℚ))
    (i : Fin q) (y : Nat) (initialOutput context : List Bool)
    (pre : List (List Bool)) (word : List Bool)
    (suffix : List (List Bool)) : Fin 32 → List Bool :=
  let output := initialOutput ++ joined (piece i.val y.bits) pre
  (LargeContextPreservingScan.frame
    (foreignBank output context suffix.length
      (CylinderCoordinateRowRun.pairExtra i.val y.bits))
    (⟨none,
     CylinderContextScanStep.getterControl
       (PreservingV2Program.v2Control
         (IndexedV2Program.indexControl
           (SourceListMachineFields.coreControl (some true, false), none))),
     CylinderContextScanStep.selectedBank
       (SourceListEncoding.encode (tupleWords source))
       (SourceListEncoding.fields suffix) word pre.length⟩ :
      CylinderContextScanStep.Config)).stk

def callbackStart : Label := .inl (.inl .scan)
def callbackInit : Control :=
  getterControl (CylinderContextScanStep.copyControl ((), none))

def callbackRun (t : Nat) (S : Fin 32 → List Bool) :
    CylinderCoordinateEqualityCallback.Config :=
  run t ⟨some callbackStart, callbackInit, S⟩

theorem witness_exists {q : Nat}
    (source : Array ((Fin q → Nat) × ℚ))
    (i : Fin q) (y : Nat) (initialOutput context : List Bool)
    (pre : List (List Bool)) (word : List Bool)
    (suffix : List (List Bool))
    (hSplit : pre ++ word :: suffix = tupleWords source) :
    ∃ w : Witness,
      callbackRun w.1
        (callbackSelected source i y initialOutput context pre word suffix) =
          ⟨none, w.2.1, w.2.2⟩ ∧
      w.2.2 9 =
        (initialOutput ++ joined (piece i.val y.bits) pre) ++
          piece i.val y.bits word ∧
      (∀ k : Fin 15,
        w.2.2 (cleanBank k) = []) ∧
      (∀ k : Fin 32,
        k = 8 ∨ k = 10 ∨ k = 12 ∨ k = 13 ∨ k = 15 ∨ k = 16 →
          w.2.2 k =
            callbackSelected source i y initialOutput context
              pre word suffix k) := by
  obtain ⟨t, v, T, hr, ho, hc, hp⟩ :=
    CylinderReachableRowCallback.reachable_run source i y
      initialOutput context pre word suffix hSplit
  exact ⟨(t, v, T), hr, ho, hc, hp⟩

def defaultWitness : Witness :=
  (0, callbackInit, fun _ => [])

def chosenWitness {q : Nat}
    (source : Array ((Fin q → Nat) × ℚ))
    (i : Fin q) (y : Nat) (initialOutput context : List Bool)
    (pre : List (List Bool)) (word : List Bool)
    (suffix : List (List Bool)) : Witness :=
  if h : pre ++ word :: suffix = tupleWords source then
    Classical.choose (witness_exists source i y initialOutput context
      pre word suffix h)
  else defaultWitness

theorem chosenWitness_spec {q : Nat}
    (source : Array ((Fin q → Nat) × ℚ))
    (i : Fin q) (y : Nat) (initialOutput context : List Bool)
    (pre : List (List Bool)) (word : List Bool)
    (suffix : List (List Bool))
    (hSplit : pre ++ word :: suffix = tupleWords source) :
    let w := chosenWitness source i y initialOutput context pre word suffix
    callbackRun w.1
      (callbackSelected source i y initialOutput context pre word suffix) =
        ⟨none, w.2.1, w.2.2⟩ ∧
    w.2.2 9 =
      (initialOutput ++ joined (piece i.val y.bits) pre) ++
        piece i.val y.bits word ∧
    (∀ k : Fin 15, w.2.2 (cleanBank k) = []) ∧
    (∀ k : Fin 32,
      k = 8 ∨ k = 10 ∨ k = 12 ∨ k = 13 ∨ k = 15 ∨ k = 16 →
        w.2.2 k =
          callbackSelected source i y initialOutput context
            pre word suffix k) := by
  dsimp only [chosenWitness]
  rw [dif_pos hSplit]
  exact Classical.choose_spec (witness_exists source i y
    initialOutput context pre word suffix hSplit)

#print axioms chosenWitness_spec

end CurrentAdditive.CylinderSourceContractPrep
