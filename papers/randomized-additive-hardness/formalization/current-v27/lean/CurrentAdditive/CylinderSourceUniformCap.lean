import CurrentAdditive.CylinderSourceCycleCap

/-! A finite, explicit maximum of the charged costs of every split of the
fixed source.  The list includes duplicate retained tuple words separately. -/

noncomputable section

namespace CurrentAdditive.CylinderSourceUniformCap

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open CurrentAdditive.CylinderSourceTupleProjection
open CurrentAdditive.CylinderSourceContractPrep
open CurrentAdditive.CylinderSourceClockContract
open CurrentAdditive.CylinderSourceCycleCap
open CurrentAdditive.LargeContextListScheduler
open CurrentAdditive.SourceContextScheduler
open CurrentAdditive.CylinderCoordinateEqualityCallback

def splitCaps {q : Nat}
    (source : Array ((Fin q → Nat) × ℚ))
    (i : Fin q) (y : Nat) (initialOutput context : List Bool)
    (pre : List (List Bool)) : List (List Bool) → List Nat
  | [] => []
  | word :: suffix =>
      splitCap source i y initialOutput context pre word suffix ::
        splitCaps source i y initialOutput context (pre ++ [word]) suffix

def uniformCap {q : Nat}
    (source : Array ((Fin q → Nat) × ℚ))
    (i : Fin q) (y : Nat) (initialOutput context : List Bool) : Nat :=
  (splitCaps source i y initialOutput context []
    (tupleWords source)).foldl max 0

private theorem start_le_foldl_max (xs : List Nat) (a : Nat) :
    a ≤ xs.foldl max a := by
  induction xs generalizing a with
  | nil => simp
  | cons x xs ih =>
      simpa only [List.foldl_cons] using
        (Nat.le_max_left a x).trans (ih (max a x))

private theorem mem_le_foldl_max (xs : List Nat) (a x : Nat)
    (hx : x ∈ xs) : x ≤ xs.foldl max a := by
  induction xs generalizing a with
  | nil => simp at hx
  | cons y ys ih =>
      rcases List.mem_cons.mp hx with h | h
      · subst x
        simpa only [List.foldl_cons] using
          (Nat.le_max_right a y).trans
            (start_le_foldl_max ys (max a y))
      · simpa only [List.foldl_cons] using ih (max a y) h

private theorem splitCap_mem_from {q : Nat}
    (source : Array ((Fin q → Nat) × ℚ))
    (i : Fin q) (y : Nat) (initialOutput context : List Bool)
    (stem pre : List (List Bool)) (word : List Bool)
    (suffix : List (List Bool)) :
    splitCap source i y initialOutput context
      (stem ++ pre) word suffix ∈
    splitCaps source i y initialOutput context stem
      (pre ++ word :: suffix) := by
  induction pre generalizing stem with
  | nil => simp [splitCaps]
  | cons head rest ih =>
      simp only [List.cons_append, splitCaps]
      apply List.mem_cons_of_mem
      simpa only [List.append_assoc, List.singleton_append] using
        ih (stem ++ [head])

theorem splitCap_le_uniformCap {q : Nat}
    (source : Array ((Fin q → Nat) × ℚ))
    (i : Fin q) (y : Nat) (initialOutput context : List Bool)
    (pre : List (List Bool)) (word : List Bool)
    (suffix : List (List Bool))
    (hSplit : pre ++ word :: suffix = tupleWords source) :
    splitCap source i y initialOutput context pre word suffix ≤
      uniformCap source i y initialOutput context := by
  have hm := splitCap_mem_from source i y initialOutput context
    [] pre word suffix
  simp only [List.nil_append] at hm
  rw [hSplit] at hm
  exact mem_le_foldl_max _ 0 _ hm

theorem cycleBudget_le_uniformCap {q : Nat}
    (source : Array ((Fin q → Nat) × ℚ))
    (i : Fin q) (y : Nat) (initialOutput context : List Bool)
    (pre : List (List Bool)) (word : List Bool)
    (suffix : List (List Bool))
    (hSplit : pre ++ word :: suffix = tupleWords source) :
    SourceContextScheduler.cycleBudget
      CylinderCoordinateEqualityCallback.program
      callbackStart callbackInit (piece i.val y.bits)
      initialOutput context (tupleWords source)
      (clockContract source i y initialOutput context)
      pre word suffix ≤ uniformCap source i y initialOutput context :=
  (cycleBudget_le_splitCap source i y initialOutput context pre word suffix
    hSplit).trans
    (splitCap_le_uniformCap source i y initialOutput context
      pre word suffix hSplit)

#print axioms splitCap_le_uniformCap
#print axioms cycleBudget_le_uniformCap

end CurrentAdditive.CylinderSourceUniformCap
