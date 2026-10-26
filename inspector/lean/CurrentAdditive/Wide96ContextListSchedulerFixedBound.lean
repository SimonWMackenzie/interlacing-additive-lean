import CurrentAdditive.Wide96ContextListSchedulerRun

/-!
A useful fixed-input clock bound for the physical list scheduler. The cycle
cap is required only for cuts of one given source list, not for every list.
-/

namespace CurrentAdditive.Wide96ContextListScheduler

open EthInapproximability.CurrentPaper
open Turing BitMachineEncoding

variable {L V : Type} [DecidableEq L] [Fintype L]
    [DecidableEq V] [Fintype V]

theorem remainingBudget_fixed_input
    (callback : L → TM2.Stmt (fun _ : Stack => Bool) L V)
    (callbackStart : L) (callbackInit : V)
    (piece : List Bool → List Bool)
    (initialOutput context : List Bool)
    (C : CallbackContract callback callbackStart callbackInit piece
      initialOutput context)
    (original : List (List Bool)) (P : Nat)
    (hP : ∀ a word b, a ++ word :: b = original →
      cycleBudget callback callbackStart callbackInit piece
        initialOutput context C a word b ≤ P)
    (pre suffix : List (List Bool))
    (hSplit : pre ++ suffix = original) :
    remainingBudget callback callbackStart callbackInit piece
      initialOutput context C pre suffix ≤
      (suffix.length + 1) * (P + 1) := by
  induction suffix generalizing pre with
  | nil => simp [remainingBudget]
  | cons word tail ih =>
      have hc := hP pre word tail hSplit
      have hs : (pre ++ [word]) ++ tail = original := by
        simpa only [List.append_assoc, List.singleton_append] using hSplit
      have ht := ih (pre ++ [word]) hs
      simp only [remainingBudget, List.length_cons]
      nlinarith

theorem run_remaining_fixed_input
    (callback : L → TM2.Stmt (fun _ : Stack => Bool) L V)
    (callbackStart : L) (callbackInit : V)
    (piece : List Bool → List Bool)
    (initialOutput context : List Bool)
    (C : CallbackContract callback callbackStart callbackInit piece
      initialOutput context)
    (original : List (List Bool)) (P : Nat)
    (hP : ∀ a word b, a ++ word :: b = original →
      cycleBudget callback callbackStart callbackInit piece
        initialOutput context C a word b ≤ P)
    (pre suffix : List (List Bool))
    (hSplit : pre ++ suffix = original) (v : Control V) :
    let source := SourceListEncoding.encode original
    let output := initialOutput ++ joined piece pre
    ∃ t ≤ (suffix.length + 1) * (P + 1),
      ∃ vFinal : Control V,
      run callback callbackStart callbackInit t
        ⟨some (.inr (.inr .check)), v,
         (Wide96ContextPreservingScan.frame
           (foreignBank output context suffix.length C.extra)
           (CylinderContextScanStep.initial source pre.length)).stk⟩ =
        ⟨none, vFinal,
         (Wide96ContextPreservingScan.frame
           (foreignBank (initialOutput ++ joined piece original)
             context 0 C.extra)
           (CylinderContextScanStep.initial source
             original.length)).stk⟩ := by
  have hr := run_remaining callback callbackStart callbackInit piece
    initialOutput context C pre suffix v
  have hb := remainingBudget_fixed_input callback callbackStart
    callbackInit piece initialOutput context C original P hP pre suffix hSplit
  rcases hr with ⟨t, ht, vFinal, he⟩
  refine ⟨t, ht.trans hb, vFinal, ?_⟩
  simpa only [hSplit] using he

#print axioms remainingBudget_fixed_input
#print axioms run_remaining_fixed_input

end CurrentAdditive.Wide96ContextListScheduler
