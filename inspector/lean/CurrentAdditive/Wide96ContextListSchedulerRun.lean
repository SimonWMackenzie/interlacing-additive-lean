import CurrentAdditive.Wide96ContextListScheduler

set_option maxHeartbeats 1000000

/-!
Whole-list execution of the contextual scheduler, conditional on a concrete
callback that physically appends the prescribed bytes and preserves its
context.  The scheduler's getter, cleanup, index increment, and item-count
loop are discharged here; only the callback's own machine run is a premise.
-/

namespace CurrentAdditive.Wide96ContextListScheduler

open EthInapproximability.CurrentPaper
open CurrentAdditive.Wide96ContextPreservingScan
open CurrentAdditive.GaussListContext
open Turing BitMachineEncoding

variable {L V : Type} [DecidableEq L] [Fintype L]
    [DecidableEq V] [Fintype V]

def joined (piece : List Bool → List Bool)
    (xs : List (List Bool)) : List Bool :=
  xs.flatMap piece

theorem joined_append (piece : List Bool → List Bool)
    (xs ys : List (List Bool)) :
    joined piece (xs ++ ys) = joined piece xs ++ joined piece ys := by
  simp [joined]

theorem joined_append_one (piece : List Bool → List Bool)
    (xs : List (List Bool)) (word : List Bool) :
    joined piece (xs ++ [word]) = joined piece xs ++ piece word := by
  simp [joined_append, joined]

/-- A concrete callback contract for every canonical list split. The local
callback run starts on the selected item and must append exactly `piece word`
on bank 9. `post` is the full resulting stack equality after the scheduler's
physical scratch cleanup and index increment. It includes the fixed extra
registers on banks 15 through 95 and the appended output. -/
structure CallbackContract
    (callback : L → TM2.Stmt (fun _ : Stack => Bool) L V)
    (callbackStart : L) (callbackInit : V)
    (piece : List Bool → List Bool)
    (initialOutput context : List Bool) where
  /-- Fixed callback-owned registers. In particular, banks 15 and 16 may
  carry the coordinate and bound throughout the whole list run. -/
  extra : Stack → List Bool
  time : (pre : List (List Bool)) → (word : List Bool) →
    (suffix : List (List Bool)) → Nat
  control : (pre : List (List Bool)) → (word : List Bool) →
    (suffix : List (List Bool)) → V
  state : (pre : List (List Bool)) → (word : List Bool) →
    (suffix : List (List Bool)) → Stack → List Bool
  callback_run : ∀ pre word suffix,
    let source := SourceListEncoding.encode (pre ++ word :: suffix)
    let output := initialOutput ++ joined piece pre
    let selected := Wide96ContextPreservingScan.frame
      (foreignBank output context suffix.length extra)
      (⟨none,
       CylinderContextScanStep.getterControl
         (PreservingV2Program.v2Control
           (IndexedV2Program.indexControl
             (SourceListMachineFields.coreControl (some true, false), none))),
       CylinderContextScanStep.selectedBank source
         (SourceListEncoding.fields suffix) word pre.length⟩ :
        CylinderContextScanStep.Config)
    ((advance callback)^[time pre word suffix])
      (⟨some callbackStart, callbackInit, selected.stk⟩ :
        TM2.Cfg (fun _ : Stack => Bool) L V) =
      ⟨none, control pre word suffix, state pre word suffix⟩
  post : ∀ pre word suffix,
    let source := SourceListEncoding.encode (pre ++ word :: suffix)
    let SOut := state pre word suffix
    Function.update
      (BitMachineClearBank.cleared cleanBank SOut) 10
      (true :: (BitMachineClearBank.cleared cleanBank SOut) 10) =
    (Wide96ContextPreservingScan.frame
      (foreignBank (initialOutput ++ joined piece (pre ++ [word]))
        context suffix.length extra)
      (CylinderContextScanStep.initial source (pre.length + 1))).stk

def getterBudget (pre : List (List Bool)) (word : List Bool)
    (suffix : List (List Bool)) : Nat :=
  let source := SourceListEncoding.encode (pre ++ word :: suffix)
  2 * pre.length + 5 +
    (2 * source.length + 5 +
      (4 * (pre ++ word :: suffix).length.bits.length + 6 +
        IndexedFieldProgram.fieldCost (pre ++ [word]))) + 1

def cycleBudget
    (callback : L → TM2.Stmt (fun _ : Stack => Bool) L V)
    (callbackStart : L) (callbackInit : V)
    (piece : List Bool → List Bool)
    (initialOutput context : List Bool)
    (C : CallbackContract callback callbackStart callbackInit piece
      initialOutput context)
    (pre : List (List Bool)) (word : List Bool)
    (suffix : List (List Bool)) : Nat :=
  getterBudget pre word suffix + (C.time pre word suffix + 1) + 1 +
    ((∑ i : Fin 10,
      ((C.state pre word suffix) (cleanBank i)).length) + 11) + 1

def remainingBudget
    (callback : L → TM2.Stmt (fun _ : Stack => Bool) L V)
    (callbackStart : L) (callbackInit : V)
    (piece : List Bool → List Bool)
    (initialOutput context : List Bool)
    (C : CallbackContract callback callbackStart callbackInit piece
      initialOutput context)
    (pre suffix : List (List Bool)) : Nat :=
  match suffix with
  | [] => 1
  | word :: tail =>
      1 + cycleBudget callback callbackStart callbackInit piece
        initialOutput context C pre word tail +
      remainingBudget callback callbackStart callbackInit piece
        initialOutput context C (pre ++ [word]) tail

theorem run_remaining
    (callback : L → TM2.Stmt (fun _ : Stack => Bool) L V)
    (callbackStart : L) (callbackInit : V)
    (piece : List Bool → List Bool)
    (initialOutput context : List Bool)
    (C : CallbackContract callback callbackStart callbackInit piece
      initialOutput context)
    (pre suffix : List (List Bool)) (v : Control V) :
    let source := SourceListEncoding.encode (pre ++ suffix)
    let output := initialOutput ++ joined piece pre
    ∃ t ≤ remainingBudget callback callbackStart callbackInit piece
        initialOutput context C pre suffix,
      ∃ vFinal : Control V,
      run callback callbackStart callbackInit t
        ⟨some (.inr (.inr .check)), v,
         (Wide96ContextPreservingScan.frame
           (foreignBank output context suffix.length C.extra)
           (CylinderContextScanStep.initial source pre.length)).stk⟩ =
        ⟨none, vFinal,
         (Wide96ContextPreservingScan.frame
           (foreignBank (initialOutput ++ joined piece (pre ++ suffix))
             context 0 C.extra)
           (CylinderContextScanStep.initial source
             (pre ++ suffix).length)).stk⟩ := by
  induction suffix generalizing pre v with
  | nil =>
      dsimp only
      have hzero := check_zero callback callbackStart callbackInit
        (Wide96ContextPreservingScan.frame
          (foreignBank (initialOutput ++ joined piece pre) context 0 C.extra)
          (CylinderContextScanStep.initial
            (SourceListEncoding.encode (pre ++ [])) pre.length)).stk v
      have hs := frame_fuel_same
        (SourceListEncoding.encode (pre ++ []))
        (initialOutput ++ joined piece pre) context pre.length 0 C.extra
      simp only [List.replicate_zero] at hs
      rw [hs] at hzero
      refine ⟨1, by simp [remainingBudget], (v.1, none), ?_⟩
      simpa [run, joined] using hzero
  | cons word tail ih =>
      dsimp only
      let source := SourceListEncoding.encode (pre ++ word :: tail)
      let output := initialOutput ++ joined piece pre
      let foreign := foreignBank output context tail.length C.extra
      let SOut := C.state pre word tail
      have hc := C.callback_run pre word tail
      have hp := C.post pre word tail
      obtain ⟨t, ht, hr⟩ := cycle_from_getter callback callbackStart
        callbackInit (C.control pre word tail) pre word tail
        foreign SOut (C.time pre word tail) hc
      have hcheck := check_to_getter callback callbackStart callbackInit
        source output context pre.length tail.length C.extra v
      have hcycle :=
        (run_add callback callbackStart callbackInit
          (show run callback callbackStart callbackInit 1
            ⟨some (.inr (.inr .check)), v,
             (Wide96ContextPreservingScan.frame
               (foreignBank output context (tail.length + 1) C.extra)
               (CylinderContextScanStep.initial source pre.length)).stk⟩ =
            ⟨some (.inl (.inl (.inl .scan))),
             getterControl callbackInit
               (CylinderContextScanStep.copyControl ((), none)),
             (Wide96ContextPreservingScan.frame foreign
               (CylinderContextScanStep.initial source pre.length)).stk⟩
            from hcheck) t).trans hr
      have hnext :
          run callback callbackStart callbackInit (1 + t)
            ⟨some (.inr (.inr .check)), v,
             (Wide96ContextPreservingScan.frame
               (foreignBank output context (word :: tail).length C.extra)
               (CylinderContextScanStep.initial source pre.length)).stk⟩ =
            ⟨some (.inr (.inr .check)),
             callbackControl
               (CylinderContextScanStep.copyControl ((), none))
               (C.control pre word tail),
             (Wide96ContextPreservingScan.frame
               (foreignBank
                 (initialOutput ++ joined piece (pre ++ [word]))
                 context tail.length C.extra)
               (CylinderContextScanStep.initial source
                 (pre ++ [word]).length)).stk⟩ := by
        have hcycle' := hcycle
        change run callback callbackStart callbackInit (1 + t)
            ⟨some (.inr (.inr .check)), v,
             (Wide96ContextPreservingScan.frame
               (foreignBank output context (tail.length + 1) C.extra)
               (CylinderContextScanStep.initial source pre.length)).stk⟩ =
          ⟨some (.inr (.inr .check)),
           callbackControl
             (CylinderContextScanStep.copyControl ((), none))
             (C.control pre word tail),
           Function.update
             (BitMachineClearBank.cleared cleanBank SOut) 10
             (true :: (BitMachineClearBank.cleared cleanBank SOut) 10)⟩ at hcycle'
        rw [hp] at hcycle'
        simpa only [List.length_cons, List.length_append,
          List.length_singleton, Nat.add_zero, source, output] using hcycle'
      obtain ⟨u, huBound, vFinal, hu⟩ := ih (pre ++ [word])
        (callbackControl
          (CylinderContextScanStep.copyControl ((), none))
          (C.control pre word tail))
      refine ⟨1 + t + u, ?_, vFinal, ?_⟩
      · have hcycleBound : t ≤
            cycleBudget callback callbackStart callbackInit piece
              initialOutput context C pre word tail := by
          simpa [cycleBudget, getterBudget, SOut, source]
            using ht
        simp only [remainingBudget]
        omega
      have hsource : source =
          SourceListEncoding.encode (pre ++ [word] ++ tail) := by
        simp [source, List.append_assoc]
      rw [hsource] at hnext
      have htotal :=
        (run_add callback callbackStart callbackInit hnext u).trans hu
      simpa only [List.append_assoc, List.singleton_append,
        List.length_cons, source, output] using htotal

#print axioms run_remaining

end CurrentAdditive.Wide96ContextListScheduler
