import CurrentAdditive.StatefulListScheduler

set_option maxHeartbeats 1200000
set_option maxRecDepth 10000

/-!
Source-specific indexed execution of the same fixed contextual scheduler.
The output may depend on the processed prefix, allowing equal source records
to use different coefficient positions. Conditional on a concrete
callback that physically updates the accumulator and preserves its context.
The scheduler's getter, cleanup, index increment, and item-count loop are
discharged here; the callback's own machine run remains an explicit premise.
-/

namespace CurrentAdditive.RatioIndexedScheduler

open EthInapproximability.CurrentPaper
open CurrentAdditive.StatefulPreservingScan
open CurrentAdditive.GaussListContext
open Turing BitMachineEncoding
open CurrentAdditive.StatefulListScheduler

variable {N : Nat}
local notation "Stack" => StatefulListScheduler.StackN N

variable {L V : Type} [DecidableEq L] [Fintype L]
    [DecidableEq V] [Fintype V]

/-- A concrete callback contract for every canonical list split. The local
callback starts on the selected item and the current bank-9 accumulator.
`post` is the full resulting stack equality after physical scratch cleanup
and index increment. It requires the next fold accumulator on bank 9 and
restores callback scratch banks at each item boundary. -/
structure CallbackContract
    (callback : L → TM2.Stmt (fun _ : Stack => Bool) L V)
    (callbackStart : L) (callbackInit : V)
    (xs : List (List Bool)) (outputAt : List (List Bool) → List Bool)
    (context : List Bool) where
  /-- Initial callback-owned registers, restored after each item. -/
  extra : Stack → List Bool
  time : (pre : List (List Bool)) → (word : List Bool) →
    (suffix : List (List Bool)) → Nat
  control : (pre : List (List Bool)) → (word : List Bool) →
    (suffix : List (List Bool)) → V
  state : (pre : List (List Bool)) → (word : List Bool) →
    (suffix : List (List Bool)) → Stack → List Bool
  callback_run : ∀ pre word suffix, pre ++ word :: suffix = xs →
    let source := SourceListEncoding.encode (pre ++ word :: suffix)
    let output := outputAt pre
    let selected := StatefulPreservingScan.frame
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
  post : ∀ pre word suffix, pre ++ word :: suffix = xs →
    let source := SourceListEncoding.encode (pre ++ word :: suffix)
    let SOut := state pre word suffix
    Function.update
      (BitMachineClearBank.cleared cleanBank SOut) 10
      (true :: (BitMachineClearBank.cleared cleanBank SOut) 10) =
    (StatefulPreservingScan.frame
      (foreignBank (outputAt (pre ++ [word]))
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
    (xs : List (List Bool)) (outputAt : List (List Bool) → List Bool)
    (context : List Bool)
    (C : CallbackContract callback callbackStart callbackInit xs outputAt context)
    (pre : List (List Bool)) (word : List Bool)
    (suffix : List (List Bool)) : Nat :=
  getterBudget pre word suffix + (C.time pre word suffix + 1) + 1 +
    ((∑ i : Fin 10,
      ((C.state pre word suffix) (cleanBank i)).length) + 11) + 1

def remainingBudget
    (callback : L → TM2.Stmt (fun _ : Stack => Bool) L V)
    (callbackStart : L) (callbackInit : V)
    (xs : List (List Bool)) (outputAt : List (List Bool) → List Bool)
    (context : List Bool)
    (C : CallbackContract callback callbackStart callbackInit xs outputAt context)
    (pre suffix : List (List Bool)) : Nat :=
  match suffix with
  | [] => 1
  | word :: tail =>
      1 + cycleBudget callback callbackStart callbackInit xs outputAt context C pre word tail +
      remainingBudget callback callbackStart callbackInit xs outputAt context C (pre ++ [word]) tail

theorem run_remaining
    (callback : L → TM2.Stmt (fun _ : Stack => Bool) L V)
    (callbackStart : L) (callbackInit : V)
    (xs : List (List Bool)) (outputAt : List (List Bool) → List Bool)
    (context : List Bool)
    (C : CallbackContract callback callbackStart callbackInit xs outputAt context)
    (pre suffix : List (List Bool)) (v : Control V)
    (hfull : pre ++ suffix = xs) :
    let source := SourceListEncoding.encode (pre ++ suffix)
    let output := outputAt pre
    ∃ t ≤ remainingBudget callback callbackStart callbackInit xs outputAt context C pre suffix,
      ∃ vFinal : Control V,
      run callback callbackStart callbackInit t
        ⟨some (.inr (.inr .check)), v,
         (StatefulPreservingScan.frame
           (foreignBank output context suffix.length C.extra)
           (CylinderContextScanStep.initial source pre.length)).stk⟩ =
        ⟨none, vFinal,
         (StatefulPreservingScan.frame
           (foreignBank (outputAt (pre ++ suffix))
             context 0 C.extra)
           (CylinderContextScanStep.initial source
             (pre ++ suffix).length)).stk⟩ := by
  induction suffix generalizing pre v with
  | nil =>
      dsimp only
      have hzero := check_zero callback callbackStart callbackInit
        (StatefulPreservingScan.frame
          (foreignBank (outputAt pre) context 0 C.extra)
          (CylinderContextScanStep.initial
            (SourceListEncoding.encode (pre ++ [])) pre.length)).stk v
      have hs := frame_fuel_same
        (SourceListEncoding.encode (pre ++ []))
        (outputAt pre) context pre.length 0 C.extra
      simp only [List.replicate_zero] at hs
      rw [hs] at hzero
      refine ⟨1, by simp [remainingBudget], (v.1, none), ?_⟩
      simpa [StatefulListScheduler.run] using hzero
  | cons word tail ih =>
      dsimp only
      let source := SourceListEncoding.encode (pre ++ word :: tail)
      let output := outputAt pre
      let foreign := foreignBank output context tail.length C.extra
      let SOut := C.state pre word tail
      have hc := C.callback_run pre word tail hfull
      have hp := C.post pre word tail hfull
      obtain ⟨t, ht, hr⟩ := cycle_from_getter callback callbackStart
        callbackInit (C.control pre word tail) pre word tail
        foreign SOut (C.time pre word tail) hc
      have hcheck := check_to_getter callback callbackStart callbackInit
        source output context pre.length tail.length C.extra v
      have hcycle :=
        (run_add callback callbackStart callbackInit
          (show run callback callbackStart callbackInit 1
            ⟨some (.inr (.inr .check)), v,
             (StatefulPreservingScan.frame
               (foreignBank output context (tail.length + 1) C.extra)
               (CylinderContextScanStep.initial source pre.length)).stk⟩ =
            ⟨some (.inl (.inl (.inl .scan))),
             getterControl callbackInit
               (CylinderContextScanStep.copyControl ((), none)),
             (StatefulPreservingScan.frame foreign
               (CylinderContextScanStep.initial source pre.length)).stk⟩
            from hcheck) t).trans hr
      have hnext :
          run callback callbackStart callbackInit (1 + t)
            ⟨some (.inr (.inr .check)), v,
             (StatefulPreservingScan.frame
               (foreignBank output context (word :: tail).length C.extra)
               (CylinderContextScanStep.initial source pre.length)).stk⟩ =
            ⟨some (.inr (.inr .check)),
             callbackControl
               (CylinderContextScanStep.copyControl ((), none))
               (C.control pre word tail),
             (StatefulPreservingScan.frame
               (foreignBank
                 (outputAt (pre ++ [word]))
                 context tail.length C.extra)
               (CylinderContextScanStep.initial source
                 (pre ++ [word]).length)).stk⟩ := by
        have hcycle' := hcycle
        change run callback callbackStart callbackInit (1 + t)
            ⟨some (.inr (.inr .check)), v,
             (StatefulPreservingScan.frame
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
        (by simpa only [List.append_assoc,List.singleton_append] using hfull)
      refine ⟨1 + t + u, ?_, vFinal, ?_⟩
      · have hcycleBound : t ≤
            cycleBudget callback callbackStart callbackInit xs outputAt context C pre word tail := by
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

end CurrentAdditive.RatioIndexedScheduler
