import CurrentAdditive.GaussPivotCallbackPost
import CurrentAdditive.LargeContextListSchedulerRun

set_option maxHeartbeats 1000000

namespace CurrentAdditive.GaussPivotTypedScan

open EthInapproximability.CurrentPaper
open CurrentAdditive.LargeContextPreservingScan
open CurrentAdditive.LargeContextListScheduler
open CurrentAdditive.GaussListContext
open Turing BitMachineEncoding

abbrev Stack := Fin 32

variable {L V : Type} [DecidableEq L] [Fintype L]
    [DecidableEq V] [Fintype V]

def reversed (piece : List Bool → Bool) (xs : List (List Bool)) :
    List Bool := (xs.map piece).reverse

theorem reversed_snoc (piece : List Bool → Bool)
    (pre : List (List Bool)) (word : List Bool) :
    reversed piece (pre ++ [word]) = piece word :: reversed piece pre := by
  simp [reversed]

structure Contract
    (callback : L → TM2.Stmt (fun _ : Stack => Bool) L V)
    (callbackStart : L) (callbackInit : V)
    (rows : List (List Bool)) (piece : List Bool → Bool)
    (initialOutput context : List Bool) where
  extra : Stack → List Bool
  time : (pre : List (List Bool)) → (word : List Bool) →
    (suffix : List (List Bool)) → Nat
  control : (pre : List (List Bool)) → (word : List Bool) →
    (suffix : List (List Bool)) → V
  state : (pre : List (List Bool)) → (word : List Bool) →
    (suffix : List (List Bool)) → Stack → List Bool
  callback_run : ∀ pre word suffix,
    pre ++ word :: suffix = rows →
    let source := SourceListEncoding.encode rows
    let output := reversed piece pre ++ initialOutput
    let selected := LargeContextPreservingScan.frame
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
    pre ++ word :: suffix = rows →
    let SOut := state pre word suffix
    Function.update
      (BitMachineClearBank.cleared cleanBank SOut) 10
      (true :: (BitMachineClearBank.cleared cleanBank SOut) 10) =
    (LargeContextPreservingScan.frame
      (foreignBank (reversed piece (pre ++ [word]) ++ initialOutput)
        context suffix.length extra)
      (CylinderContextScanStep.initial
        (SourceListEncoding.encode rows) (pre.length + 1))).stk

def cycleBudget
    (callback : L → TM2.Stmt (fun _ : Stack => Bool) L V)
    (callbackStart : L) (callbackInit : V)
    (rows : List (List Bool)) (piece : List Bool → Bool)
    (initialOutput context : List Bool)
    (C : Contract callback callbackStart callbackInit rows piece
      initialOutput context)
    (pre : List (List Bool)) (word : List Bool)
    (suffix : List (List Bool)) : Nat :=
  getterBudget pre word suffix + (C.time pre word suffix + 1) + 1 +
    ((∑ i : Fin 10,
      ((C.state pre word suffix) (cleanBank i)).length) + 11) + 1

def remainingBudget
    (callback : L → TM2.Stmt (fun _ : Stack => Bool) L V)
    (callbackStart : L) (callbackInit : V)
    (rows : List (List Bool)) (piece : List Bool → Bool)
    (initialOutput context : List Bool)
    (C : Contract callback callbackStart callbackInit rows piece
      initialOutput context)
    (pre suffix : List (List Bool)) : Nat :=
  match suffix with
  | [] => 1
  | word :: tail =>
      1 + cycleBudget callback callbackStart callbackInit rows piece
        initialOutput context C pre word tail +
      remainingBudget callback callbackStart callbackInit rows piece
        initialOutput context C (pre ++ [word]) tail

theorem run_remaining
    (callback : L → TM2.Stmt (fun _ : Stack => Bool) L V)
    (callbackStart : L) (callbackInit : V)
    (rows : List (List Bool)) (piece : List Bool → Bool)
    (initialOutput context : List Bool)
    (C : Contract callback callbackStart callbackInit rows piece
      initialOutput context)
    (pre suffix : List (List Bool)) (v : Control V)
    (hrows : pre ++ suffix = rows) :
    ∃ t ≤ remainingBudget callback callbackStart callbackInit rows piece
        initialOutput context C pre suffix,
      ∃ vFinal : Control V,
      LargeContextListScheduler.run callback callbackStart callbackInit t
        ⟨some (.inr (.inr .check)), v,
         (LargeContextPreservingScan.frame
           (foreignBank (reversed piece pre ++ initialOutput)
             context suffix.length C.extra)
           (CylinderContextScanStep.initial
             (SourceListEncoding.encode rows) pre.length)).stk⟩ =
        ⟨none, vFinal,
         (LargeContextPreservingScan.frame
           (foreignBank (reversed piece rows ++ initialOutput)
             context 0 C.extra)
           (CylinderContextScanStep.initial
             (SourceListEncoding.encode rows) rows.length)).stk⟩ := by
  induction suffix generalizing pre v with
  | nil =>
      have hpre : pre = rows := by simpa using hrows
      subst rows
      have hzero := check_zero callback callbackStart callbackInit
        (LargeContextPreservingScan.frame
          (foreignBank (reversed piece pre ++ initialOutput) context 0 C.extra)
          (CylinderContextScanStep.initial
            (SourceListEncoding.encode pre) pre.length)).stk v
      have hs := frame_fuel_same
        (SourceListEncoding.encode pre)
        (reversed piece pre ++ initialOutput) context pre.length 0 C.extra
      simp only [List.replicate_zero] at hs
      rw [hs] at hzero
      refine ⟨1, by simp [remainingBudget], (v.1, none), ?_⟩
      simpa [LargeContextListScheduler.run] using hzero
  | cons word tail ih =>
      let source := SourceListEncoding.encode (pre ++ word :: tail)
      let output := reversed piece pre ++ initialOutput
      let foreign := foreignBank output context tail.length C.extra
      let SOut := C.state pre word tail
      have hsplit : pre ++ word :: tail = rows := hrows
      have hc := C.callback_run pre word tail hsplit
      have hp := C.post pre word tail hsplit
      have hsrc : SourceListEncoding.encode rows = source := by
        simp [source, ← hsplit]
      simp only [hsrc] at hc hp
      obtain ⟨t, ht, hr⟩ := cycle_from_getter callback callbackStart
        callbackInit (C.control pre word tail) pre word tail
        foreign SOut (C.time pre word tail) (by
          simpa only [source] using hc)
      have hcheck := check_to_getter callback callbackStart callbackInit
        source output context pre.length tail.length C.extra v
      have hcycle :=
        (run_add callback callbackStart callbackInit
          (show run callback callbackStart callbackInit 1
            ⟨some (.inr (.inr .check)), v,
             (LargeContextPreservingScan.frame
               (foreignBank output context (tail.length + 1) C.extra)
               (CylinderContextScanStep.initial source pre.length)).stk⟩ =
            ⟨some (.inl (.inl (.inl .scan))),
             getterControl callbackInit
               (CylinderContextScanStep.copyControl ((), none)),
             (LargeContextPreservingScan.frame foreign
               (CylinderContextScanStep.initial source pre.length)).stk⟩
            from hcheck) t).trans hr
      have hnext :
          run callback callbackStart callbackInit (1 + t)
            ⟨some (.inr (.inr .check)), v,
             (LargeContextPreservingScan.frame
               (foreignBank output context (word :: tail).length C.extra)
               (CylinderContextScanStep.initial source pre.length)).stk⟩ =
            ⟨some (.inr (.inr .check)),
             callbackControl
               (CylinderContextScanStep.copyControl ((), none))
               (C.control pre word tail),
             (LargeContextPreservingScan.frame
               (foreignBank
                 (reversed piece (pre ++ [word]) ++ initialOutput)
                 context tail.length C.extra)
               (CylinderContextScanStep.initial source
                 (pre ++ [word]).length)).stk⟩ := by
        have hcycle' := hcycle
        change run callback callbackStart callbackInit (1 + t)
            ⟨some (.inr (.inr .check)), v,
             (LargeContextPreservingScan.frame
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
      have hrows' : (pre ++ [word]) ++ tail = rows := by
        simpa only [List.append_assoc, List.singleton_append] using hsplit
      obtain ⟨u, huBound, vFinal, hu⟩ := ih (pre ++ [word])
        (callbackControl
          (CylinderContextScanStep.copyControl ((), none))
          (C.control pre word tail)) hrows'
      refine ⟨1 + t + u, ?_, vFinal, ?_⟩
      · have hcycleBound : t ≤
            cycleBudget callback callbackStart callbackInit rows piece
              initialOutput context C pre word tail := by
          simpa [cycleBudget, getterBudget, SOut, source]
            using ht
        simp only [remainingBudget]
        omega
      rw [hsrc.symm] at hnext
      have htotal :=
        (run_add callback callbackStart callbackInit hnext u).trans hu
      simpa only [List.append_assoc, List.singleton_append,
        List.length_cons, source, output] using htotal

#print axioms run_remaining

end CurrentAdditive.GaussPivotTypedScan
