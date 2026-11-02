import CurrentAdditive.StatefulListSchedulerFixedBound

set_option maxHeartbeats 1000000

/-!
The frozen Fin (32+N) scheduler invokes its callback only on splits of its one
fixed source list. This adapter records that reachable-source invariant in the
physical callback contract. No callback run for an unrelated list is assumed.
-/

noncomputable section

namespace CurrentAdditive.FeatureMapSourceScheduler

open EthInapproximability.CurrentPaper
open CurrentAdditive.StatefulPreservingScan
open CurrentAdditive.GaussListContext
open CurrentAdditive.StatefulListScheduler
open Turing BitMachineEncoding

variable {N : Nat}
local notation "Stack" => StatefulListScheduler.StackN N

def joined (piece : List Bool → List Bool) (xs : List (List Bool)) : List Bool :=
  xs.flatMap piece

theorem joined_append_one (piece : List Bool → List Bool)
    (xs : List (List Bool)) (word : List Bool) :
    joined piece (xs ++ [word]) = joined piece xs ++ piece word := by
  simp [joined]

variable {L V : Type} [DecidableEq L] [Fintype L]
    [DecidableEq V] [Fintype V]

/-- A physical callback contract only for actual splits of `original`.
The callback run and its full-bank postcondition are both required at every
reachable split; no behavior on unrelated words is prescribed. -/
structure SourceCallbackContract
    (callback : L → TM2.Stmt (fun _ : Stack => Bool) L V)
    (callbackStart : L) (callbackInit : V)
    (piece : List Bool → List Bool)
    (initialOutput context : List Bool)
    (original : List (List Bool)) where
  extra : Stack → List Bool
  time : (pre : List (List Bool)) → (word : List Bool) →
    (suffix : List (List Bool)) → Nat
  control : (pre : List (List Bool)) → (word : List Bool) →
    (suffix : List (List Bool)) → V
  state : (pre : List (List Bool)) → (word : List Bool) →
    (suffix : List (List Bool)) → Stack → List Bool
  callback_run : ∀ pre word suffix,
    pre ++ word :: suffix = original →
    let source := SourceListEncoding.encode original
    let output := initialOutput ++ joined piece pre
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
  post : ∀ pre word suffix,
    pre ++ word :: suffix = original →
    let source := SourceListEncoding.encode original
    let SOut := state pre word suffix
    Function.update
      (BitMachineClearBank.cleared cleanBank SOut) 10
      (true :: (BitMachineClearBank.cleared cleanBank SOut) 10) =
    (StatefulPreservingScan.frame
      (foreignBank (initialOutput ++ joined piece (pre ++ [word]))
        context suffix.length extra)
      (CylinderContextScanStep.initial source (pre.length + 1))).stk

def cycleBudget
    (callback : L → TM2.Stmt (fun _ : Stack => Bool) L V)
    (callbackStart : L) (callbackInit : V)
    (piece : List Bool → List Bool)
    (initialOutput context : List Bool)
    (original : List (List Bool))
    (C : SourceCallbackContract callback callbackStart callbackInit piece
      initialOutput context original)
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
    (original : List (List Bool))
    (C : SourceCallbackContract callback callbackStart callbackInit piece
      initialOutput context original)
    (pre suffix : List (List Bool)) : Nat :=
  match suffix with
  | [] => 1
  | word :: tail =>
      1 + cycleBudget callback callbackStart callbackInit piece
        initialOutput context original C pre word tail +
      remainingBudget callback callbackStart callbackInit piece
        initialOutput context original C (pre ++ [word]) tail

theorem run_remaining
    (callback : L → TM2.Stmt (fun _ : Stack => Bool) L V)
    (callbackStart : L) (callbackInit : V)
    (piece : List Bool → List Bool)
    (initialOutput context : List Bool)
    (original : List (List Bool))
    (C : SourceCallbackContract callback callbackStart callbackInit piece
      initialOutput context original)
    (pre suffix : List (List Bool))
    (hSplit : pre ++ suffix = original) (v : Control V) :
    let source := SourceListEncoding.encode (pre ++ suffix)
    let output := initialOutput ++ joined piece pre
    ∃ t ≤ remainingBudget callback callbackStart callbackInit piece
        initialOutput context original C pre suffix,
      ∃ vFinal : Control V,
      StatefulListScheduler.run callback callbackStart callbackInit t
        ⟨some (.inr (.inr .check)), v,
         (StatefulPreservingScan.frame
           (foreignBank output context suffix.length C.extra)
           (CylinderContextScanStep.initial source pre.length)).stk⟩ =
        ⟨none, vFinal,
         (StatefulPreservingScan.frame
           (foreignBank (initialOutput ++ joined piece (pre ++ suffix))
             context 0 C.extra)
           (CylinderContextScanStep.initial source
             (pre ++ suffix).length)).stk⟩ := by
  induction suffix generalizing pre v with
  | nil =>
      dsimp only
      have hzero := check_zero callback callbackStart callbackInit
        (StatefulPreservingScan.frame
          (foreignBank (initialOutput ++ joined piece pre) context 0 C.extra)
          (CylinderContextScanStep.initial
            (SourceListEncoding.encode (pre ++ [])) pre.length)).stk v
      have hs := frame_fuel_same
        (SourceListEncoding.encode (pre ++ []))
        (initialOutput ++ joined piece pre) context pre.length 0 C.extra
      simp only [List.replicate_zero] at hs
      rw [hs] at hzero
      refine ⟨1, by simp [remainingBudget], (v.1, none), ?_⟩
      simpa [StatefulListScheduler.run, joined] using hzero
  | cons word tail ih =>
      dsimp only
      let source := SourceListEncoding.encode (pre ++ word :: tail)
      let output := initialOutput ++ joined piece pre
      let foreign := foreignBank output context tail.length C.extra
      let SOut := C.state pre word tail
      have hc := C.callback_run pre word tail hSplit
      have hp := C.post pre word tail hSplit
      simp only [← hSplit] at hc hp
      obtain ⟨t, ht, hr⟩ := cycle_from_getter callback callbackStart
        callbackInit (C.control pre word tail) pre word tail
        foreign SOut (C.time pre word tail) hc
      have hcheck := check_to_getter callback callbackStart callbackInit
        source output context pre.length tail.length C.extra v
      have hcycle :=
        (StatefulListScheduler.run_add callback callbackStart callbackInit
          (show StatefulListScheduler.run callback callbackStart callbackInit 1
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
          StatefulListScheduler.run callback callbackStart callbackInit (1 + t)
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
                 (initialOutput ++ joined piece (pre ++ [word]))
                 context tail.length C.extra)
               (CylinderContextScanStep.initial source
                 (pre ++ [word]).length)).stk⟩ := by
        have hcycle' := hcycle
        change StatefulListScheduler.run callback callbackStart callbackInit (1 + t)
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
      have hs : (pre ++ [word]) ++ tail = original := by
        simpa only [List.append_assoc, List.singleton_append] using hSplit
      obtain ⟨u, huBound, vFinal, hu⟩ := ih (pre ++ [word]) hs
        (callbackControl
          (CylinderContextScanStep.copyControl ((), none))
          (C.control pre word tail))
      refine ⟨1 + t + u, ?_, vFinal, ?_⟩
      · have hcycleBound : t ≤
            cycleBudget callback callbackStart callbackInit piece
              initialOutput context original C pre word tail := by
          simpa [cycleBudget, getterBudget, SOut, source]
            using ht
        simp only [remainingBudget]
        omega
      have hsource : source =
          SourceListEncoding.encode (pre ++ [word] ++ tail) := by
        simp [source, List.append_assoc]
      rw [hsource] at hnext
      have htotal :=
        (StatefulListScheduler.run_add callback callbackStart callbackInit hnext u).trans hu
      simpa only [List.append_assoc, List.singleton_append,
        List.length_cons, source, output] using htotal

#print axioms run_remaining

omit [DecidableEq L] [Fintype L] [DecidableEq V] [Fintype V] in
/-- The budget sums only cycles belonging to the fixed source list. -/
theorem remainingBudget_fixed_input
    (callback : L → TM2.Stmt (fun _ : Stack => Bool) L V)
    (callbackStart : L) (callbackInit : V)
    (piece : List Bool → List Bool)
    (initialOutput context : List Bool)
    (original : List (List Bool))
    (C : SourceCallbackContract callback callbackStart callbackInit piece
      initialOutput context original)
    (P : Nat)
    (hP : ∀ a word b, a ++ word :: b = original →
      cycleBudget callback callbackStart callbackInit piece
        initialOutput context original C a word b ≤ P)
    (pre suffix : List (List Bool))
    (hSplit : pre ++ suffix = original) :
    remainingBudget callback callbackStart callbackInit piece
      initialOutput context original C pre suffix ≤
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

/-- The very same Fin (32+N) instruction table runs from any reachable suffix of
the fixed source. The bound counts the remaining items and one uniform cycle
cap for valid splits only. -/
theorem run_remaining_fixed_input
    (callback : L → TM2.Stmt (fun _ : Stack => Bool) L V)
    (callbackStart : L) (callbackInit : V)
    (piece : List Bool → List Bool)
    (initialOutput context : List Bool)
    (original : List (List Bool))
    (C : SourceCallbackContract callback callbackStart callbackInit piece
      initialOutput context original)
    (P : Nat)
    (hP : ∀ a word b, a ++ word :: b = original →
      cycleBudget callback callbackStart callbackInit piece
        initialOutput context original C a word b ≤ P)
    (pre suffix : List (List Bool))
    (hSplit : pre ++ suffix = original) (v : Control V) :
    let source := SourceListEncoding.encode original
    let output := initialOutput ++ joined piece pre
    ∃ t ≤ (suffix.length + 1) * (P + 1),
      ∃ vFinal : Control V,
      StatefulListScheduler.run callback callbackStart callbackInit t
        ⟨some (.inr (.inr .check)), v,
         (StatefulPreservingScan.frame
           (foreignBank output context suffix.length C.extra)
           (CylinderContextScanStep.initial source pre.length)).stk⟩ =
        ⟨none, vFinal,
         (StatefulPreservingScan.frame
           (foreignBank (initialOutput ++ joined piece original)
             context 0 C.extra)
           (CylinderContextScanStep.initial source
             original.length)).stk⟩ := by
  have hr := run_remaining callback callbackStart callbackInit piece
    initialOutput context original C pre suffix hSplit v
  have hb := remainingBudget_fixed_input callback callbackStart
    callbackInit piece initialOutput context original C P hP pre suffix hSplit
  rcases hr with ⟨t, ht, vFinal, he⟩
  refine ⟨t, ht.trans hb, vFinal, ?_⟩
  simpa only [hSplit] using he

theorem run_full_fixed_input
    (callback : L → TM2.Stmt (fun _ : Stack => Bool) L V)
    (callbackStart : L) (callbackInit : V)
    (piece : List Bool → List Bool)
    (initialOutput context : List Bool)
    (original : List (List Bool))
    (C : SourceCallbackContract callback callbackStart callbackInit piece
      initialOutput context original)
    (P : Nat)
    (hP : ∀ a word b, a ++ word :: b = original →
      cycleBudget callback callbackStart callbackInit piece
        initialOutput context original C a word b ≤ P)
    (v : Control V) :
    let source := SourceListEncoding.encode original
    ∃ t ≤ (original.length + 1) * (P + 1),
      ∃ vFinal : Control V,
      StatefulListScheduler.run callback callbackStart callbackInit t
        ⟨some (.inr (.inr .check)), v,
         (StatefulPreservingScan.frame
           (foreignBank initialOutput context original.length C.extra)
           (CylinderContextScanStep.initial source 0)).stk⟩ =
        ⟨none, vFinal,
         (StatefulPreservingScan.frame
           (foreignBank (initialOutput ++ joined piece original)
             context 0 C.extra)
           (CylinderContextScanStep.initial source
             original.length)).stk⟩ := by
  have h := run_remaining_fixed_input callback callbackStart
    callbackInit piece initialOutput context original C P hP [] original
    (by simp) v
  have hn : joined piece [] = [] := rfl
  simpa only [List.nil_append, List.length_nil, Nat.zero_add, hn,
    List.append_nil] using h

#print axioms remainingBudget_fixed_input
#print axioms run_remaining_fixed_input
#print axioms run_full_fixed_input

end CurrentAdditive.FeatureMapSourceScheduler
