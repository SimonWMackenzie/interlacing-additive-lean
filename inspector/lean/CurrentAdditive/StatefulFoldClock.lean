import CurrentAdditive.StatefulListSchedulerFixedBound
import CurrentAdditive.IndexedV2Clock

set_option maxHeartbeats 1000000

/-!
The physical clock is one final empty-count check plus one count check and
one complete getter/callback/cleanup/index cycle per source item.  This file
also packages the fixed-input bound when the concrete callback and its scratch
use have uniform bounds on cuts of that input.
-/

namespace CurrentAdditive.StatefulListScheduler

open EthInapproximability.CurrentPaper
open CurrentAdditive.GaussListContext
open Turing BitMachineEncoding

variable {N : Nat}
local notation "Stack" => StackN N

variable {L V : Type} [DecidableEq L] [Fintype L]
    [DecidableEq V] [Fintype V]

def cycleCosts
    (callback : L → TM2.Stmt (fun _ : Stack => Bool) L V)
    (callbackStart : L) (callbackInit : V)
    (step : List Bool → List Bool → List Bool)
    (initialOutput context : List Bool)
    (C : CallbackContract callback callbackStart callbackInit step
      initialOutput context)
    (pre suffix : List (List Bool)) : List Nat :=
  match suffix with
  | [] => []
  | word :: tail =>
      (1 + cycleBudget callback callbackStart callbackInit step
        initialOutput context C pre word tail) ::
      cycleCosts callback callbackStart callbackInit step
        initialOutput context C (pre ++ [word]) tail

theorem remainingBudget_eq_sum
    (callback : L → TM2.Stmt (fun _ : Stack => Bool) L V)
    (callbackStart : L) (callbackInit : V)
    (step : List Bool → List Bool → List Bool)
    (initialOutput context : List Bool)
    (C : CallbackContract callback callbackStart callbackInit step
      initialOutput context)
    (pre suffix : List (List Bool)) :
    remainingBudget callback callbackStart callbackInit step
      initialOutput context C pre suffix =
    1 + (cycleCosts callback callbackStart callbackInit step
      initialOutput context C pre suffix).sum := by
  induction suffix generalizing pre with
  | nil => simp [remainingBudget, cycleCosts]
  | cons word tail ih =>
      simp only [remainingBudget, cycleCosts, List.sum_cons]
      rw [ih (pre ++ [word])]
      omega

theorem getterBudget_cubic (pre : List (List Bool))
    (word : List Bool) (suffix : List (List Bool)) :
    let source := SourceListEncoding.encode (pre ++ word :: suffix)
    getterBudget pre word suffix ≤ 50 * (source.length + 1)^3 := by
  dsimp only
  let xs := pre ++ word :: suffix
  let source := SourceListEncoding.encode xs
  have hcost := IndexedV2Clock.fieldCost_prefix_le
    (pre ++ [word]) suffix
  have hshape : (pre ++ [word]) ++ suffix = xs := by
    simp [xs, List.append_assoc]
  rw [hshape] at hcost
  have hpre : pre.length ≤ source.length := by
    have hcount := IndexedV2Clock.fields_length_ge_count xs
    have hprelen : pre.length ≤ xs.length := by simp [xs]
    have hfields : (SourceListEncoding.fields xs).length ≤ source.length := by
      simp [source, SourceListEncoding.encode]
    omega
  have hbits : xs.length.bits.length ≤ source.length := by
    have hcount := IndexedV2Clock.fields_length_ge_count xs
    have hbit := IndexedV2Clock.bits_length_le xs.length
    have hfields : (SourceListEncoding.fields xs).length ≤ source.length := by
      simp [source, SourceListEncoding.encode]
    omega
  change getterBudget pre word suffix ≤ 50 * (source.length + 1)^3
  unfold getterBudget
  change 2 * pre.length + 5 +
    (2 * source.length + 5 + (4 * xs.length.bits.length + 6 +
      IndexedFieldProgram.fieldCost (pre ++ [word]))) + 1 ≤ _
  nlinarith [sq_nonneg ((source.length : ℤ))]

theorem run_fixed_input_polynomial_envelope
    (callback : L → TM2.Stmt (fun _ : Stack => Bool) L V)
    (callbackStart : L) (callbackInit : V)
    (step : List Bool → List Bool → List Bool)
    (initialOutput context : List Bool)
    (C : CallbackContract callback callbackStart callbackInit step
      initialOutput context)
    (original : List (List Bool))
    (G Q R dG dQ dR : Nat)
    (size : Nat)
    (hGet : ∀ a word b, a ++ word :: b = original →
      getterBudget a word b ≤ G * (size + 1) ^ dG)
    (hCallback : ∀ a word b, a ++ word :: b = original →
      C.time a word b ≤ Q * (size + 1) ^ dQ)
    (hScratch : ∀ a word b, a ++ word :: b = original →
      (∑ i : Fin 10, ((C.state a word b) (cleanBank i)).length) ≤
        R * (size + 1) ^ dR)
    (v : Control V) :
    let source := SourceListEncoding.encode original
    ∃ t ≤ (original.length + 1) *
        (G * (size + 1) ^ dG + Q * (size + 1) ^ dQ +
          R * (size + 1) ^ dR + 15),
      ∃ vFinal : Control V,
      run callback callbackStart callbackInit t
        ⟨some (.inr (.inr .check)), v,
         (StatefulPreservingScan.frame
           (foreignBank initialOutput context original.length C.extra)
           (CylinderContextScanStep.initial source 0)).stk⟩ =
        ⟨none, vFinal,
         (StatefulPreservingScan.frame
           (foreignBank (original.foldl step initialOutput)
             context 0 C.extra)
           (CylinderContextScanStep.initial source original.length)).stk⟩ := by
  dsimp only
  have hP : ∀ a word b, a ++ word :: b = original →
      cycleBudget callback callbackStart callbackInit step
        initialOutput context C a word b ≤
        G * (size + 1) ^ dG + Q * (size + 1) ^ dQ +
          R * (size + 1) ^ dR + 14 := by
    intro a word b hsplit
    have hg := hGet a word b hsplit
    have hq := hCallback a word b hsplit
    have hr := hScratch a word b hsplit
    unfold cycleBudget
    omega
  obtain ⟨t, ht, vf, he⟩ := run_remaining_fixed_input
    callback callbackStart callbackInit step initialOutput context C
    original (G * (size + 1) ^ dG + Q * (size + 1) ^ dQ +
      R * (size + 1) ^ dR + 14) hP [] original (by simp) v
  refine ⟨t, ?_, vf, ?_⟩
  · simpa [Nat.add_assoc] using ht
  · simpa [folded] using he

theorem run_with_callback_polynomial_cap
    (callback : L → TM2.Stmt (fun _ : Stack => Bool) L V)
    (callbackStart : L) (callbackInit : V)
    (step : List Bool → List Bool → List Bool)
    (initialOutput context : List Bool)
    (C : CallbackContract callback callbackStart callbackInit step
      initialOutput context)
    (original : List (List Bool))
    (Q R dQ dR : Nat)
    (hCallback : ∀ a word b, a ++ word :: b = original →
      C.time a word b ≤ Q *
        ((SourceListEncoding.encode original).length + 1) ^ dQ)
    (hScratch : ∀ a word b, a ++ word :: b = original →
      (∑ i : Fin 10, ((C.state a word b) (cleanBank i)).length) ≤
        R * ((SourceListEncoding.encode original).length + 1) ^ dR)
    (v : Control V) :
    let source := SourceListEncoding.encode original
    ∃ t ≤ (original.length + 1) *
        (50 * (source.length + 1)^3 +
          Q * (source.length + 1)^dQ +
          R * (source.length + 1)^dR + 15),
      ∃ vFinal : Control V,
      run callback callbackStart callbackInit t
        ⟨some (.inr (.inr .check)), v,
         (StatefulPreservingScan.frame
           (foreignBank initialOutput context original.length C.extra)
           (CylinderContextScanStep.initial source 0)).stk⟩ =
        ⟨none, vFinal,
         (StatefulPreservingScan.frame
           (foreignBank (original.foldl step initialOutput)
             context 0 C.extra)
           (CylinderContextScanStep.initial source original.length)).stk⟩ := by
  have hGet : ∀ a word b, a ++ word :: b = original →
      getterBudget a word b ≤
        50 * ((SourceListEncoding.encode original).length + 1)^3 := by
    intro a word b hsplit
    simpa only [hsplit] using getterBudget_cubic a word b
  exact run_fixed_input_polynomial_envelope
    callback callbackStart callbackInit step initialOutput context C
    original 50 Q R 3 dQ dR
    (SourceListEncoding.encode original).length hGet hCallback hScratch v

#print axioms remainingBudget_eq_sum
#print axioms getterBudget_cubic
#print axioms run_fixed_input_polynomial_envelope
#print axioms run_with_callback_polynomial_cap

end CurrentAdditive.StatefulListScheduler
