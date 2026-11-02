import CurrentAdditive.GaussPivotSearchRun
import CurrentAdditive.IndexedV2Clock
import EthInapproximability.CurrentPaper.BitMachineStackGrowth
import EthInapproximability.CurrentPaper.SourceListMachineSemantics

set_option maxHeartbeats 1000000

namespace CurrentAdditive.GaussSearchClock

open EthInapproximability.CurrentPaper
open CurrentAdditive.GaussListContext
open CurrentAdditive.GaussRowZeroCallback
open CurrentAdditive.GaussPivotTypedScan
open CurrentAdditive.GaussPivotTypedContract

theorem rows_le_code (rows : List (List Bool)) :
    rows.length ≤ (SourceListEncoding.encode rows).length := by
  have h := SourceListMachineSemantics.count_le_fields_length rows
  simp [SourceListEncoding.encode]
  omega

theorem getter_bound (pre : List (List Bool)) (word : List Bool)
    (suffix : List (List Bool)) :
    LargeContextListScheduler.getterBudget pre word suffix ≤
      50 * ((SourceListEncoding.encode (pre ++ word :: suffix)).length + 1)^3 := by
  let xs := pre ++ word :: suffix
  let source := SourceListEncoding.encode xs
  have hsource : source.length = (SourceListEncoding.encode xs).length := rfl
  have hcost := IndexedV2Clock.fieldCost_prefix_le (pre ++ [word]) suffix
  have hshape : (pre ++ [word]) ++ suffix = xs := by
    simp [xs, List.append_assoc]
  rw [hshape] at hcost
  have hpre : pre.length ≤ source.length := by
    have hc := rows_le_code xs
    have hp : pre.length ≤ xs.length := by simp [xs]
    omega
  have hbits : xs.length.bits.length ≤ source.length := by
    have hc := rows_le_code xs
    have hb := IndexedV2Clock.bits_length_le xs.length
    have hsrc : source.length = (SourceListEncoding.encode xs).length := rfl
    omega
  change LargeContextListScheduler.getterBudget pre word suffix ≤
    50 * (source.length + 1)^3
  unfold LargeContextListScheduler.getterBudget
  change 2 * pre.length + 5 +
    (2 * source.length + 5 + (4 * xs.length.bits.length + 6 +
      IndexedFieldProgram.fieldCost (pre ++ [word]))) + 1 ≤ _
  nlinarith [sq_nonneg ((source.length : ℤ))]

theorem cellCost_bound (pre : List (List Bool)) (cell : List Bool)
    (suffix : List (List Bool)) :
    GaussRowZeroCallback.cellCost pre cell suffix ≤
      50 * ((SourceListEncoding.encode (pre ++ cell :: suffix)).length + 1)^3 := by
  let xs := pre ++ cell :: suffix
  let source := SourceListEncoding.encode xs
  have hcost := IndexedV2Clock.fieldCost_prefix_le (pre ++ [cell]) suffix
  have hshape : (pre ++ [cell]) ++ suffix = xs := by
    simp [xs, List.append_assoc]
  rw [hshape] at hcost
  have hbits : xs.length.bits.length ≤ source.length := by
    have hc := rows_le_code xs
    have hb := IndexedV2Clock.bits_length_le xs.length
    have hsrc : source.length = (SourceListEncoding.encode xs).length := rfl
    omega
  change GaussRowZeroCallback.cellCost pre cell suffix ≤
    50 * (source.length + 1)^3
  unfold GaussRowZeroCallback.cellCost
  change 2 * source.length + 5 +
    (4 * xs.length.bits.length + 6 +
      IndexedFieldProgram.fieldCost (pre ++ [cell])) ≤ _
  nlinarith [sq_nonneg ((source.length : ℤ))]

variable {L V : Type} [DecidableEq L] [Fintype L]
  [DecidableEq V] [Fintype V]

theorem remainingBudget_le_of_cycle
    (callback : L → Turing.TM2.Stmt (fun _ : Fin 32 => Bool) L V)
    (callbackStart : L) (callbackInit : V)
    (rows : List (List Bool)) (piece : List Bool → Bool)
    (initialOutput context : List Bool)
    (C : GaussPivotTypedScan.Contract callback callbackStart callbackInit
      rows piece initialOutput context)
    (P : Nat)
    (hcycle : ∀ pre word suffix, pre ++ word :: suffix = rows →
      GaussPivotTypedScan.cycleBudget callback callbackStart callbackInit
        rows piece initialOutput context C pre word suffix ≤ P)
    (pre suffix : List (List Bool)) (hsplit : pre ++ suffix = rows) :
    GaussPivotTypedScan.remainingBudget callback callbackStart callbackInit
      rows piece initialOutput context C pre suffix ≤
        (suffix.length + 1) * (P + 2) := by
  induction suffix generalizing pre with
  | nil => simp [GaussPivotTypedScan.remainingBudget]
  | cons word tail ih =>
      have hnext : (pre ++ [word]) ++ tail = rows := by
        simpa [List.append_assoc] using hsplit
      have hc := hcycle pre word tail (by simpa using hsplit)
      have hr := ih (pre ++ [word]) hnext
      simp only [GaussPivotTypedScan.remainingBudget, List.length_cons]
      nlinarith

#print axioms getter_bound
#print axioms cellCost_bound
#print axioms remainingBudget_le_of_cycle

end CurrentAdditive.GaussSearchClock
