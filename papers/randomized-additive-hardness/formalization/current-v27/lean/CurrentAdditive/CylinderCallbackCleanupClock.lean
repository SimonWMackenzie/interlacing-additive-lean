import CurrentAdditive.CylinderCoordinateEqualityCallback
import EthInapproximability.CurrentPaper.BitMachineBankCodec
import EthInapproximability.CurrentPaper.BitMachineStackGrowth

set_option maxHeartbeats 8000000
set_option maxRecDepth 16384
set_option synthInstance.maxSize 65536

namespace CurrentAdditive.CylinderCallbackCleanupClock

open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper.BitMachineStackGrowth
open CurrentAdditive.CylinderCoordinateEqualityCallback

def cleanupCost (S : Fin 32 → List Bool) : Nat :=
  ∑ i : Fin 15, (S (cleanBank i)).length

theorem scratch_each_le_run (start : Config) (t : Nat)
    (SBefore : Fin 32 → List Bool)
    (hsecond : (run t start).stk = SBefore) (i : Fin 15) :
    (SBefore (cleanBank i)).length ≤
      (start.stk (cleanBank i)).length +
        BitMachineStackGrowth.perStep program * t := by
  have h := BitMachineStackGrowth.run_growth program start t (cleanBank i)
  change ((run t start).stk (cleanBank i)).length ≤
    (start.stk (cleanBank i)).length +
      BitMachineStackGrowth.perStep program * t at h
  rw [hsecond] at h
  exact h

theorem cleanup_sum_le_encoded (S0 SBefore : Fin 32 → List Bool)
    (T : Nat)
    (h : ∀ i : Fin 15,
      (SBefore (cleanBank i)).length ≤
        (S0 (cleanBank i)).length +
          BitMachineStackGrowth.perStep program * T) :
    cleanupCost SBefore ≤
      15 * ((BitMachineBankCodec.encode S0).length +
        BitMachineStackGrowth.perStep program * T) := by
  have hEach (i : Fin 15) :
      (SBefore (cleanBank i)).length ≤
        (BitMachineBankCodec.encode S0).length +
          BitMachineStackGrowth.perStep program * T := by
    exact (h i).trans (Nat.add_le_add_right
      (BitMachineBankCodec.word_length_le_encode S0 (cleanBank i)) _)
  unfold cleanupCost
  calc
    (∑ i : Fin 15, (SBefore (cleanBank i)).length) ≤
        ∑ _i : Fin 15,
          ((BitMachineBankCodec.encode S0).length +
            BitMachineStackGrowth.perStep program * T) :=
      Finset.sum_le_sum (fun i _ => hEach i)
    _ = 15 * ((BitMachineBankCodec.encode S0).length +
          BitMachineStackGrowth.perStep program * T) := by simp

theorem cleanup_sum_le_empty (S0 SBefore : Fin 32 → List Bool)
    (T : Nat) (hEmpty : ∀ i : Fin 15, S0 (cleanBank i) = [])
    (h : ∀ i : Fin 15,
      (SBefore (cleanBank i)).length ≤
        (S0 (cleanBank i)).length +
          BitMachineStackGrowth.perStep program * T) :
    cleanupCost SBefore ≤
      15 * (BitMachineStackGrowth.perStep program * T) := by
  have hEach (i : Fin 15) :
      (SBefore (cleanBank i)).length ≤
        BitMachineStackGrowth.perStep program * T := by
    simpa only [hEmpty i, List.length_nil, zero_add] using h i
  unfold cleanupCost
  calc
    (∑ i : Fin 15, (SBefore (cleanBank i)).length) ≤
        ∑ _i : Fin 15, BitMachineStackGrowth.perStep program * T :=
      Finset.sum_le_sum (fun i _ => hEach i)
    _ = 15 * (BitMachineStackGrowth.perStep program * T) := by simp

theorem cleanup_sum_le_empty_bound (S0 SBefore : Fin 32 → List Bool)
    (t T : Nat) (ht : t ≤ T)
    (hEmpty : ∀ i : Fin 15, S0 (cleanBank i) = [])
    (h : ∀ i : Fin 15,
      (SBefore (cleanBank i)).length ≤
        (S0 (cleanBank i)).length +
          BitMachineStackGrowth.perStep program * t) :
    cleanupCost SBefore ≤
      15 * (BitMachineStackGrowth.perStep program * T) := by
  have hsmall := cleanup_sum_le_empty S0 SBefore t hEmpty h
  have hmul := Nat.mul_le_mul_left (BitMachineStackGrowth.perStep program) ht
  exact hsmall.trans (Nat.mul_le_mul_left 15 hmul)

theorem callback_cleanup_sum_le_input
    (pre : List (List Bool)) (word : List Bool)
    (suffix : List (List Bool)) (right out : List Bool)
    (S0 SBefore : Fin 32 → List Bool)
    (h : ∀ i : Fin 15,
      (SBefore (cleanBank i)).length ≤
        (S0 (cleanBank i)).length +
          BitMachineStackGrowth.perStep program *
            (getterBound pre word suffix + 1 +
              CylinderEqualityAppendCallback.callbackBound word right out)) :
    cleanupCost SBefore ≤
      15 * ((BitMachineBankCodec.encode S0).length +
        BitMachineStackGrowth.perStep program *
          (getterBound pre word suffix + 1 +
            CylinderEqualityAppendCallback.callbackBound word right out)) :=
  cleanup_sum_le_encoded S0 SBefore _ h

theorem callback_cleanup_sum_le_empty
    (pre : List (List Bool)) (word : List Bool)
    (suffix : List (List Bool)) (right out : List Bool)
    (S0 SBefore : Fin 32 → List Bool)
    (hEmpty : ∀ i : Fin 15, S0 (cleanBank i) = [])
    (h : ∀ i : Fin 15,
      (SBefore (cleanBank i)).length ≤
        (S0 (cleanBank i)).length +
          BitMachineStackGrowth.perStep program *
            (getterBound pre word suffix + 1 +
              CylinderEqualityAppendCallback.callbackBound word right out)) :
    cleanupCost SBefore ≤
      15 * (BitMachineStackGrowth.perStep program *
        (getterBound pre word suffix + 1 +
          CylinderEqualityAppendCallback.callbackBound word right out)) :=
  cleanup_sum_le_empty S0 SBefore _ hEmpty h

#print axioms scratch_each_le_run
#print axioms cleanup_sum_le_encoded
#print axioms cleanup_sum_le_empty_bound
#print axioms callback_cleanup_sum_le_input
#print axioms callback_cleanup_sum_le_empty

end CurrentAdditive.CylinderCallbackCleanupClock
