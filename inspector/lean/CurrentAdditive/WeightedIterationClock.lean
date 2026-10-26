import EthInapproximability.CurrentPaper.BitMachineIteration

/-! Charged iteration with a separate actual-machine bound at every round.
This intermediate combinator will be instantiated by the concrete weighted
StoredMatrix step; it does not assume a successful whole iteration. -/

namespace CurrentAdditive.WeightedIterationClock

open EthInapproximability.CurrentPaper
open scoped BigOperators

variable (M : BitMachine.Machine)

def cumulative (states : Nat → List Bool) (b : Nat → Nat) (k : Nat) : Nat :=
  (∑ j : Fin k, BitMachineIteration.roundBound M (states j.val).length (b j.val))+1

theorem cumulative_zero (states : Nat → List Bool) (b : Nat → Nat) :
    cumulative M states b 0 = 1 := by simp [cumulative]

theorem cumulative_succ (states : Nat → List Bool) (b : Nat → Nat) (k : Nat) :
    cumulative M states b (k+1) =
      BitMachineIteration.roundBound M (states 0).length (b 0) +
        cumulative M (fun j => states (j+1)) (fun j => b (j+1)) k := by
  simp [cumulative,Fin.sum_univ_succ,Nat.add_assoc]

theorem run (states : Nat → List Bool) (b : Nat → Nat) (fuel : List Bool)
    (hstep : ∀ j < fuel.length, M.OutputsWithin (states j) (states (j+1)) (b j)) :
    ∃ t ≤ cumulative M states b fuel.length,
      BitMachineIteration.run M t (BitMachineIteration.ready M (states 0) fuel) =
        BitMachineIteration.finished M (states fuel.length) := by
  induction fuel generalizing states b with
  | nil =>
      refine ⟨1,by simp [cumulative],?_⟩
      simpa only [BitMachineIteration.run,Function.iterate_one,List.length_nil]
        using BitMachineIteration.fuel_nil M (states 0)
  | cons bit fuel ih =>
      obtain ⟨t,ht,hr⟩ := BitMachineIteration.round_run M bit fuel (hstep 0 (by simp))
      obtain ⟨u,hu,hur⟩ := ih (fun j => states (j+1)) (fun j => b (j+1))
        (fun j hj => hstep (j+1) (by simp only [List.length_cons];omega))
      refine ⟨t+u,?_,?_⟩
      · rw [List.length_cons,cumulative_succ]
        omega
      · rw [BitMachineIteration.run,Nat.add_comm t u,Function.iterate_add_apply]
        change ((BitMachineEncoding.advance (BitMachineIteration.program M))^[u])
          (BitMachineIteration.run M t _) = _
        rw [hr]
        simpa only [BitMachineIteration.run,List.length_cons] using hur

theorem cumulative_le (states : Nat → List Bool) (b : Nat → Nat) (k L T : Nat)
    (hlen : ∀ j < k, (states j).length ≤ L)
    (htime : ∀ j < k, b j ≤ T) :
    cumulative M states b k ≤ k*BitMachineIteration.roundBound M L T+1 := by
  unfold cumulative
  apply Nat.add_le_add_right
  calc
    _ ≤ ∑ _ : Fin k, BitMachineIteration.roundBound M L T := by
      apply Finset.sum_le_sum
      intro j _
      unfold BitMachineIteration.roundBound
      have hl := hlen j.val j.isLt
      have ht := htime j.val j.isLt
      gcongr
    _ = _ := by simp

#print axioms run
#print axioms cumulative_le

end CurrentAdditive.WeightedIterationClock
