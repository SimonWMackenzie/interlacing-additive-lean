import CurrentAdditive.GaussControlTrace
import EthInapproximability.CurrentPaper.BitMachineIteration

/-!
This file instantiates the inherited literal TM2 fuel loop on the exact Gauss
state trace.  Its hypothesis is deliberately an actual `OutputsWithin` proof
for one fixed step machine on every visited state; it is not a completed Gauss
machine.  The bound charges the entire m-by-k state packet and k calls.
-/

namespace CurrentAdditive.GaussIterationBridge

open CurrentAdditive.GaussControlTrace
open EthInapproximability.CurrentPaper

theorem actual_fixed_loop_from_step {m k M : Nat}
    (A : Matrix (Fin m) (Fin k) ℤ)
    (h01 : ∀ i j, A i j = 0 ∨ A i j = 1)
    (hk : k ≤ m * M)
    (stepMachine : BitMachine.Machine) (T : Nat)
    (hstep : ∀ t < k,
      stepMachine.OutputsWithin
        (statePacket (after (fun i j => (A i j : ℚ)) t))
        (statePacket (after (fun i j => (A i j : ℚ)) (t + 1))) T) :
    ∃ u ≤ k * BitMachineIteration.roundBound stepMachine
        (fullSupportStatePoly m M) T + 1,
      let c := BitMachineIteration.run stepMachine u
        (BitMachineIteration.ready stepMachine
          (statePacket (initial (fun i j => (A i j : ℚ))))
          (List.replicate k true))
      c.l = none ∧
      c.stk (.inl stepMachine.input) =
        statePacket (after (fun i j => (A i j : ℚ)) k) := by
  let states : Nat → List Bool := fun t =>
    statePacket (after (fun i j => (A i j : ℚ)) t)
  have hlen : ∀ j < (List.replicate k true).length,
      (states j).length ≤ fullSupportStatePoly m M := by
    intro j hj
    have ht : j ≤ k := by simpa using Nat.le_of_lt (by simpa using hj)
    exact actual_statePacket_full_support A h01 hk j ht
  have hstep' : ∀ j < (List.replicate k true).length,
      stepMachine.OutputsWithin (states j) (states (j + 1)) T := by
    intro j hj
    exact hstep j (by simpa using hj)
  obtain ⟨u, hu, hc, ho⟩ :=
    BitMachineIteration.iteration_output stepMachine states
      (List.replicate k true) (fullSupportStatePoly m M) T hstep' hlen
  refine ⟨u, by simpa using hu, ?_⟩
  simpa [states, after, initial] using And.intro hc ho

#print axioms actual_fixed_loop_from_step

end CurrentAdditive.GaussIterationBridge
