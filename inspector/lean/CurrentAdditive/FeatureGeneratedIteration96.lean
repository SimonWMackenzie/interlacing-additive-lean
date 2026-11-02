import CurrentAdditive.FeatureCoordinateTransition96
import EthInapproximability.CurrentPaper.BitMachineIteration

/-! Actual repeated execution of the fixed coordinate machine. The displayed
sum budgets are exact finite envelopes; a separate scalar proof bounds them
by a polynomial in the original raw production input. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option synthInstance.maxSize 65536
set_option maxRecDepth 4096
namespace CurrentAdditive.FeatureGeneratedIteration96
open Turing EthInapproximability.CurrentPaper BitMachineEncoding
open CurrentAdditive.FeatureOldDescriptorSemantics96
abbrev M := FeatureCoordinateTransition96.machine

def featuresAt (j : Nat) (ys : List Nat) := CylinderOrderedSpec.generatedList j 8192 ys

theorem featuresAt_zero (ys : List Nat) : featuresAt 0 ys=[[]] := rfl

theorem featuresAt_succ (j : Nat) (ys : List Nat) :
    featuresAt (j+1) ys=next j ys (featuresAt j ys) := by
  simp [featuresAt,CylinderOrderedSpec.generatedList,List.range_succ,List.foldl_append,
    next]

def states (ys : List Nat) (carry : List Bool) (j : Nat) :=
  FeatureCoordinateTransition96.stateWord j ys (featuresAt j ys) [] [] carry

def timeBound (q : Nat) (ys : List Nat) (carry : List Bool) :=
  ∑ j ∈ Finset.range q,
    FeatureCoordinateTransition96.packetClock j ys (featuresAt j ys) [] [] carry

def lengthBound (q : Nat) (ys : List Nat) (carry : List Bool) :=
  ∑ j ∈ Finset.range (q+1), (states ys carry j).length

def clock (q : Nat) (ys : List Nat) (carry : List Bool) :=
  q*BitMachineIteration.roundBound M (lengthBound q ys carry) (timeBound q ys carry)+1

theorem step_outputs (j : Nat) (ys : List Nat) (carry : List Bool) :
    M.OutputsWithin (states ys carry j) (states ys carry (j+1))
      (FeatureCoordinateTransition96.packetClock j ys (featuresAt j ys) [] [] carry) := by
  simpa only [states,featuresAt_succ] using
    FeatureCoordinateTransition96.outputs j ys (featuresAt j ys) [] [] carry

theorem step_time_le (q j : Nat) (ys : List Nat) (carry : List Bool) (hj : j<q) :
    FeatureCoordinateTransition96.packetClock j ys (featuresAt j ys) [] [] carry ≤
      timeBound q ys carry := by
  dsimp only [timeBound]
  exact Finset.single_le_sum
    (f := fun n => FeatureCoordinateTransition96.packetClock n ys (featuresAt n ys) [] [] carry)
    (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr hj)

theorem state_length_le (q j : Nat) (ys : List Nat) (carry : List Bool) (hj : j<q) :
    (states ys carry j).length ≤ lengthBound q ys carry := by
  dsimp only [lengthBound]
  exact Finset.single_le_sum (f := fun n => (states ys carry n).length) (fun _ _ => Nat.zero_le _)
    (Finset.mem_range.mpr (by omega : j<q+1))

theorem actual_run (q : Nat) (ys : List Nat) (carry : List Bool) :
    ∃ t ≤ clock q ys carry,
      BitMachineIteration.run M t
        (BitMachineIteration.ready M (states ys carry 0) (List.replicate q true))=
      BitMachineIteration.finished M (states ys carry q) := by
  have hstep (j : Nat) (hj : j<(List.replicate q true).length) :
      M.OutputsWithin (states ys carry j) (states ys carry (j+1))
        (timeBound q ys carry) :=
    BitMachine.outputsWithin_mono M (step_outputs j ys carry)
      (step_time_le q j ys carry (by simpa using hj))
  have hlen (j : Nat) (hj : j<(List.replicate q true).length) :
      (states ys carry j).length ≤ lengthBound q ys carry :=
    state_length_le q j ys carry (by simpa using hj)
  simpa only [List.length_replicate,clock] using
    BitMachineIteration.iteration_run M (states ys carry) (List.replicate q true)
      (lengthBound q ys carry) (timeBound q ys carry) hstep hlen

#print axioms featuresAt_succ
#print axioms actual_run
end CurrentAdditive.FeatureGeneratedIteration96
