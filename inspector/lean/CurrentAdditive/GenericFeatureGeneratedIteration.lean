import CurrentAdditive.GenericFeatureCoordinateTransition
import EthInapproximability.CurrentPaper.BitMachineIteration

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option synthInstance.maxSize 65536
set_option maxRecDepth 4096
namespace CurrentAdditive.GenericFeatureGeneratedIteration
open Turing EthInapproximability.CurrentPaper BitMachineEncoding
open GenericFeatureOldDescriptorSemantics

abbrev M (D : Nat) := GenericFeatureCoordinateTransition.machine D
def featuresAt (D j : Nat) (ys : List Nat) := CylinderOrderedSpec.generatedList j D ys
theorem featuresAt_zero (D : Nat) (ys : List Nat) : featuresAt D 0 ys = [[]] := rfl
theorem featuresAt_succ (D j : Nat) (ys : List Nat) :
    featuresAt D (j + 1) ys = next D j ys (featuresAt D j ys) := by
  simp [featuresAt, CylinderOrderedSpec.generatedList, List.range_succ, List.foldl_append, next]

def states (D : Nat) (ys : List Nat) (carry : List Bool) (j : Nat) :=
  GenericFeatureCoordinateTransition.stateWord j ys (featuresAt D j ys) [] [] carry

theorem states_layout (D : Nat) (ys : List Nat) (carry : List Bool) (j : Nat) :
    states D ys carry j = BitMachineBankCodec.encode
      (FeatureCoordinateStage96.initialBank j ys (featuresAt D j ys) [] [] carry) := rfl

def timeBound (D q : Nat) (ys : List Nat) (carry : List Bool) :=
  ∑ j ∈ Finset.range q,
    GenericFeatureCoordinateTransition.packetClock D j ys (featuresAt D j ys) [] [] carry

def lengthBound (D q : Nat) (ys : List Nat) (carry : List Bool) :=
  ∑ j ∈ Finset.range (q + 1), (states D ys carry j).length

def clock (D q : Nat) (ys : List Nat) (carry : List Bool) :=
  q * BitMachineIteration.roundBound (M D) (lengthBound D q ys carry) (timeBound D q ys carry) + 1

theorem step_outputs (D j : Nat) (ys : List Nat) (carry : List Bool) :
    (M D).OutputsWithin (states D ys carry j) (states D ys carry (j + 1))
      (GenericFeatureCoordinateTransition.packetClock D j ys (featuresAt D j ys) [] [] carry) := by
  simpa only [states, featuresAt_succ] using
    GenericFeatureCoordinateTransition.outputs D j ys (featuresAt D j ys) [] [] carry

theorem step_time_le (D q j : Nat) (ys : List Nat) (carry : List Bool) (hj : j < q) :
    GenericFeatureCoordinateTransition.packetClock D j ys (featuresAt D j ys) [] [] carry ≤
      timeBound D q ys carry := by
  dsimp only [timeBound]
  exact Finset.single_le_sum
    (f := fun n => GenericFeatureCoordinateTransition.packetClock D n ys (featuresAt D n ys) [] [] carry)
    (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr hj)

theorem state_length_le (D q j : Nat) (ys : List Nat) (carry : List Bool) (hj : j < q) :
    (states D ys carry j).length ≤ lengthBound D q ys carry := by
  dsimp only [lengthBound]
  exact Finset.single_le_sum (f := fun n => (states D ys carry n).length) (fun _ _ => Nat.zero_le _)
    (Finset.mem_range.mpr (by omega : j < q + 1))

/-- Every coordinate is executed by the exact fixed-D transition. All
descriptor order, duplicate positions, counts and retained banks follow the
literal generatedList semantics, without a callback or run premise. -/
theorem actual_run (D q : Nat) (ys : List Nat) (carry : List Bool) :
    ∃ t ≤ clock D q ys carry,
      BitMachineIteration.run (M D) t
        (BitMachineIteration.ready (M D) (states D ys carry 0) (List.replicate q true)) =
      BitMachineIteration.finished (M D) (states D ys carry q) := by
  have hstep (j : Nat) (hj : j < (List.replicate q true).length) :
      (M D).OutputsWithin (states D ys carry j) (states D ys carry (j + 1))
        (timeBound D q ys carry) :=
    BitMachine.outputsWithin_mono (M D) (step_outputs D j ys carry)
      (step_time_le D q j ys carry (by simpa using hj))
  have hlen (j : Nat) (hj : j < (List.replicate q true).length) :
      (states D ys carry j).length ≤ lengthBound D q ys carry :=
    state_length_le D q j ys carry (by simpa using hj)
  simpa only [List.length_replicate, clock] using
    BitMachineIteration.iteration_run (M D) (states D ys carry) (List.replicate q true)
      (lengthBound D q ys carry) (timeBound D q ys carry) hstep hlen

#print axioms actual_run
#print axioms states_layout
end CurrentAdditive.GenericFeatureGeneratedIteration
