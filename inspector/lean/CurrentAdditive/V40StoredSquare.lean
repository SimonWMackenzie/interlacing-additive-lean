import CurrentAdditive.V40StoredRectangle
import CurrentAdditive.DeterministicETHPhysicalSquare
import CurrentAdditive.V39ActualSquare

namespace CurrentAdditive.V40StoredSquare
noncomputable section
set_option maxHeartbeats 8000000
set_option maxRecDepth 32768
open Paper2 EthInapproximability.CurrentPaper EncodedCommunication
open V39GeneratedConstruction

def stageCoefficient : Nat := ASquare.Post.squareCP +
  2*(ASquare.Post.squareCP*ASquare.Post.squareMachine.pushBound+1)+
  3*(ASquare.Post.squareCP*ASquare.Post.squareMachine.pushBound+1)^1
def stageDegree : Nat := (ASquare.Post.squareEP+1)*(1+1)

/-- The inherited padding and projection machines act on the actual stored
entries. Their intermediate printed size is bounded by their actual run. -/
theorem stage_outputs (R : StoredMatrix) (b : Nat) :
    DeterministicETHPhysicalSquare.squareMatrixMachine.OutputsWithin
      (encodeInstance (DeterministicETHPhysicalSquare.rectangleInstance R.entry b))
      R.squareWord
      (stageCoefficient*((encodeInstance
        (DeterministicETHPhysicalSquare.rectangleInstance R.entry b)).length+1)^stageDegree) := by
  let I := DeterministicETHPhysicalSquare.rectangleInstance R.entry b
  have hv : I.Valid := DeterministicETHPhysicalSquare.rectangleInstance_valid
    R.entry b R.rows_pos R.cols_pos
  have hs := ASquare.Post.squarePost I hv
  have hl := BitMachine.output_length_bound ASquare.Post.squareMachine hs
  have hb := BitMachineCompositionArithmetic.composition_time_bound
    (encodeInstance I).length ASquare.Post.squareCP ASquare.Post.squareEP 3 1
    ASquare.Post.squareMachine.pushBound
    (encodeInstance (ASquare.squareInstance I)).length hl
  have hf := ASquare.Post.fullBound_le I hv
  have ho := DeterministicETHPhysicalSquare.squareMatrixMachine_outputs
    R.entry b R.rows_pos R.cols_pos
  apply BitMachine.outputsWithin_mono _ ho
  change ASquare.Post.fullBound I.rows I.cols I.threshold +
    2*(encodeInstance (ASquare.squareInstance I)).length+2+
    3*((encodeInstance (ASquare.squareInstance I)).length+1) ≤ _
  apply le_trans (Nat.add_le_add_right (Nat.add_le_add_right
    (Nat.add_le_add_right hf _) _) _)
  simpa only [pow_one,stageCoefficient,stageDegree] using hb

def machine := BitMachineComposition.composition V40StoredRectangle.machine
  DeterministicETHPhysicalSquare.squareMatrixMachine
def coefficient : Nat := V40StoredRectangle.rectangle.coefficient+
  2*(V40StoredRectangle.rectangle.coefficient*V40StoredRectangle.machine.pushBound+1)+
  stageCoefficient*(V40StoredRectangle.rectangle.coefficient*
    V40StoredRectangle.machine.pushBound+1)^stageDegree
def degree : Nat := (V40StoredRectangle.rectangle.degree+1)*(stageDegree+1)

/-- One fixed physical formatter consumes the complete retained public state.
It computes the threshold and dimensions, prints the rectangle, pads it, and
prints exactly the current canonical square estimator word. -/
theorem outputs (L K : Nat) (context : List Bool) (R : StoredMatrix) :
    machine.OutputsWithin (V40StoredRectangle.input L K context R) R.squareWord
      (coefficient*((V40StoredRectangle.input L K context R).length+1)^degree) := by
  have hr := V40StoredRectangle.outputs L K context R
  have hs := stage_outputs R (V40StoredThreshold.thresholdNumber L K)
  have hI : V40StoredRectangle.rectangleInstance L K R =
      DeterministicETHPhysicalSquare.rectangleInstance R.entry
        (V40StoredThreshold.thresholdNumber L K) := rfl
  rw [← hI] at hs
  have h := BitMachineComposition.composition_outputsWithin
    V40StoredRectangle.machine DeterministicETHPhysicalSquare.squareMatrixMachine hr hs
  apply BitMachine.outputsWithin_mono _ h
  exact BitMachineCompositionArithmetic.composition_time_bound
    (V40StoredRectangle.input L K context R).length
    V40StoredRectangle.rectangle.coefficient V40StoredRectangle.rectangle.degree
    stageCoefficient stageDegree V40StoredRectangle.machine.pushBound
    (encodeInstance (V40StoredRectangle.rectangleInstance L K R)).length
    (BitMachine.output_length_bound V40StoredRectangle.machine hr)

/-- This is the exact floor-aware public constructor's word. The retained
parameter is its actual selected logarithm, and its threshold is computed. -/
theorem public_outputs (p : SourceConstants) (floor : Nat) {n m : Nat}
    (hn : 0<n) (hlow : n≤2*m) (hdegree : 2*m≤p.degree*n)
    (edge : Fin m → Bool → Fin n) (K : Nat) (context : List Bool) :
    let L := publicLogFrom p floor n m hn hlow hdegree
    let R := publicGraphRunFrom p floor hn hlow hdegree edge K
    machine.OutputsWithin (V40StoredRectangle.input L K context R) R.squareWord
      (coefficient*((V40StoredRectangle.input L K context R).length+1)^degree) :=
  outputs _ _ _ _

#print axioms stage_outputs
#print axioms outputs
#print axioms public_outputs
end
end CurrentAdditive.V40StoredSquare
