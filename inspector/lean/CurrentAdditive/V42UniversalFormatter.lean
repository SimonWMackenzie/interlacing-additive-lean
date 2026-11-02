import CurrentAdditive.V42DeterministicRequest
import CurrentAdditive.DeterministicETHPhysicalSquare

/-! The public instance threshold is the replacement recipe's exact B_N.
One fixed formatter prints that rectangle and duplicates rows/columns to a
square power-of-two table, retaining the same threshold in its full encoding. -/

set_option maxHeartbeats 4000000
set_option maxRecDepth 65536
set_option synthInstance.maxSize 32768

namespace CurrentAdditive.V42UniversalFormatter
noncomputable section
open Paper2 EthInapproximability.CurrentPaper EncodedCommunication
open V39GeneratedConstruction

def outputInstance (L K : ℕ) (R : StoredMatrix) : Instance :=
  ASquare.squareInstance (V42DeterministicRequest.rectangleInstance L K R)
def word (L K : ℕ) (R : StoredMatrix) := encodeInstance (outputInstance L K R)
def machine := BitMachineComposition.composition V42DeterministicRequest.rectangle.machine ASquare.Post.squareMachine
def coefficient := V42DeterministicRequest.rectangle.coefficient+
  2*(V42DeterministicRequest.rectangle.coefficient*V42DeterministicRequest.rectangle.machine.pushBound+1)+
  ASquare.Post.squareCP*(V42DeterministicRequest.rectangle.coefficient*
    V42DeterministicRequest.rectangle.machine.pushBound+1)^ASquare.Post.squareEP
def degree := (V42DeterministicRequest.rectangle.degree+1)*(ASquare.Post.squareEP+1)

theorem outputs (L K : ℕ) (ctx : List Bool) (R : StoredMatrix) :
    machine.OutputsWithin (V40StoredEnvelope.input L K ctx R) (word L K R)
      (coefficient*((V40StoredEnvelope.input L K ctx R).length+1)^degree) := by
  let I:=V42DeterministicRequest.rectangleInstance L K R
  have hv : I.Valid := ⟨R.rows_pos,R.cols_pos,MatrixMaterialization.rowMajor_length R.entry⟩
  have hr:=V42DeterministicRequest.rectangle.outputs (V40StoredEnvelope.input L K ctx R)
  rw [V42DeterministicRequest.rectangle_result] at hr
  have hs:=ASquare.Post.squarePost I hv
  have h:=BitMachineComposition.composition_outputsWithin
    V42DeterministicRequest.rectangle.machine ASquare.Post.squareMachine hr hs
  apply BitMachine.outputsWithin_mono _ h
  exact BitMachineCompositionArithmetic.composition_time_bound
    (V40StoredEnvelope.input L K ctx R).length
    V42DeterministicRequest.rectangle.coefficient V42DeterministicRequest.rectangle.degree
    ASquare.Post.squareCP ASquare.Post.squareEP V42DeterministicRequest.rectangle.machine.pushBound
    (encodeInstance I).length
    (BitMachine.output_length_bound V42DeterministicRequest.rectangle.machine hr)

theorem instance_valid (L K : ℕ) (R : StoredMatrix) : (outputInstance L K R).Valid :=
  ASquare.squareInstance_valid _

theorem cost (L K : ℕ) (R : StoredMatrix) :
    Workspace.Types.CommComplexity.D (ProtocolVerifier.tableGame (outputInstance L K R).rows
      (outputInstance L K R).cols (outputInstance L K R).table)=Workspace.Types.CommComplexity.D R.entry := by
  change Workspace.Types.CommComplexity.D
    (ProtocolVerifier.tableGame (SquarePadding.side R.rows R.cols) (SquarePadding.side R.rows R.cols)
      (MatrixMaterialization.rowMajor
        (ASquare.squareFun R.rows R.cols (MatrixMaterialization.rowMajor R.entry))))=_
  rw [DeterministicETHEncodedTable.tableGame_rowMajor,
    ASquare.squareFun_eq_matrix R.rows_pos R.cols_pos,
    DeterministicETHPhysicalSquare.rectangle_tableGame_rowMajor,
    SquarePadding.D_matrix]

theorem shape (L K : ℕ) (R : StoredMatrix) :
    (outputInstance L K R).rows=SquarePadding.side R.rows R.cols ∧
    (outputInstance L K R).cols=(outputInstance L K R).rows ∧
    (outputInstance L K R).threshold=V42DeterministicRequest.thresholdNumber L K ∧
    ∃ e, (outputInstance L K R).rows=2^e :=
  ⟨rfl,rfl,rfl,SquarePadding.exponent R.rows R.cols,rfl⟩

#print axioms outputs
#print axioms cost

end
end CurrentAdditive.V42UniversalFormatter

