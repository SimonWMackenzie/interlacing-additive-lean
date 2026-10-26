import CurrentAdditive.DeterministicETHEncodedTable
import Paper2.ASquarePost
import Paper2.AFrontProjection

/-! A fixed inherited physical postprocessor converts any valid indexed
rectangle instance into the canonical square matrix word sent to the estimator.
The producer of the rectangle instance is a separate Code D obligation. -/

namespace CurrentAdditive.DeterministicETHPhysicalSquare

open EthInapproximability.CurrentPaper
open CurrentAdditive.DeterministicETHEncodedTable

noncomputable def squareMatrixMachine : BitMachine.Machine :=
  BitMachineComposition.composition Paper2.ASquare.Post.squareMachine
    AFront.Projection.matrixMachine

def rectangleInstance {r c : ℕ} (F : Fin r → Fin c → Bool) (b : ℕ) :
    EncodedCommunication.Instance :=
  ⟨r, c, b, MatrixMaterialization.rowMajor F⟩

theorem rectangleInstance_valid {r c : ℕ} (F : Fin r → Fin c → Bool)
    (b : ℕ) (hr : 0 < r) (hc : 0 < c) :
    (rectangleInstance F b).Valid :=
  ⟨hr, hc, MatrixMaterialization.rowMajor_length F⟩

theorem rectangle_tableGame_rowMajor {r c : ℕ}
    (F : Fin r → Fin c → Bool) :
    ProtocolVerifier.tableGame r c (MatrixMaterialization.rowMajor F) = F := by
  funext i j
  simp only [ProtocolVerifier.tableGame, ProtocolVerifier.tableEntry,
    MatrixMaterialization.rowMajor_entry, Option.getD_some]

theorem squareMatrixMachine_outputs {r c : ℕ}
    (F : Fin r → Fin c → Bool) (b : ℕ)
    (hr : 0 < r) (hc : 0 < c) :
    squareMatrixMachine.OutputsWithin
      (EncodedCommunication.encodeInstance (rectangleInstance F b))
      (squareWord (Paper2.SquarePadding.matrix hr hc F))
      (Paper2.ASquare.Post.fullBound r c b +
        2 * (EncodedCommunication.encodeInstance
          (Paper2.ASquare.squareInstance (rectangleInstance F b))).length + 2 +
        3 * ((EncodedCommunication.encodeInstance
          (Paper2.ASquare.squareInstance (rectangleInstance F b))).length + 1)) := by
  let I := rectangleInstance F b
  have hv : I.Valid := rectangleInstance_valid F b hr hc
  have hs := Paper2.ASquare.Post.full_outputs I hv
  have hp := AFront.Projection.matrixMachine_encodeInstance
    (Paper2.ASquare.squareInstance I)
  have hout := BitMachineComposition.composition_outputsWithin
    Paper2.ASquare.Post.squareMachine AFront.Projection.matrixMachine hs hp
  have hsq : Paper2.ASquare.squareFun r c (MatrixMaterialization.rowMajor F) =
      Paper2.SquarePadding.matrix hr hc F := by
    rw [Paper2.ASquare.squareFun_eq_matrix hr hc,
      rectangle_tableGame_rowMajor]
  simpa only [squareMatrixMachine, I, rectangleInstance,
    Paper2.ASquare.squareInstance, hsq,
    AFront.Projection.matrixWord, squareWord,
    Paper2.AModel.matrixWord] using hout

#print axioms squareMatrixMachine_outputs

/-- Applied to exactly the table presentation consumed by the finite
endpoint, the inherited physical postprocessor prints the estimator input. -/
theorem paddedTable_outputs
    {Graph State : Type} (C : CurrentAdditive.DeterministicIteration.Construction Graph State)
    (N : ℕ) (P : CurrentAdditive.DeterministicEndpointAssembly.TablePresentation C N)
    (R : State) (b : ℕ) :
    let I := rectangleInstance (P.table R) b
    squareMatrixMachine.OutputsWithin
      (EncodedCommunication.encodeInstance I)
      (squareWord (CurrentAdditive.DeterministicEndpointAssembly.paddedTable C N P R))
      (Paper2.ASquare.Post.fullBound (P.rows R) (P.cols R) b +
        2 * (EncodedCommunication.encodeInstance (Paper2.ASquare.squareInstance I)).length + 2 +
        3 * ((EncodedCommunication.encodeInstance (Paper2.ASquare.squareInstance I)).length + 1)) := by
  simpa only [CurrentAdditive.DeterministicEndpointAssembly.paddedTable] using
    squareMatrixMachine_outputs (P.table R) b (P.rows_pos R) (P.cols_pos R)

#print axioms paddedTable_outputs

end CurrentAdditive.DeterministicETHPhysicalSquare
