import CurrentAdditive.DeterministicEndpointDecision
import Paper2.AModelEstimator

/-! The finite endpoint's actual padded Boolean function is serialized as
the adopted canonical matrix word. This is the exact input consumed by the
deterministic estimator, not a cost oracle. -/

namespace CurrentAdditive.DeterministicETHEncodedTable

open EthInapproximability.CurrentPaper
open Workspace.Types.CommComplexity

variable {S : ℕ}

def squareWord (F : Fin S → Fin S → Bool) : List Bool :=
  Paper2.AModel.matrixWord S S (MatrixMaterialization.rowMajor F)

theorem tableGame_rowMajor (F : Fin S → Fin S → Bool) :
    ProtocolVerifier.tableGame S S (MatrixMaterialization.rowMajor F) = F := by
  funext i j
  simp only [ProtocolVerifier.tableGame, ProtocolVerifier.tableEntry,
    MatrixMaterialization.rowMajor_entry, Option.getD_some]

theorem squareWord_valid (F : Fin S → Fin S → Bool) (hS : 0 < S) :
    Paper2.AModel.MatrixValid S S (MatrixMaterialization.rowMajor F) :=
  ⟨hS, hS, MatrixMaterialization.rowMajor_length F⟩

theorem squareWord_decodes (F : Fin S → Fin S → Bool) (hS : 0 < S) :
    Paper2.AModel.decodeMatrix (squareWord F) =
      some (S,S,MatrixMaterialization.rowMajor F) :=
  Paper2.AModel.decodeMatrix_matrixWord (squareWord_valid F hS)

theorem squareWord_targetD (F : Fin S → Fin S → Bool) (hS : 0 < S) :
    Paper2.AModel.targetD (squareWord F) = some (D F) := by
  unfold squareWord
  rw [Paper2.AModel.targetD_matrixWord (squareWord_valid F hS),
    tableGame_rowMajor]

theorem squareWord_length_le (F : Fin S → Fin S → Bool) (hS : 0 < S) :
    (squareWord F).length ≤ 5 * S^2 + 2 := by
  have hfield := EncodedGraph.natField_length_upper S
  have hSsq : S ≤ S^2 := by
    calc
      S = S*1 := by omega
      _ ≤ S*S := Nat.mul_le_mul_left _ hS
      _ = S^2 := by ring
  have hlen : (squareWord F).length =
      2 * (EncodedCommunication.natField S).length + S^2 := by
    simp only [squareWord, Paper2.AModel.matrixWord, List.length_append,
      MatrixMaterialization.rowMajor_length]
    ring
  rw [hlen]
  omega

#print axioms squareWord_decodes
#print axioms squareWord_targetD
#print axioms squareWord_length_le

end CurrentAdditive.DeterministicETHEncodedTable
