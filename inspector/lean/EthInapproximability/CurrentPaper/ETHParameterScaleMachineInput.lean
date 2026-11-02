import EthInapproximability.CurrentPaper.Parameters
import EthInapproximability.CurrentPaper.ETHParameterScaleMachineMax

/-! Exact six supplied unary words for the literal single-scale parameter.
`incomingDepth` is deliberately absent because `Parameters.scale` does not
read it. This file does not derive the words from an original graph. -/

namespace EthInapproximability.CurrentPaper.ETHParameterScaleMachineInput

def words (i : Parameters.Input) : Fin 6 → List Bool :=
  ![List.replicate i.sourceConstant true,
    List.replicate i.nextDepth true,
    List.replicate i.cost true,
    List.replicate i.rows true,
    List.replicate i.columns true,
    List.replicate i.edges true]

def wordSize (i : Parameters.Input) : ℕ :=
  i.sourceConstant + i.nextDepth + i.cost + i.rows + i.columns + i.edges

def candidates (i : Parameters.Input) : List ℕ :=
  [Nat.clog 2 (i.edges+2), Nat.clog 2 i.columns,
    Nat.clog 2 i.rows, i.cost, i.nextDepth, i.sourceConstant]

theorem candidate_fold_eq_scaleBound (i : Parameters.Input) :
    (candidates i).foldl max 2 = Parameters.scaleBound i := by
  simp only [candidates, List.foldl_cons, List.foldl_nil,
    Parameters.scaleBound, Parameters.namingLength]
  ac_rfl

theorem scale_eq_candidate_fold (i : Parameters.Input) :
    Parameters.scale i =
      max (2^24) (Nat.clog 2 ((candidates i).foldl max 2)) := by
  rw [candidate_fold_eq_scaleBound]
  rfl

theorem word_lengths (i : Parameters.Input) :
    (words i 0).length = i.sourceConstant ∧
    (words i 1).length = i.nextDepth ∧
    (words i 2).length = i.cost ∧
    (words i 3).length = i.rows ∧
    (words i 4).length = i.columns ∧
    (words i 5).length = i.edges := by
  simp [words]

end EthInapproximability.CurrentPaper.ETHParameterScaleMachineInput
