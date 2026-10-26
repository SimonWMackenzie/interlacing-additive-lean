import CurrentAdditive.QuarticSquareAsymptotics
import CurrentAdditive.QuarticEncodedOutput
import CurrentAdditive.EventualDomain
import Paper2.ASquare

/-! Exact estimator words for the actual v27 selected output. -/

noncomputable section

namespace Paper2.CurrentAdditive.QuarticConstructor

open _root_.CurrentAdditive.Eventual

open EthInapproximability.CurrentPaper
open Workspace.Types.CommComplexity

def matrixWord27 {n m : ℕ} (hn : 0 < n)
    (edge : Fin m → Bool → Fin n) (Δ : ℕ) (γ : ℚ) (k : ℕ)
    (t : (select27 hn edge Δ γ k).Tape) : List Bool :=
  let o := select27 hn edge Δ γ k
  AModel.matrixWord o.rows o.cols (o.table t).bits

theorem matrixWord27_valid {n m : ℕ} (hn : 0 < n)
    (edge : Fin m → Bool → Fin n) (Δ : ℕ) (γ : ℚ) (k : ℕ)
    (t : (select27 hn edge Δ γ k).Tape) :
    let o := select27 hn edge Δ γ k
    AModel.MatrixValid o.rows o.cols (o.table t).bits := by
  dsimp only
  obtain ⟨hr, hc⟩ := select27_dimensions_pos hn edge Δ γ k
  exact ⟨hr, hc, (select27_exact_lengths hn edge Δ γ k t).1⟩

theorem matrixWord27_target {n m : ℕ} (hn : 0 < n)
    (edge : Fin m → Bool → Fin n) (Δ : ℕ) (γ : ℚ) (k : ℕ)
    (t : (select27 hn edge Δ γ k).Tape) :
    AModel.targetD (matrixWord27 hn edge Δ γ k t) =
      some (D ((select27 hn edge Δ γ k).table t).matrix) := by
  unfold matrixWord27
  rw [AModel.targetD_matrixWord (matrixWord27_valid hn edge Δ γ k t),
    EncodedSelectedOutput.tableGame_eq_matrix]

theorem matrixWord27_entries {n m : ℕ} (hn : 0 < n)
    (edge : Fin m → Bool → Fin n) (Δ : ℕ) (γ : ℚ) (k : ℕ)
    (t : (select27 hn edge Δ γ k).Tape) :
    entries (matrixWord27 hn edge Δ γ k t) =
      (select27 hn edge Δ γ k).rows * (select27 hn edge Δ γ k).cols := by
  unfold matrixWord27
  exact entries_matrixWord _ _ _ (matrixWord27_valid hn edge Δ γ k t)

theorem matrixWord27_accuracy {n m : ℕ} (hn : 0 < n)
    (edge : Fin m → Bool → Fin n) (Δ : ℕ) (γ : ℚ) (k : ℕ)
    (t : (select27 hn edge Δ γ k).Tape) (c : ℝ) :
    ADecider.accT c (matrixWord27 hn edge Δ γ k t) =
      c * (Real.logb 2 (((select27 hn edge Δ γ k).rows *
          (select27 hn edge Δ γ k).cols : ℕ) : ℝ) /
        Real.logb 2 (Real.logb 2 (((select27 hn edge Δ γ k).rows *
          (select27 hn edge Δ γ k).cols : ℕ) : ℝ))) := by
  unfold matrixWord27 ADecider.accT
  rw [AModel.decodeMatrix_matrixWord (matrixWord27_valid hn edge Δ γ k t)]

def squareWord27 {n m : ℕ} (hn : 0 < n)
    (edge : Fin m → Bool → Fin n) (Δ : ℕ) (γ : ℚ) (k : ℕ)
    (t : (select27 hn edge Δ γ k).Tape) : List Bool :=
  let o := select27 hn edge Δ γ k
  AModel.matrixWord (SquarePadding.side o.rows o.cols)
    (SquarePadding.side o.rows o.cols)
    (MatrixMaterialization.rowMajor (ASquare.squareTable o t))

theorem squareWord27_valid {n m : ℕ} (hn : 0 < n)
    (edge : Fin m → Bool → Fin n) (Δ : ℕ) (γ : ℚ) (k : ℕ)
    (t : (select27 hn edge Δ γ k).Tape) :
    let o := select27 hn edge Δ γ k
    AModel.MatrixValid (SquarePadding.side o.rows o.cols)
      (SquarePadding.side o.rows o.cols)
      (MatrixMaterialization.rowMajor (ASquare.squareTable o t)) := by
  dsimp only
  exact ⟨SquarePadding.side_pos _ _, SquarePadding.side_pos _ _,
    MatrixMaterialization.rowMajor_length _⟩

theorem squareWord27_target {n m : ℕ} (hn : 0 < n)
    (edge : Fin m → Bool → Fin n) (Δ : ℕ) (γ : ℚ) (k : ℕ)
    (t : (select27 hn edge Δ γ k).Tape) :
    AModel.targetD (squareWord27 hn edge Δ γ k t) =
      some (D ((select27 hn edge Δ γ k).table t).matrix) := by
  unfold squareWord27
  rw [AModel.targetD_matrixWord (squareWord27_valid hn edge Δ γ k t),
    ADecider.tableGame_rowMajor,
    ASquare.D_squareTable _ (select27_dimensions_pos hn edge Δ γ k).1
      (select27_dimensions_pos hn edge Δ γ k).2]

theorem squareWord27_square {n m : ℕ} (hn : 0 < n)
    (edge : Fin m → Bool → Fin n) (Δ : ℕ) (γ : ℚ) (k : ℕ)
    (t : (select27 hn edge Δ γ k).Tape) :
    ADecider.SquareWord (squareWord27 hn edge Δ γ k t) :=
  ⟨SquarePadding.exponent _ _, _,
    AModel.decodeMatrix_matrixWord (squareWord27_valid hn edge Δ γ k t)⟩

theorem squareWord27_entries {n m : ℕ} (hn : 0 < n)
    (edge : Fin m → Bool → Fin n) (Δ : ℕ) (γ : ℚ) (k : ℕ)
    (t : (select27 hn edge Δ γ k).Tape) :
    entries (squareWord27 hn edge Δ γ k t) =
      SquarePadding.entries (select27 hn edge Δ γ k).rows
        (select27 hn edge Δ γ k).cols := by
  unfold squareWord27 SquarePadding.entries
  exact entries_matrixWord _ _ _ (squareWord27_valid hn edge Δ γ k t)

theorem squareWord27_accuracy {n m : ℕ} (hn : 0 < n)
    (edge : Fin m → Bool → Fin n) (Δ : ℕ) (γ : ℚ) (k : ℕ)
    (t : (select27 hn edge Δ γ k).Tape) (c : ℝ) :
    ADecider.accT c (squareWord27 hn edge Δ γ k t) =
      c * (Real.logb 2 ((SquarePadding.entries
        (select27 hn edge Δ γ k).rows (select27 hn edge Δ γ k).cols : ℕ) : ℝ) /
        Real.logb 2 (Real.logb 2 ((SquarePadding.entries
        (select27 hn edge Δ γ k).rows (select27 hn edge Δ γ k).cols : ℕ) : ℝ))) := by
  unfold squareWord27 ADecider.accT SquarePadding.entries
  rw [AModel.decodeMatrix_matrixWord (squareWord27_valid hn edge Δ γ k t)]

#print axioms matrixWord27_target
#print axioms matrixWord27_accuracy
#print axioms squareWord27_target
#print axioms squareWord27_square
#print axioms squareWord27_accuracy

end Paper2.CurrentAdditive.QuarticConstructor
