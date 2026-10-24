import Paper2.E2Core
import Paper2.ASquare

/-! a-eth-owner-2 copy of frozen `a-eth-owner-1/AEthDSquare.lean` (SHA-256 2610c5fa1a498a8e38110524611b75a9a1a308f53506d1f4ab38fd349f214bea). Changes: import `AEthDT24` -> `E2Core`; removed everything from `RealisesMidpointSq` to the end of the namespace (`RealisesMidpointSq`, `decider_error_sq`, `DeciderAssemblySq`, `T24_square_class_decided`, `T03_square_class_decided`: route-A / prefix-carrier material, the latter two concluding `¬ AModel.RandomizedSparseETH`) and their #print lines. -/

/-!
# Lane `owner:a-decider-2` (Paper A, lock v12): the square power-of-two variant of T24 at class level

Private module, 27 September 2026. Nothing here is admitted; no ledger row is closed.

Lock v12 `06-reduction.tex:115-116`: "The conclusion also holds when the inputs are square matrices of
power-of-two side length." Proof, `06-reduction.tex:143-148`: "To obtain a square power-of-two table,
let $S$ be the least power of two at least $m_Y$, and repeat rows and columns until both dimensions are
$S$. Every original row and column is retained, so these repetitions preserve communication
complexity exactly. Since $m_Y/m_X=\Theta(L)$, $\log(S^2)=\log T+O(\log L)$; the leading constant in
\cref{eq:quantitative-size} is unchanged."

The estimator hypothesis `EstimatesGrowingSq` is required ONLY on square power-of-two matrix words
(`SquareWord`), with accuracy `c·log₂T/log₂log₂T` at `T = S²` the number of entries of the input
word. The decider runs the estimator on `mwSqOf`, the matrix word of the admitted square table
`ASquare.squareTable` (side `SquarePadding.side rows cols = 2^exponent`), whose `D` equals `D` of the
printed table (admitted `ASquare.D_squareTable`). The law level is the admitted
`A3CloseEndpoints.T24_final` at `square = true`.
-/

set_option maxHeartbeats 4000000

namespace Paper2.ADecider

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.EncodedETHSource
open EthInapproximability.CurrentPaper.EncodedETHSourceComposition
open Paper2 Paper2.FiniteLaw Paper2.Unit4Shell.T10Finite Paper2.Unit4Shell.Asymptotics
open Paper2.Unit4Shell.Definitions (uniformTape)
open Paper2.Unit4Shell.Amplification (reps)
open Paper2.MedianOwner

variable (D : DinurReduction) (B : BOTReduction (booleanOccurrence D))

set_option hygiene false in
local notation "EXP" Φ:max k:max => TotalFiniteConstructorScratch.experiment (t10_vertices_pos D B Φ)
  (CanonicalEdgeTape.graphEdge (t10Graph D B Φ) (t10Graph_valid D B Φ)) B.degreeBound (sourceGap D B) k

/-- The table read from a row-major word is the tabulated function. -/
theorem tableGame_rowMajor {r c : ℕ} (F : Fin r → Fin c → Bool) :
    ProtocolVerifier.tableGame r c (MatrixMaterialization.rowMajor F) = F := by
  funext i j
  simp only [ProtocolVerifier.tableGame, ProtocolVerifier.tableEntry,
    MatrixMaterialization.rowMajor_entry, Option.getD_some]

/-- A square power-of-two matrix word (lock `06-reduction.tex:115-116`). -/
def SquareWord (w : List Bool) : Prop :=
  ∃ (e : ℕ) (table : List Bool), AModel.decodeMatrix w = some (2 ^ e, 2 ^ e, table)

/-- **The estimator hypothesis of the square sentence**: `EstimatesGrowing` required only on square
power-of-two matrix words. -/
def EstimatesGrowingSq (E : AModel.PrefixAlgorithm) (c : ℝ) : Prop :=
  ∀ w (d : ℕ), AModel.targetD w = some d → SquareWord w →
    2 / 3 ≤ E.prob w (fun out => ∃ v, AModel.decodeDyadic out = some v ∧ |v - d| ≤ accT c w)

theorem estimatesGrowingSq_of (E : AModel.PrefixAlgorithm) (c : ℝ) (h : EstimatesGrowing E c) :
    EstimatesGrowingSq E c :=
  fun w d hd _ => h w d hd

/-- The square matrix word of reduction tape `b`: side `S = SquarePadding.side rows cols`, table the
row-major serialization of the admitted `ASquare.squareTable`. -/
noncomputable def mwSqOf (Φ : ValidFormula) (k : ℕ) (b : (EXP Φ k).output.Tape) : List Bool :=
  AModel.matrixWord (SquarePadding.side (EXP Φ k).output.rows (EXP Φ k).output.cols)
    (SquarePadding.side (EXP Φ k).output.rows (EXP Φ k).output.cols)
    (MatrixMaterialization.rowMajor (ASquare.squareTable (EXP Φ k).output b))

theorem mwSqOf_valid (Φ : ValidFormula) (k : ℕ) (b : (EXP Φ k).output.Tape) :
    AModel.MatrixValid (SquarePadding.side (EXP Φ k).output.rows (EXP Φ k).output.cols)
      (SquarePadding.side (EXP Φ k).output.rows (EXP Φ k).output.cols)
      (MatrixMaterialization.rowMajor (ASquare.squareTable (EXP Φ k).output b)) :=
  ⟨SquarePadding.side_pos _ _, SquarePadding.side_pos _ _,
    MatrixMaterialization.rowMajor_length _⟩

theorem targetD_mwSqOf (Φ : ValidFormula) (k : ℕ) (b : (EXP Φ k).output.Tape) :
    AModel.targetD (mwSqOf D B Φ k b) =
      some (Workspace.Types.CommComplexity.D ((EXP Φ k).output.table b).matrix) := by
  unfold mwSqOf
  rw [AModel.targetD_matrixWord (mwSqOf_valid D B Φ k b), tableGame_rowMajor,
    ASquare.D_squareTable _ (exp_dims_pos D B Φ k).1 (exp_dims_pos D B Φ k).2]

theorem squareWord_mwSqOf (Φ : ValidFormula) (k : ℕ) (b : (EXP Φ k).output.Tape) :
    SquareWord (mwSqOf D B Φ k b) :=
  ⟨SquarePadding.exponent (EXP Φ k).output.rows (EXP Φ k).output.cols, _,
    AModel.decodeMatrix_matrixWord (mwSqOf_valid D B Φ k b)⟩

theorem accT_mwSqOf (c : ℝ) (Φ : ValidFormula) (k : ℕ) (b : (EXP Φ k).output.Tape) :
    accT c (mwSqOf D B Φ k b) =
      c * (Real.logb 2 ((SquarePadding.entries (EXP Φ k).output.rows (EXP Φ k).output.cols : ℕ) : ℝ) /
        Real.logb 2 (Real.logb 2
          ((SquarePadding.entries (EXP Φ k).output.rows (EXP Φ k).output.cols : ℕ) : ℝ))) := by
  unfold accT mwSqOf
  rw [AModel.decodeMatrix_matrixWord (mwSqOf_valid D B Φ k b)]
  rfl

end Paper2.ADecider

#print axioms Paper2.ADecider.tableGame_rowMajor
#print axioms Paper2.ADecider.estimatesGrowingSq_of
#print axioms Paper2.ADecider.targetD_mwSqOf
#print axioms Paper2.ADecider.squareWord_mwSqOf
#print axioms Paper2.ADecider.accT_mwSqOf
