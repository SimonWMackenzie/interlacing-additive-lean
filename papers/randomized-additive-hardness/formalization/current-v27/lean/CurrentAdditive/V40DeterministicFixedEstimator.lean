import CurrentAdditive.V40DeterministicStoredClassifier
import CurrentAdditive.V40DeterministicFixedGap
import CurrentAdditive.DeterministicFixedDecision

/-! The fixed-additive-error consumer of the same actual stored square.
The permitted estimator is extracted once, with its original numerical
interpretation. This does not assume a dyadic output presentation. -/
namespace CurrentAdditive.V40DeterministicETHEndpoint
noncomputable section
open Paper2 EthInapproximability.CurrentPaper EncodedCommunication
open EncodedETHSource EncodedETHSourceComposition Unit4Shell.T10Finite
open V39CurrentSourceJoin V39PermittedDeterministicExtraction V39FramedNumerical
open V39PermittedNumericalExtraction
open Workspace.Types.CommComplexity
open scoped Classical
set_option maxHeartbeats 3000000
set_option maxRecDepth 32768

def FixedSquareAccuracy (A : PermittedDeterministicEstimator) (u : ℝ) : Prop :=
  ∀ (m : ℕ) (f : Fin m → Fin m → Bool), 0 < m → (∃ e,m=2^e) →
    |A.value (A.output (AModel.matrixWord m m (MatrixMaterialization.rowMajor f)))-
      (Workspace.Types.CommComplexity.D f:ℝ)| ≤ u

theorem fixed_stored_accuracy (A : PermittedDeterministicEstimator) (u : ℝ)
    (hA : FixedSquareAccuracy A u) (R : V39GeneratedConstruction.StoredMatrix) :
    |A.value (A.output R.squareWord)-(Workspace.Types.CommComplexity.D R.entry:ℝ)|≤u := by
  simpa only [V39GeneratedConstruction.StoredMatrix.square_cost] using
    hA (SquarePadding.side R.rows R.cols) R.square (SquarePadding.side_pos _ _) R.square_side_power

variable (D : DinurReduction) (B : BOTReduction (booleanOccurrence D))

theorem fixed_source_classification (A : PermittedDeterministicEstimator) (u : ℝ)
    (hA : FixedSquareAccuracy A u) (k : ℕ) (hgap : 2*u<(k:ℝ)) (Φ : ValidFormula) :
    (extractedEstimator A).run (sourceRequest D B Φ k)=[decide (EncodedCNF.Satisfiable Φ.val)] := by
  let R:=ethRun D B Φ k
  have hv : ValidTable (ethWord D B Φ k) := valid_of_target (ethWord_target D B Φ k)
  have hacc : |(extractedEstimator A).value ((extractedEstimator A).output (ethWord D B Φ k))-
      (Workspace.Types.CommComplexity.D R.entry:ℝ)|≤u := by
    rw [extracted_value,extracted_output A _ hv]
    exact fixed_stored_accuracy A u hA R
  have hmid:=V39FramedNumerical.midpoint_outputs (extractedEstimator A) (ethWord D B Φ k)
    (Workspace.Types.CommComplexity.D R.entry) (ethThreshold D B Φ k) k u
    hgap hacc (extracted_comparison A D B Φ k)
  by_cases hs : EncodedCNF.Satisfiable Φ.val
  · simpa only [sourceRequest,hs,decide_true] using hmid.1 (ethRun_yes D B Φ k hs)
  · simpa only [sourceRequest,hs,decide_false] using hmid.2 (ethRun_no D B Φ k hs).ge

def fixedRound (u : ℝ) : ℕ := ⌈2*u⌉₊+1

theorem fixed_round_classification (A : PermittedDeterministicEstimator) (u : ℝ)
    (hA : FixedSquareAccuracy A u) (Φ : ValidFormula) :
    (extractedEstimator A).run (sourceRequest D B Φ (fixedRound u))=
      [decide (EncodedCNF.Satisfiable Φ.val)] :=
  fixed_source_classification D B A u hA _ (DeterministicFixedDecision.fixed_real_gap_choice u).2 Φ

theorem fixed_all_input_classification (A : PermittedDeterministicEstimator) (u : ℝ)
    (hA : FixedSquareAccuracy A u) (w : List Bool) :
    (extractedEstimator A).run
      (sourceRequest D B (V40DeterministicSourcePack.fixedFormula w) (fixedRound u))=
        [decide (w∈EncodedCNF.Language)] := by
  rw [fixed_round_classification D B A u hA]
  simp only [V40DeterministicSourcePack.fixed_front_sat_iff]

#print axioms fixed_source_classification
#print axioms fixed_all_input_classification
end
end CurrentAdditive.V40DeterministicETHEndpoint
