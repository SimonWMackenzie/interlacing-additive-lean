import CurrentAdditive.V42ActualSourceGap
import CurrentAdditive.V42ActualSourceEstimator
import CurrentAdditive.V42SourcePhysical
import CurrentAdditive.DeterministicFixedDecision

/-! Literal fixed-gap CNF reduction and fixed additive-estimation endpoint
for the actual v42 generated matrix and physical request machine. -/
namespace CurrentAdditive.V42FixedEndpoints
noncomputable section
open Paper2 EthInapproximability.CurrentPaper EncodedCommunication EncodedComplexity
open EncodedETHSource EncodedETHSourceComposition Unit4Shell.T10Finite
open V39GeneratedConstruction V39PermittedDeterministicExtraction V39FramedNumerical
open V39PermittedNumericalExtraction Workspace.Types.CommComplexity
open scoped Classical
set_option maxHeartbeats 500000
set_option maxRecDepth 65536

variable (D : DinurReduction) (B : BOTReduction (booleanOccurrence D))


def instanceWord (K : ℕ) (w : List Bool) : Instance :=
  V42SourcePhysical.rectangle D B (V42SourcePhysical.fixedFormula w) K

theorem instance_valid (K : ℕ) (w : List Bool) : (instanceWord D B K w).Valid := by
  let R := V42ActualSource.run D B (V42SourcePhysical.fixedFormula w) K
  change 0<R.rows ∧ 0<R.cols ∧ (StoredWeightedState.cells R).length=R.rows*R.cols
  exact ⟨R.rows_pos,R.cols_pos,MatrixMaterialization.rowMajor_length R.entry⟩


theorem table_eq (K : ℕ) (w : List Bool) :
    ProtocolVerifier.tableGame (instanceWord D B K w).rows (instanceWord D B K w).cols
      (instanceWord D B K w).table=
      (V42ActualSource.run D B (V42SourcePhysical.fixedFormula w) K).entry := by
  funext i j
  simp only [instanceWord,V42SourcePhysical.rectangle,V42DeterministicRequest.rectangleInstance,
    StoredWeightedState.cells,ProtocolVerifier.tableGame,ProtocolVerifier.tableEntry,
    MatrixMaterialization.rowMajor_entry,Option.getD_some]


theorem threshold_eq (K : ℕ) (w : List Bool) :
    (instanceWord D B K w).threshold=V42ActualSource.threshold D B (V42SourcePhysical.fixedFormula w) K :=
  V42DeterministicRequest.generated_threshold _ _


theorem fixed_gap (K : ℕ) (w : List Bool) :
    (w∈EncodedCNF.Language → Workspace.Types.CommComplexity.D (ProtocolVerifier.tableGame
      (instanceWord D B K w).rows (instanceWord D B K w).cols (instanceWord D B K w).table)≤
        (instanceWord D B K w).threshold) ∧
    (w∉EncodedCNF.Language → Workspace.Types.CommComplexity.D (ProtocolVerifier.tableGame
      (instanceWord D B K w).rows (instanceWord D B K w).cols (instanceWord D B K w).table)=
        (instanceWord D B K w).threshold+K) := by
  rw [table_eq,threshold_eq]
  have hs:=V40DeterministicSourcePack.fixed_front_sat_iff w
  exact ⟨fun hy => V42ActualSource.run_yes D B _ K (hs.2 hy),
    fun hn => V42ActualSource.run_no D B _ K (fun hy => hn (hs.1 hy))⟩


private theorem encoded_membership (I : Instance) (hi : I.Valid) :
    encodeInstance I ∈ EncodedCommunication.Language ↔
      Workspace.Types.CommComplexity.D (ProtocolVerifier.tableGame I.rows I.cols I.table) ≤ I.threshold := by
  constructor
  · rintro ⟨J,hj,hcost⟩
    rw [decode_encode I hi] at hj
    cases Option.some.inj hj
    exact hcost
  · intro hc
    exact ⟨I,decode_encode I hi,hc⟩

include D B in
theorem fixed_gap_reduction (K : ℕ) (hK : 1≤K) :
    Reduces EncodedCNF.Language EncodedCommunication.Language := by
  refine ⟨fun w => encodeInstance (instanceWord D B K w),
    V42SourcePhysical.rectangleSource_polytime D B K,?_⟩
  intro w
  rw [encoded_membership (instanceWord D B K w) (instance_valid D B K w)]
  constructor
  · exact (fixed_gap D B K w).1
  · intro hcost
    by_contra hn
    have hno := (fixed_gap D B K w).2 hn
    omega


include D B in
theorem fixed_gap_npHard (hard : NPHard EncodedCNF.Language) :
    NPHard EncodedCommunication.Language :=
  ComplexityReductionClosure.npHard_of_reduces hard (fixed_gap_reduction D B 1 (by decide))

def FixedSquareAccuracy (A : PermittedDeterministicEstimator) (u : ℝ) : Prop :=
  ∀ (m : ℕ) (f : Fin m → Fin m → Bool), 0 < m → (∃ e,m=2^e) →
    |A.value (A.output (AModel.matrixWord m m (MatrixMaterialization.rowMajor f)))-
      (Workspace.Types.CommComplexity.D f:ℝ)| ≤ u

def FixedAccuracy (A : PermittedDeterministicEstimator) (u : ℝ) : Prop :=
  ∀ (r s : ℕ) (f : Fin r → Fin s → Bool), 0 < r → 0 < s →
    |A.value (A.output (AModel.matrixWord r s (MatrixMaterialization.rowMajor f)))-
      (Workspace.Types.CommComplexity.D f:ℝ)| ≤ u

theorem fixed_stored_accuracy (A : PermittedDeterministicEstimator) (u : ℝ)
    (hA : FixedSquareAccuracy A u) (R : StoredMatrix) :
    |A.value (A.output R.squareWord)-(Workspace.Types.CommComplexity.D R.entry:ℝ)|≤u := by
  simpa only [StoredMatrix.square_cost] using
    hA (SquarePadding.side R.rows R.cols) R.square (SquarePadding.side_pos _ _) R.square_side_power

theorem fixed_source_classification (A : PermittedDeterministicEstimator) (u : ℝ)
    (hA : FixedSquareAccuracy A u) (K : ℕ) (hgap : 2*u<(K:ℝ)) (Φ : ValidFormula) :
    (V42PermittedExtraction.estimator A).run (V42ActualSource.request D B Φ K)=
      [decide (EncodedCNF.Satisfiable Φ.val)] := by
  let E := V42PermittedExtraction.estimator A
  let R := V42ActualSource.run D B Φ K
  have hv : ValidTable (V42ActualSource.word D B Φ K) :=
    valid_of_target (V42ActualSource.word_target D B Φ K)
  have hacc : |E.value (E.output (V42ActualSource.word D B Φ K))-
      (Workspace.Types.CommComplexity.D R.entry:ℝ)|≤u := by
    rw [V42PermittedExtraction.estimator_value,V42PermittedExtraction.estimator_output A _ hv]
    exact fixed_stored_accuracy A u hA R
  have hmid := midpoint_outputs E (V42ActualSource.word D B Φ K)
    (Workspace.Types.CommComplexity.D R.entry) (V42ActualSource.threshold D B Φ K) K u
    hgap hacc (V42ActualSource.source_comparison D B A Φ K)
  by_cases hs : EncodedCNF.Satisfiable Φ.val
  · simpa only [V42ActualSource.request,hs,decide_true] using
      hmid.1 (V42ActualSource.run_yes D B Φ K hs)
  · simpa only [V42ActualSource.request,hs,decide_false] using
      hmid.2 (V42ActualSource.run_no D B Φ K hs).ge


def fixedRound (u : ℝ) : ℕ := ⌈2*u⌉₊+1

theorem fixed_all_input_classification (A : PermittedDeterministicEstimator) (u : ℝ)
    (hA : FixedSquareAccuracy A u) (w : List Bool) :
    (V42PermittedExtraction.estimator A).run
      (V42ActualSource.request D B (V42SourcePhysical.fixedFormula w) (fixedRound u))=
        [decide (w∈EncodedCNF.Language)] := by
  have h := fixed_source_classification D B A u hA (fixedRound u)
    (DeterministicFixedDecision.fixed_real_gap_choice u).2 (V42SourcePhysical.fixedFormula w)
  simpa only [V42SourcePhysical.fixedFormula,V40DeterministicSourcePack.fixed_front_sat_iff] using h

include D B in
theorem fixed_additive_square_inP (A : PermittedDeterministicEstimator) (u : ℝ)
    (_hu : 0≤u) (hA : FixedSquareAccuracy A u) : ComplexityReductionClosure.InP EncodedCNF.Language := by
  have hreq := V42SourcePhysical.requestSource_polytime D B (fixedRound u)
  have he : BitMachine.Polytime (V42PermittedExtraction.estimator A).run :=
    ⟨(V42PermittedExtraction.estimator A).machine,(V42PermittedExtraction.estimator A).clockCoefficient,
      (V42PermittedExtraction.estimator A).clockDegree,
      V39FramedNumerical.machine_outputs (V42PermittedExtraction.estimator A)⟩
  have hpoly := BitMachineComposition.polytime_comp hreq he
  change BitMachine.Polytime (fun w => (V42PermittedExtraction.estimator A).run
    (V42ActualSource.request D B (V42SourcePhysical.fixedFormula w) (fixedRound u))) at hpoly
  have heq : (fun w => (V42PermittedExtraction.estimator A).run
      (V42ActualSource.request D B (V42SourcePhysical.fixedFormula w) (fixedRound u)))=
      (fun w => [decide (w∈EncodedCNF.Language)]) := by
    funext w
    exact fixed_all_input_classification D B A u hA w
  rw [heq] at hpoly
  exact ⟨fun w=>decide (w∈EncodedCNF.Language),hpoly,fun w=>by simp⟩

include D B in
theorem fixed_additive_np_subset_p (hard : NPHard EncodedCNF.Language)
    (A : PermittedDeterministicEstimator) (u : ℝ) (hu : 0≤u) (hA : FixedAccuracy A u) :
    ∀ L, InNP L → ComplexityReductionClosure.InP L :=
  ComplexityReductionClosure.npHard_inP_implies_np_subset_p hard
    (fixed_additive_square_inP D B A u hu (fun m f hm _ => hA m m f hm hm))

#print axioms fixed_gap_reduction
#print axioms fixed_gap_npHard
#print axioms fixed_source_classification
#print axioms fixed_additive_square_inP
#print axioms fixed_additive_np_subset_p
end
end CurrentAdditive.V42FixedEndpoints
