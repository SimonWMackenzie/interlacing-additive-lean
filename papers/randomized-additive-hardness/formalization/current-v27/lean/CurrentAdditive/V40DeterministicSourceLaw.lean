import CurrentAdditive.V39RuntimeSourceETHNumerics
import CurrentAdditive.V40ActualSourceGap
import CurrentAdditive.V39PermittedFloorDeterministic

/-! Actual-source deterministic classification with one permitted estimator.
The runtime-aware constant precedes all inputs, and every statement uses
the same original-floor stored square word. No constructor run is assumed. -/
namespace CurrentAdditive.V40DeterministicETHEndpoint
noncomputable section
open Paper2 EthInapproximability.CurrentPaper EncodedCommunication
open EncodedETHSource EncodedETHSourceComposition Unit4Shell.T10Finite
open V39GeneratedConstruction V39CurrentSourceJoin V39RuntimeETHNumerics
open V39PermittedDeterministicExtraction V39FramedNumerical
open V39PermittedNumericalExtraction
open scoped Classical
set_option maxHeartbeats 4000000
set_option maxRecDepth 32768
set_option synthInstance.maxSize 32768

def GrowingSquareAccuracy (A : PermittedDeterministicEstimator) (c : ℝ) (T₀ : ℕ) : Prop :=
  ∀ (m : ℕ) (f : Fin m → Fin m → Bool), 0 < m → (∃ e,m=2^e) → T₀ ≤ m^2 →
    |A.value (A.output (AModel.matrixWord m m (MatrixMaterialization.rowMajor f)))-
      (Workspace.Types.CommComplexity.D f:ℝ)| ≤ c*Real.logb 2 (Real.logb 2 (m^2:ℕ))

def extractedEstimator (A : PermittedDeterministicEstimator) : Estimator :=
  Classical.choose (V39PermittedFloorDeterministic.extract_all_floor_constructors A)

theorem extracted_value (A : PermittedDeterministicEstimator) :
    (extractedEstimator A).value=A.value :=
  (Classical.choose_spec (V39PermittedFloorDeterministic.extract_all_floor_constructors A)).1

theorem extracted_output (A : PermittedDeterministicEstimator) (word : List Bool)
    (hv : ValidTable word) :
    (extractedEstimator A).output word=A.output word :=
  (Classical.choose_spec (V39PermittedFloorDeterministic.extract_all_floor_constructors A)).2.1 word hv

theorem extracted_comparison (A : PermittedDeterministicEstimator)
    (D : DinurReduction) (B : BOTReduction (booleanOccurrence D)) (Φ : ValidFormula) (k : ℕ) :
    ComparisonAt (extractedEstimator A) (ethWord D B Φ k) (2*ethThreshold D B Φ k+k) :=
  (Classical.choose_spec (V39PermittedFloorDeterministic.extract_all_floor_constructors A)).2.2
    (V39PermittedFloorDeterministic.sourceInput D B Φ k)

theorem stored_accuracy (A : PermittedDeterministicEstimator) (c : ℝ) (T₀ : ℕ)
    (hA : GrowingSquareAccuracy A c T₀) (R : StoredMatrix)
    (hT : T₀≤V39ActualETHNumerics.entryCount R) :
    |A.value (A.output R.squareWord)-(Workspace.Types.CommComplexity.D R.entry:ℝ)| ≤
      c*Real.logb 2 (Real.logb 2 (V39ActualETHNumerics.entryCount R)) := by
  have h:=hA (SquarePadding.side R.rows R.cols) R.square (SquarePadding.side_pos _ _)
    R.square_side_power hT
  simpa only [StoredMatrix.square_cost] using h

variable (D : DinurReduction) (B : BOTReduction (booleanOccurrence D))

def sourceRequest (Φ : ValidFormula) (k : ℕ) : List Bool :=
  natField (2*ethThreshold D B Φ k+k)++ethWord D B Φ k

/-- The comparison and raw-output identity are derived internally from the
permitted class. The two gap cases use exactly the actual source square. -/
theorem source_classification_all_large (amp C : ℕ) (hamp : 2^64≤amp) (hC : 1040≤C)
    (A : PermittedDeterministicEstimator) (cs T₀ : ℕ)
    (hA : GrowingSquareAccuracy A (errorCoefficient amp:ℝ) T₀) :
    ∃ M₀ : ℕ, ∀ Φ : ValidFormula,
      Φ.val.clauses.length≤cs*Φ.val.variables → M₀≤Φ.val.variables →
      (extractedEstimator A).run (sourceRequest D B Φ (rounds amp Φ.val.variables))=
        [decide (EncodedCNF.Satisfiable Φ.val)] := by
  obtain ⟨M₀,hnum⟩ := runtime_source_eth_numerics D B amp C hamp hC cs T₀
  refine ⟨M₀,?_⟩
  intro Φ hsp hN
  obtain ⟨hc,hk,hsqrt,hT,hgap,hsize⟩ := hnum Φ hsp hN
  let k:=rounds amp Φ.val.variables
  let R:=ethRun D B Φ k
  have hv : ValidTable (ethWord D B Φ k) :=
    valid_of_target (ethWord_target D B Φ k)
  have hacc : |(extractedEstimator A).value ((extractedEstimator A).output (ethWord D B Φ k))-
      (Workspace.Types.CommComplexity.D R.entry:ℝ)| ≤
      (errorCoefficient amp:ℝ)*Real.logb 2 (Real.logb 2 (V39ActualETHNumerics.entryCount R)) := by
    rw [extracted_value,extracted_output A _ hv]
    exact stored_accuracy A _ T₀ hA R hT
  have hmid:=V39FramedNumerical.midpoint_outputs (extractedEstimator A) (ethWord D B Φ k)
    (Workspace.Types.CommComplexity.D R.entry) (ethThreshold D B Φ k) k
    ((errorCoefficient amp:ℝ)*Real.logb 2 (Real.logb 2 (V39ActualETHNumerics.entryCount R)))
    (by simpa only [mul_assoc] using hgap) hacc (extracted_comparison A D B Φ k)
  by_cases hs : EncodedCNF.Satisfiable Φ.val
  · simpa only [sourceRequest,hs,decide_true] using hmid.1 (ethRun_yes D B Φ k hs)
  · have hn : ethThreshold D B Φ k+k≤Workspace.Types.CommComplexity.D R.entry :=
      (ethRun_no D B Φ k hs).ge
    simpa only [sourceRequest,hs,decide_false] using hmid.2 hn

/-- The actual fixed zero-tape classifier already executes the preceding
same-word decision. Only the missing whole constructor is outside this lemma. -/
theorem source_classifier_runs_all_large (amp C : ℕ) (hamp : 2^64≤amp) (hC : 1040≤C)
    (A : PermittedDeterministicEstimator) (cs T₀ : ℕ)
    (hA : GrowingSquareAccuracy A (errorCoefficient amp:ℝ) T₀) :
    ∃ M₀ : ℕ, ∀ Φ : ValidFormula,
      Φ.val.clauses.length≤cs*Φ.val.variables → M₀≤Φ.val.variables →
      (extractedEstimator A).machine.OutputsWithin
        (sourceRequest D B Φ (rounds amp Φ.val.variables))
        [decide (EncodedCNF.Satisfiable Φ.val)]
        ((extractedEstimator A).clockCoefficient*
          ((sourceRequest D B Φ (rounds amp Φ.val.variables)).length+1)^
            (extractedEstimator A).clockDegree) := by
  obtain ⟨M₀,h⟩:=source_classification_all_large D B amp C hamp hC A cs T₀ hA
  refine ⟨M₀,?_⟩
  intro Φ hsp hN
  have hr:=V39FramedNumerical.machine_outputs (extractedEstimator A)
    (sourceRequest D B Φ (rounds amp Φ.val.variables))
  rw [h Φ hsp hN] at hr
  exact hr

#print axioms source_classification_all_large
#print axioms source_classifier_runs_all_large
end
end CurrentAdditive.V40DeterministicETHEndpoint
