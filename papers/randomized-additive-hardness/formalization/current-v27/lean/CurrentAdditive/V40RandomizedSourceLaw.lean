import CurrentAdditive.V40RandomizedETHCutoffs
import CurrentAdditive.V40RawRequestSemantics
import CurrentAdditive.V40PermittedRawClassifier
import CurrentAdditive.V39ActualSourceGeometry

/-! Growing-error semantics for the actual source graph and the actual raw
request. The source-only assumptions are discharged from Dinur/BOT, and the
single permitted estimator precedes every formula and construction tape. -/
namespace CurrentAdditive.V40RandomizedETHEndpoint
noncomputable section
open Paper2 EthInapproximability.CurrentPaper
open EncodedETHSource EncodedETHSourceComposition
open Unit4Shell.T10Finite Unit4Shell.Asymptotics
open V38Schedule V39PublicSchedule V39ActualOutputMajority
open V39PermittedNumericalExtraction
set_option maxHeartbeats 2000000
set_option maxRecDepth 16384
set_option synthInstance.maxSize 32768

/-- Ordinary approximation on every sufficiently large explicit square
Boolean table whose side is a power of two. -/
def GrowingSquareAccuracy (A : PermittedEstimator) (c : ℝ) (T₀ : ℕ) : Prop :=
  ∀ (m : ℕ) (f : Fin m → Fin m → Bool), 0 < m → (∃ e, m=2^e) → T₀ ≤ m^2 →
    (2:ℝ)/3 ≤ A.raw.prob (AModel.matrixWord m m (MatrixMaterialization.rowMajor f))
      (fun out => |A.value out-(Workspace.Types.CommComplexity.D f:ℝ)| ≤ growingError c (m^2))

theorem sampled_accuracy (A : PermittedEstimator) (c : ℝ) (T₀ L k : ℕ)
    (hA : GrowingSquareAccuracy A c T₀) (hT : T₀ ≤ sampleEntries L k) :
    ∀ f : V40JointEstimatorLaw.Table L k,
      (2:ℝ)/3 ≤ A.raw.prob (V40RandomPermittedFamily.matrixWord L k f)
        (fun out => |A.value out-(Workspace.Types.CommComplexity.D f:ℝ)| ≤ growingError c (sampleEntries L k)) := by
  obtain ⟨e,he,_⟩ := V39ActualRandomizedReduction.square_power_of_two L k
  intro f
  exact hA (sampleSide L k) f (V40RandomPermittedFamily.side_pos L k) ⟨e,he⟩ hT

variable (D : DinurReduction) (B : BOTReduction (booleanOccurrence D))

def sourceAccepts (Φ : ValidFormula)
    (ht : FullPublicTests (sourceGap D B) B.degreeBound (t10Graph D B Φ).vertices
      (t10Graph D B Φ).edges.length (Nat.clog 2 (t10Graph D B Φ).vertices))
    (E : ActualEstimator)
    (bits : V40PhysicalEstimatorConsumer.Bits (t10Graph D B Φ).vertices
      (Nat.clog 2 (t10Graph D B Φ).vertices) (kOf Φ.val.variables))
    (t : Fin (V40JointEstimatorLaw.classifierLength E
      (Nat.clog 2 (t10Graph D B Φ).vertices) (kOf Φ.val.variables)) → Bool) : Prop :=
  letI : NeZero (t10Graph D B Φ).vertices := ⟨Nat.ne_of_gt (t10_vertices_pos D B Φ)⟩
  V40RawRequestSemantics.accepts (t10Graph D B Φ) (t10Graph_valid D B Φ) (kOf Φ.val.variables)
    (fullConstant (sourceGap D B) B.degreeBound (t10Graph D B Φ).vertices (t10Graph D B Φ).edges.length)
    (sourceDeltaV (sourceGap D B) B.degreeBound (t10Graph D B Φ).vertices (t10Graph D B Φ).edges.length)
    (sourceZeta (sourceGap D B)) ht E bits t

def sourceLaw (E : ActualEstimator) (Φ : ValidFormula) :=
  V40PhysicalEstimatorConsumer.jointLaw E (t10Graph D B Φ).vertices
    (Nat.clog 2 (t10Graph D B Φ).vertices) (kOf Φ.val.variables)

/-- All graph promises, sharp error separation, and sufficiently large table
threshold are derived. No desired constructor, event law or execution is supplied. -/
theorem source_law_all_large (A : PermittedEstimator) (E : ActualEstimator)
    (hvalue : E.value=A.value)
    (hlaw : ∀ word, ValidTable word → ∀ P : List Bool → Prop,
      E.estimator.prob word P=A.raw.prob word P)
    (hcompare : ∀ L k (f : V40JointEstimatorLaw.Table L k),
      E.actualComparison (V40RandomPermittedFamily.matrixWord L k f)
        (V40RandomPermittedFamily.numerator L k))
    (cs T₀ : ℕ) (c : ℝ) (hc0 : 0 ≤ c) (hc : c < 1/8)
    (hA : GrowingSquareAccuracy A c T₀) :
    ∃ N₀ : ℕ, 1 ≤ N₀ ∧ ∀ Φ : ValidFormula,
      Φ.val.clauses.length ≤ cs*Φ.val.variables → N₀ ≤ Φ.val.variables →
      ∀ ht : FullPublicTests (sourceGap D B) B.degreeBound (t10Graph D B Φ).vertices
        (t10Graph D B Φ).edges.length (Nat.clog 2 (t10Graph D B Φ).vertices),
      (EncodedCNF.Satisfiable Φ.val →
        (99:ℝ)/100 ≤ (sourceLaw D B E Φ).prob (fun z => sourceAccepts D B Φ ht E z.1 z.2)) ∧
      (¬EncodedCNF.Satisfiable Φ.val →
        (sourceLaw D B E Φ).prob (fun z => sourceAccepts D B Φ ht E z.1 z.2) ≤ (3:ℝ)/100) := by
  obtain ⟨Nn,hNn,hnum⟩ := current_numeric_cutoff B.degreeBound (D.sizeExponent+2) T₀
    B.degreeBound_pos E.classifier c hc0 hc
  refine ⟨max Nn (V39SourceGeometry.originalCutoff D B cs),hNn.trans (le_max_left _ _),?_⟩
  intro Φ hsp hN ht
  obtain ⟨facts,hft,hsize⟩ := V39SourceGeometry.source_all_large D B cs Φ hsp
    ((le_max_right _ _).trans hN)
  have hpositive : 1 ≤ (t10Graph D B Φ).vertices := facts.vertices_pos
  obtain ⟨hk,hT,_,hu,hgap,_⟩ := hnum Φ.val.variables ((le_max_left _ _).trans hN)
    (t10Graph D B Φ).vertices hpositive facts.original_degree_bound hsize
  letI : NeZero (t10Graph D B Φ).vertices := ⟨Nat.ne_of_gt facts.vertices_pos⟩
  have haccurate := V40PhysicalEstimatorConsumer.permitted_accuracy (Nat.clog 2 (t10Graph D B Φ).vertices) A E hvalue hlaw
    (kOf Φ.val.variables) (growingError c (sampleEntries (Nat.clog 2 (t10Graph D B Φ).vertices) (kOf Φ.val.variables)))
    (sampled_accuracy A c T₀ _ _ hA hT)
  have hlarge : V39FullCutoff.sourceCutoff (sourceGap D B) B.degreeBound ≤ (t10Graph D B Φ).vertices :=
    facts.vertices_floor _ ((le_max_left _ _).trans ((le_max_right _ _).trans hN))
  have hs := DeterministicETHSourceBridge.fixed_graph_source D B Φ
  constructor
  · intro hy
    obtain ⟨colour,proper⟩ := hs.2.2.2.2.2.1 hy
    apply V40RawRequestSemantics.source_yes (t10Graph D B Φ) (t10Graph_valid D B Φ)
      (kOf Φ.val.variables) _ _ _ ht B.degreeBound B.degreeBound_pos
      (sourceGap D B) (source_gap_pos D B) facts.vertex_edge_bound facts.edge_degree_bound
      hlarge E _ hu hgap (hcompare _ _) haccurate colour
    rw [V39SourceGeometry.physical_edge_eq]
    exact proper
  · intro hn
    apply V40RawRequestSemantics.source_no (t10Graph D B Φ) (t10Graph_valid D B Φ)
      (kOf Φ.val.variables) _ _ _ ht B.degreeBound B.degreeBound_pos facts.degree
      (sourceGap D B) (source_gap_pos D B) facts.vertex_edge_bound facts.edge_degree_bound
      hlarge _ E _ hu hgap (hcompare _ _) haccurate
    rw [V39SourceGeometry.physical_edge_eq]
    exact hs.2.2.2.2.2.2 hn


/-- The one actual normalized estimator is chosen before the formula,
source graph, iteration count, construction randomness and density. -/
def extractedEstimator (A : PermittedEstimator) : ActualEstimator :=
  Classical.choose (V40PermittedRawClassifier.extract_all A)

theorem extractedEstimator_value (A : PermittedEstimator) :
    (extractedEstimator A).value=A.value := by
  obtain ⟨he,hv,hc,hl,ho,hp,hr⟩ := Classical.choose_spec (V40PermittedRawClassifier.extract_all A)
  exact hv

theorem extractedEstimator_comparison (A : PermittedEstimator) :
    ∀ L k (f : V40JointEstimatorLaw.Table L k),
      (extractedEstimator A).actualComparison (V40RandomPermittedFamily.matrixWord L k f)
        (V40RandomPermittedFamily.numerator L k) := by
  obtain ⟨he,hv,hc,hl,ho,hp,hr⟩ := Classical.choose_spec (V40PermittedRawClassifier.extract_all A)
  exact hc

theorem extractedEstimator_event_law (A : PermittedEstimator) :
    ∀ word, ValidTable word → ∀ P : List Bool → Prop,
      (extractedEstimator A).estimator.prob word P=A.raw.prob word P := by
  obtain ⟨he,hv,hc,hl,ho,hp,hr⟩ := Classical.choose_spec (V40PermittedRawClassifier.extract_all A)
  exact hp

/-- The same-request source probability theorem has only the manuscript's
ordinary permitted-estimator accuracy hypothesis. Comparison, output law,
source geometry and the event bound are all supplied by concrete owners. -/
theorem permitted_source_law_all_large (A : PermittedEstimator)
    (cs T₀ : ℕ) (c : ℝ) (hc0 : 0 ≤ c) (hc : c < 1/8)
    (hA : GrowingSquareAccuracy A c T₀) :
    ∃ N₀ : ℕ, 1 ≤ N₀ ∧ ∀ Φ : ValidFormula,
      Φ.val.clauses.length ≤ cs*Φ.val.variables → N₀ ≤ Φ.val.variables →
      ∀ ht : FullPublicTests (sourceGap D B) B.degreeBound (t10Graph D B Φ).vertices
        (t10Graph D B Φ).edges.length (Nat.clog 2 (t10Graph D B Φ).vertices),
      (EncodedCNF.Satisfiable Φ.val →
        (99:ℝ)/100 ≤ (sourceLaw D B (extractedEstimator A) Φ).prob
          (fun z => sourceAccepts D B Φ ht (extractedEstimator A) z.1 z.2)) ∧
      (¬EncodedCNF.Satisfiable Φ.val →
        (sourceLaw D B (extractedEstimator A) Φ).prob
          (fun z => sourceAccepts D B Φ ht (extractedEstimator A) z.1 z.2) ≤ (3:ℝ)/100) :=
  source_law_all_large D B A (extractedEstimator A) (extractedEstimator_value A)
    (extractedEstimator_event_law A) (extractedEstimator_comparison A) cs T₀ c hc0 hc hA

#print axioms permitted_source_law_all_large

#print axioms sampled_accuracy
#print axioms source_law_all_large
end
end CurrentAdditive.V40RandomizedETHEndpoint
