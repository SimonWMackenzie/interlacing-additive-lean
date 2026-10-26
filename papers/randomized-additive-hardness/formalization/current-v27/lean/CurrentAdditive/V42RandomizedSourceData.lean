import CurrentAdditive.V42RandomizedETHCutoffs
import CurrentAdditive.V42JointEstimatorLaw
import CurrentAdditive.V42RawRequestPacket
import CurrentAdditive.V42SourceGeometry

namespace CurrentAdditive.V42RandomizedETHEndpoint
noncomputable section
open Paper2 EthInapproximability.CurrentPaper
open EncodedETHSource EncodedETHSourceComposition
open Unit4Shell.T10Finite Unit4Shell.Asymptotics
open V42PublicSchedule V39ActualOutputMajority
open V39PermittedNumericalExtraction
set_option maxHeartbeats 3000000
set_option maxRecDepth 32768
set_option synthInstance.maxSize 32768

/-- The ordinary estimator premise, restricted only to positive square
explicit tables with power-of-two side length. -/
def GrowingSquareAccuracy (A : PermittedEstimator) (c : ℝ) (T₀ : ℕ) : Prop :=
  ∀ (m : ℕ) (f : Fin m → Fin m → Bool), 0 < m → (∃ e, m=2^e) → T₀ ≤ m^2 →
    (2:ℝ)/3 ≤ A.raw.prob (AModel.matrixWord m m (MatrixMaterialization.rowMajor f))
      (fun out => |A.value out-(Workspace.Types.CommComplexity.D f:ℝ)| ≤ growingError c (m^2))

def GrowingAccuracy (A : PermittedEstimator) (c : ℝ) (T₀ : ℕ) : Prop :=
  ∀ (r s : ℕ) (f : Fin r → Fin s → Bool), 0<r → 0<s → T₀ ≤ r*s →
    (2:ℝ)/3 ≤ A.raw.prob (AModel.matrixWord r s (MatrixMaterialization.rowMajor f))
      (fun out => |A.value out-(Workspace.Types.CommComplexity.D f:ℝ)| ≤ growingError c (r*s))

theorem growingSquareAccuracy_of_growingAccuracy (A : PermittedEstimator)
    (c : ℝ) (T₀ : ℕ) (hA : GrowingAccuracy A c T₀) :
    GrowingSquareAccuracy A c T₀ := by
  intro m f hm hp hT
  simpa only [pow_two] using hA m m f hm hm (by simpa only [pow_two] using hT)

theorem sampled_accuracy (A : PermittedEstimator) (c : ℝ) (T₀ L k : ℕ)
    (hA : GrowingSquareAccuracy A c T₀) (hT : T₀ ≤ sampleEntries L k) :
    ∀ f : V42JointEstimatorLaw.Table L k,
      (2:ℝ)/3 ≤ A.raw.prob (V42RandomPermittedFamily.matrixWord L k f)
        (fun out => |A.value out-(Workspace.Types.CommComplexity.D f:ℝ)| ≤ growingError c (sampleEntries L k)) := by
  intro f
  exact hA (sampleSide L k) f (V42RandomPermittedFamily.side_pos L k) ⟨_,rfl⟩ hT

/-- One fixed normalized estimator and one fixed amplified classifier are
selected before the formula, graph, iteration count, or construction tape. -/
def extractedEstimator (A : PermittedEstimator) : ActualEstimator :=
  Classical.choose (V42RandomPermittedFamily.extract_all A)

theorem extractedEstimator_value (A : PermittedEstimator) :
    (extractedEstimator A).value=A.value := by
  obtain ⟨he,hv,hc,hl,ho,hp⟩ := Classical.choose_spec (V42RandomPermittedFamily.extract_all A)
  exact hv

theorem extractedEstimator_comparison (A : PermittedEstimator) :
    ∀ L k (f : V42JointEstimatorLaw.Table L k),
      (extractedEstimator A).actualComparison (V42RandomPermittedFamily.matrixWord L k f)
        (V42RandomPermittedFamily.numerator L k) := by
  obtain ⟨he,hv,hc,hl,ho,hp⟩ := Classical.choose_spec (V42RandomPermittedFamily.extract_all A)
  exact hc

theorem extractedEstimator_event_law (A : PermittedEstimator) :
    ∀ word, ValidTable word → ∀ P : List Bool → Prop,
      (extractedEstimator A).estimator.prob word P=A.raw.prob word P := by
  obtain ⟨he,hv,hc,hl,ho,hp⟩ := Classical.choose_spec (V42RandomPermittedFamily.extract_all A)
  exact hp

theorem extracted_accuracy (A : PermittedEstimator) (c : ℝ) (T₀ L k : ℕ)
    (hA : GrowingSquareAccuracy A c T₀) (hT : T₀ ≤ sampleEntries L k) :
    ∀ f : V42JointEstimatorLaw.Table L k,
      (2:ℝ)/3 ≤ (extractedEstimator A).estimator.prob (V42RandomPermittedFamily.matrixWord L k f)
        (fun out => |(extractedEstimator A).value out-(Workspace.Types.CommComplexity.D f:ℝ)| ≤
          growingError c (sampleEntries L k)) := by
  intro f
  rw [extractedEstimator_value,extractedEstimator_event_law A _ (V42RandomPermittedFamily.valid_table L k f)]
  exact sampled_accuracy A c T₀ L k hA hT f

variable (D : DinurReduction) (B : BOTReduction (booleanOccurrence D))

def sourceAccepts (Φ : ValidFormula)
    (ht : V42RuntimeSchedule.FullTests
      (V38Schedule.fullConstant (sourceGap D B) B.degreeBound
        (t10Graph D B Φ).vertices (t10Graph D B Φ).edges.length)
      (Nat.clog 2 (t10Graph D B Φ).vertices) (t10Graph D B Φ).edges.length
      (V38Schedule.sourceDeltaV (sourceGap D B) B.degreeBound
        (t10Graph D B Φ).vertices (t10Graph D B Φ).edges.length)
      (V38Schedule.sourceZeta (sourceGap D B)))
    (E : ActualEstimator)
    (bits : RoundedDraw.BitBlocks (V42RawSamplerJoin.precision (t10Graph D B Φ).vertices (kOf Φ.val.variables))
      (V42RawSamplerJoin.reservation (t10Graph D B Φ).vertices (kOf Φ.val.variables)))
    (t : Fin (V42JointEstimatorLaw.classifierLength E
      (Nat.clog 2 (t10Graph D B Φ).vertices) (kOf Φ.val.variables)) → Bool) : Prop :=
  letI : NeZero (t10Graph D B Φ).vertices := ⟨(t10_vertices_pos D B Φ).ne'⟩
  E.classifier.output (V42RawRequestPacket.request (t10Graph D B Φ) (t10Graph_valid D B Φ)
    (kOf Φ.val.variables)
    (V38Schedule.fullConstant (sourceGap D B) B.degreeBound
      (t10Graph D B Φ).vertices (t10Graph D B Φ).edges.length)
    (V38Schedule.sourceDeltaV (sourceGap D B) B.degreeBound
      (t10Graph D B Φ).vertices (t10Graph D B Φ).edges.length)
    (V38Schedule.sourceZeta (sourceGap D B)) ht bits) (List.ofFn t)=[true]

def sourceLaw (E : ActualEstimator) (Φ : ValidFormula) :=
  V42JointEstimatorLaw.independentLaw
    (RoundedDraw.bitBlocksLaw (V42RawSamplerJoin.precision (t10Graph D B Φ).vertices (kOf Φ.val.variables))
      (V42RawSamplerJoin.reservation (t10Graph D B Φ).vertices (kOf Φ.val.variables)))
    E (Nat.clog 2 (t10Graph D B Φ).vertices) (kOf Φ.val.variables)

#print axioms extracted_accuracy
#print axioms sourceAccepts
#print axioms sourceLaw
end
end CurrentAdditive.V42RandomizedETHEndpoint
