import CurrentAdditive.V42ActualSource
import CurrentAdditive.V42PermittedExtraction

/-! The shared permitted estimator is extracted over the actual v42
constructor family; this maps the approved CNF source into that family. -/
namespace CurrentAdditive.V42ActualSource
noncomputable section
open Paper2 EthInapproximability.CurrentPaper
open EncodedETHSource EncodedETHSourceComposition Unit4Shell.T10Finite
open V39PermittedDeterministicExtraction V39FramedNumerical
variable (D : DinurReduction) (B : BOTReduction (booleanOccurrence D))

def sourceInput (Φ : ValidFormula) (K : ℕ) : V42PermittedExtraction.Input where
  k := selected D B Φ
  hk := selected_two D B Φ
  n := (t10Graph D B Φ).vertices
  m := (t10Graph D B Φ).edges.length
  rep := V42RuntimePacket.repetition (selected D B Φ) (t10Graph D B Φ).edges.length
  hn := (V39CurrentSourceJoin.source_geometry D B Φ).1
  hwidth := V42GraphRuntime.selected_width B.degreeBound (k0 D B) (t10Graph D B Φ)
    (V39CurrentSourceJoin.source_geometry D B Φ).2.2 (k0_degree D B)
  edge := LiteralEdgeEncoder.edge (t10Graph D B Φ) (t10Graph_valid D B Φ)
  rounds := K

theorem source_comparison (A : PermittedDeterministicEstimator) (Φ : ValidFormula) (K : ℕ) :
    ComparisonAt (V42PermittedExtraction.estimator A) (word D B Φ K) (2*threshold D B Φ K+K) :=
  V42PermittedExtraction.estimator_comparison A (sourceInput D B Φ K)

#print axioms source_comparison
end
end CurrentAdditive.V42ActualSource
