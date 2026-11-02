import CurrentV43.Randomized.Concrete
import CurrentV43.Randomized.AlgorithmLaw
namespace CurrentV43.RandomizedRate
noncomputable section
open CurrentAdditive ParametricSource
open Paper2 EthInapproximability.CurrentPaper
open EncodedETHSource EncodedETHSourceComposition
open Unit4Shell.T10Finite Unit4Shell.Asymptotics
open V42RandomizedETHEndpoint V39PermittedNumericalExtraction V39ActualOutputMajority
open CurrentAdditive.V43RandomizedRate
set_option maxHeartbeats 4000000
set_option maxRecDepth 32768
set_option synthInstance.maxSize 32768
variable (D : DinurReduction) (B : BOTReduction (booleanOccurrence D))
theorem algorithm_probability (E : ActualEstimator) (a b cs cutoff : ℕ) (hcutoff : 1 ≤ cutoff)
    (hsource : V42SourceGeometry.originalCutoff D B (cs+2) ≤ cutoff) (w : List Bool) :
    (algorithm D B E a b cs cutoff hcutoff hsource).prob w (· = [true]) =
    let Φ := routedSource cs cutoff hcutoff w
    (sourceLaw D B (iterations a b Φ.val.variables) E Φ).prob
      (fun z => sourceAccepts D B (iterations a b Φ.val.variables) Φ
        (routedTests D B cs cutoff hcutoff hsource w) E z.1 z.2) :=
  routedAlgorithm_probability D B E (rationalSchedule a b) (resource D B E.classifier a b)
    cs cutoff hcutoff hsource _ w

/-- Actual bounded-error correctness on every sparse formula, including
all sizes below the asymptotic cutoff. No completed-decider premise occurs. -/
theorem algorithm_correctness (A : PermittedEstimator) (a b : ℕ)
    (ha : 0 < a) (hb : 0 < b) (hβ1 : (a:ℝ)/(b:ℝ) ≤ 1)
    (cs T₀ : ℕ) (c : ℝ) (hc0 : 0 ≤ c) (hcβ : 8*c < (a:ℝ)/(b:ℝ))
    (hA : GrowingSquareAccuracy A c T₀) :
    ∃ cutoff : ℕ, ∃ hcutoff : 1 ≤ cutoff,
      ∃ hsource : V42SourceGeometry.originalCutoff D B (cs+2) ≤ cutoff,
      ∀ Φ : ValidFormula, Φ.val.clauses.length ≤ cs*Φ.val.variables →
      (EncodedCNF.Satisfiable Φ.val → (2:ℝ)/3 ≤
        (algorithm D B (extractedEstimator A) a b cs cutoff hcutoff hsource).prob
          (EncodedCNF.encode Φ.val) (· = [true])) ∧
      (¬EncodedCNF.Satisfiable Φ.val →
        (algorithm D B (extractedEstimator A) a b cs cutoff hcutoff hsource).prob
          (EncodedCNF.encode Φ.val) (· = [true]) ≤ (1:ℝ)/3) := by
  obtain ⟨cutoff,hcutoff,hsource,h⟩ :=
    routed_source_correctness D B a b ha hb hβ1 A cs T₀ c hc0 hcβ hA
  refine ⟨cutoff,hcutoff,hsource,?_⟩
  intro Φ hsp
  rw [algorithm_probability]
  have he := h cutoff le_rfl hcutoff Φ hsp
    (routedTests D B cs cutoff hcutoff hsource (EncodedCNF.encode Φ.val))
  have hlang : EncodedCNF.encode Φ.val ∈ EncodedCNF.Language ↔ EncodedCNF.Satisfiable Φ.val :=
    EncodedCNF.encode_mem_iff Φ.val Φ.property
  exact ⟨fun hy => by have hp := he.1 (hlang.2 hy); linarith,
    fun hn => by have hp := he.2 (fun hy => hn (hlang.1 hy)); linarith⟩

#print axioms algorithm_probability
#print axioms algorithm_correctness
end
end CurrentV43.RandomizedRate
