import CurrentAdditive.V40RandomizedMachineLaw
import CurrentAdditive.V40RandomizedMachineClock
import CurrentAdditive.V40RandomizedEstimatorDomain
import CurrentAdditive.V40EffectiveTapePackage

/-! The actual permitted estimator yields one all-input effective-tape
machine at each sparse source density. This closes the current c<1/8
class contradiction using the same printed table, tape law and paid clock. -/
namespace CurrentAdditive.V40RandomizedETHEndpoint
noncomputable section
open Paper2 EthInapproximability.CurrentPaper
open EncodedETHSource EncodedETHSourceComposition EncodedComplexity
open Unit4Shell.T10Finite Unit4Shell.Asymptotics
open V38Schedule V39PublicSchedule V39ActualOutputMajority
open V39PermittedNumericalExtraction
set_option maxHeartbeats 4000000
set_option maxRecDepth 32768
set_option synthInstance.maxSize 32768

variable (D : DinurReduction) (B : BOTReduction (booleanOccurrence D))
include D B

/-- A single fixed actual machine for all raw formula words, with a computed
length-only tape carrier, every-tape run and arbitrary unused suffix law. -/
def actualAlgorithm (C : SelectedTape.Algorithm) (cs cutoff : ℕ) (hcut : 1 ≤ cutoff)
    (hmin : V40SourceClassifier.minimum D B C cs ≤ cutoff) : AEth2.ETape.Algorithm :=
  withSourceCarrier cutoff (classifierBlockExponent C)
    (V40SourceClassifier.machine D B C cs cutoff hcut)
    (V40SourceClassifier.time D B C cs cutoff hcut)
    (V40SourceClassifier.output D B C cs cutoff hcut hmin)
    (V40SourceClassifier.runs_carrier D B C cs cutoff hcut hmin)
    (V40SourceClassifier.extend D B C cs cutoff hcut hmin)

theorem actualAlgorithm_probability (E : ActualEstimator) (cs cutoff : ℕ) (hcut : 1 ≤ cutoff)
    (hmin : V40SourceClassifier.minimum D B E.classifier cs ≤ cutoff) (w : List Bool) :
    (actualAlgorithm D B E.classifier cs cutoff hcut hmin).prob w (·=[true]) =
    (sourceLaw D B E (routedSource cs cutoff hcut w)).prob
      (fun z => sourceAccepts D B (routedSource cs cutoff hcut w)
        (V40SourceClassifier.tests D B E.classifier cs cutoff hcut hmin w) E z.1 z.2) := by
  exact machine_probability D B E cs cutoff hcut hmin w

/-- Ordinary growing-error accuracy supplies an actual bounded-error sparse
SAT decider. Only the stated sparse language is the correctness promise;
the underlying fixed program runs on every raw input and prescribed tape. -/
theorem permitted_estimator_sparse_decider (A : PermittedEstimator)
    (T₀ : ℕ) (c : ℝ) (hc0 : 0 ≤ c) (hc : c<1/8)
    (hA : GrowingSquareAccuracy A c T₀) (cs : ℕ) :
    ∃ M : AEth2.ETape.Algorithm, AEth2.SparseDeciderR20 cs M := by
  let E := extractedEstimator A
  obtain ⟨Ns,hNs,hsource,hcorrect⟩ := permitted_routed_correctness D B A cs T₀ c hc0 hc hA
  let cutoff := max Ns (V40SourceClassifier.minimum D B E.classifier cs)
  have hcut : 1 ≤ cutoff := hNs.trans (le_max_left _ _)
  have hmin : V40SourceClassifier.minimum D B E.classifier cs ≤ cutoff := le_max_right _ _
  refine ⟨actualAlgorithm D B E.classifier cs cutoff hcut hmin,?_,?_⟩
  · intro input hwf hsp
    obtain ⟨Φ,rfl⟩ := hwf
    rw [ADecider.cnfClauseCount_encode,ADecider.variableCount_encode] at hsp
    have hp := actualAlgorithm_probability D B E cs cutoff hcut hmin (EncodedCNF.encode Φ.val)
    have h := hcorrect cutoff (le_max_left _ _) hcut Φ hsp
      (V40SourceClassifier.tests D B E.classifier cs cutoff hcut hmin (EncodedCNF.encode Φ.val))
    rw [hp]
    exact ⟨fun hy => by have hyes := h.1 hy; linarith,
      fun hn => by have hno := h.2 hn; linarith⟩
  · intro ε hε
    obtain ⟨K,d,N₀,h⟩ := actual_time_sparse D B E.classifier cs cutoff hcut ε hε
    refine ⟨K,d,N₀,?_⟩
    intro input hwf hsp hN
    obtain ⟨Φ,rfl⟩ := hwf
    rw [ADecider.cnfClauseCount_encode,ADecider.variableCount_encode] at hsp
    rw [ADecider.variableCount_encode] at hN ⊢
    exact h Φ hsp hN

/-- Every 0≤c<1/8 is excluded already on square explicit Boolean tables
whose side is a power of two. No constructor, comparison, event-law or
running-time conclusion is an input to this class theorem. -/
theorem quantitative_square_class (c : ℝ) (hc0 : 0 ≤ c) (hc : c<1/8)
    (hETH : AEth2.RandomizedSparseETH_R20) :
    ¬ ∃ A : PermittedEstimator, ∃ T₀ : ℕ, GrowingSquareAccuracy A c T₀ := by
  rintro ⟨A,T₀,hA⟩
  exact (AEth2.not_R20_iff.2 (fun cs =>
    permitted_estimator_sparse_decider D B A T₀ c hc0 hc hA cs)) hETH

/-- The unrestricted explicit-table consequence uses the same actual
matrix-only estimator input and the same sharp growing-error constant. -/
theorem quantitative_class (c : ℝ) (hc0 : 0 ≤ c) (hc : c<1/8)
    (hETH : AEth2.RandomizedSparseETH_R20) :
    ¬ ∃ A : PermittedEstimator, ∃ T₀ : ℕ, GrowingAccuracy A c T₀ := by
  rintro ⟨A,T₀,hA⟩
  exact quantitative_square_class D B c hc0 hc hETH
    ⟨A,T₀,growingSquareAccuracy_of_growingAccuracy A c T₀ hA⟩

#print axioms actualAlgorithm
#print axioms actualAlgorithm_probability
#print axioms permitted_estimator_sparse_decider
#print axioms quantitative_square_class
#print axioms quantitative_class
end
end CurrentAdditive.V40RandomizedETHEndpoint
