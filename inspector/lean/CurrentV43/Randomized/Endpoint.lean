import CurrentV43.Randomized.ConcreteLaw
import CurrentV43.Randomized.Runtime

/-! v43 Corollary 1.4: a permitted polynomial-time estimator yields one
actual bounded-error sparse 3-SAT algorithm for every 8c<alpha<1. -/
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
include D B

/-- v43 Corollary 1.4 on dyadic square tables. The conclusion quantifies
over every exponent strictly above 8c, returns the actual all-input fair-bit
machine, and pays its carrier printer, fair bits, framing and every run.
The only mathematical interfaces are the named source reductions and the
ordinary accuracy premise for the permitted polynomial-time estimator. -/
theorem quantitative_square_algorithm (A : PermittedEstimator) (T₀ : ℕ)
    (c : ℝ) (hc0 : 0 ≤ c) (hc : c < 1/8) (hA : GrowingSquareAccuracy A c T₀) :
    ∀ α : ℝ, 8*c < α → α < 1 → ∀ cs : ℕ,
    ∃ M : FairBitAlgorithm.Algorithm,
      (∀ Φ : ValidFormula, Φ.val.clauses.length ≤ cs*Φ.val.variables →
        (EncodedCNF.Satisfiable Φ.val → (2:ℝ)/3 ≤ M.prob (EncodedCNF.encode Φ.val) (· = [true])) ∧
        (¬EncodedCNF.Satisfiable Φ.val → M.prob (EncodedCNF.encode Φ.val) (· = [true]) ≤ (1:ℝ)/3)) ∧
      ∃ K N₀ : ℕ, ∀ Φ : ValidFormula,
        Φ.val.clauses.length ≤ cs*Φ.val.variables → N₀ ≤ Φ.val.variables →
        M.totalTime (EncodedCNF.encode Φ.val) ≤ ⌈(2:ℝ)^((K:ℝ)*(Φ.val.variables:ℝ)^α)⌉₊ := by
  intro α hcα hα1 cs
  obtain ⟨a,b,ha,hab,hcβ,hβα⟩ := exists_rational_rate c α hc0 hcα hα1
  have hb : 0 < b := lt_trans ha hab
  have hβ1 : (a:ℝ)/(b:ℝ) ≤ 1 := by linarith
  obtain ⟨cutoff,hcutoff,hsource,hcorrect⟩ :=
    algorithm_correctness D B A a b ha hb hβ1 cs T₀ c hc0 hcβ hA
  refine ⟨algorithm D B (extractedEstimator A) a b cs cutoff hcutoff hsource,hcorrect,?_⟩
  exact algorithm_power_time D B (extractedEstimator A) a b ha hb α hβα.le hβ1 cs cutoff hcutoff hsource

/-- The unrestricted explicit-table premise implies the same algorithm;
the proof actually needs accuracy only on square tables of dyadic side. -/
theorem quantitative_algorithm (A : PermittedEstimator) (T₀ : ℕ)
    (c : ℝ) (hc0 : 0 ≤ c) (hc : c < 1/8) (hA : GrowingAccuracy A c T₀) :
    ∀ α : ℝ, 8*c < α → α < 1 → ∀ cs : ℕ,
    ∃ M : FairBitAlgorithm.Algorithm,
      (∀ Φ : ValidFormula, Φ.val.clauses.length ≤ cs*Φ.val.variables →
        (EncodedCNF.Satisfiable Φ.val → (2:ℝ)/3 ≤ M.prob (EncodedCNF.encode Φ.val) (· = [true])) ∧
        (¬EncodedCNF.Satisfiable Φ.val → M.prob (EncodedCNF.encode Φ.val) (· = [true]) ≤ (1:ℝ)/3)) ∧
      ∃ K N₀ : ℕ, ∀ Φ : ValidFormula,
        Φ.val.clauses.length ≤ cs*Φ.val.variables → N₀ ≤ Φ.val.variables →
        M.totalTime (EncodedCNF.encode Φ.val) ≤ ⌈(2:ℝ)^((K:ℝ)*(Φ.val.variables:ℝ)^α)⌉₊ :=
  quantitative_square_algorithm D B A T₀ c hc0 hc
    (growingSquareAccuracy_of_growingAccuracy A c T₀ hA)

#print axioms quantitative_square_algorithm
#print axioms quantitative_algorithm
end
end CurrentV43.RandomizedRate
