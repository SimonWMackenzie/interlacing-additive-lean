import CurrentAdditive.V40DeterministicRoutedLaw
import CurrentAdditive.V40DeterministicFrontClock
import CurrentAdditive.V40DeterministicClockArithmetic
import CurrentAdditive.DeterministicSparseETHEventual

/-! CONDITIONAL INTERMEDIATE: the physical source request run parameter in
this module is pending concrete instantiation from the actual graph
constructor. No final class or ETH endpoint is asserted here. -/
namespace CurrentAdditive.V40DeterministicETHEndpoint
noncomputable section
open Paper2 V38Schedule EthInapproximability.CurrentPaper
open EncodedETHSource EncodedETHSourceComposition Unit4Shell.T10Finite
open V39CurrentSourceJoin V39RuntimeETHNumerics V39FramedNumerical
open V39PermittedDeterministicExtraction V40DeterministicSourcePack
open scoped Classical
set_option maxHeartbeats 4000000
set_option maxRecDepth 32768

variable (D : DinurReduction) (B : BOTReduction (booleanOccurrence D))

def sourceRequestClock (amp C : ℕ) (Φ : ValidFormula) (k : ℕ) :=
  (generatedN (sourceLog D B Φ))^(C*amp^k)

def sourcePipelineMachine (M : BitMachine.Machine) (E : Estimator)
    (amp cs cutoff : ℕ) (hcut : 1≤cutoff) :=
  BitMachineComposition.composition (sparseFront D B amp cs cutoff hcut).machine
    (BitMachineComposition.composition M E.machine)

def sourcePipelineTime (E : Estimator) (amp C cs cutoff : ℕ) (hcut : 1≤cutoff) (w : List Bool) :=
  let Φ:=sparseFormula cs cutoff hcut w
  let k:=rounds amp Φ.val.variables
  frontClock (sparseFront D B amp cs cutoff hcut) w+
    sourceRequestClock D B amp C Φ k+classifierClock E (sourceRequest D B Φ k)

theorem sourcePipeline_outputs (M : BitMachine.Machine) (amp C : ℕ)
    (hamp : 2^64≤amp) (hC : 1040≤C)
    (A : PermittedDeterministicEstimator) (cs T₀ : ℕ)
    (hA : GrowingSquareAccuracy A (errorCoefficient amp:ℝ) T₀)
    (cutoff : ℕ) (hcut : 1≤cutoff)
    (hmin : semanticCutoff D B amp C hamp hC A cs T₀ hA≤cutoff)
    (pendingSourceRun : ∀ (Φ : ValidFormula) (k : ℕ),
      M.OutputsWithin (graphInput (t10Graph D B Φ) Φ.val.variables k)
        (sourceRequest D B Φ k) (sourceRequestClock D B amp C Φ k))
    (w : List Bool) :
    (sourcePipelineMachine D B M (extractedEstimator A) amp cs cutoff hcut).OutputsWithin w
      [decide (EncodedCNF.Satisfiable (sparseFormula cs cutoff hcut w).val)]
      (sourcePipelineTime D B (extractedEstimator A) amp C cs cutoff hcut w) := by
  let Φ:=sparseFormula cs cutoff hcut w
  let k:=rounds amp Φ.val.variables
  have hf:=sparse_front_outputs D B amp cs cutoff hcut w
  have hm:=pendingSourceRun Φ k
  have he:=V39FramedNumerical.machine_outputs (extractedEstimator A) (sourceRequest D B Φ k)
  have hsem:=routed_classification D B amp C hamp hC A cs T₀ hA cutoff hmin w
  change (extractedEstimator A).run (sourceRequest D B Φ k)=[decide (EncodedCNF.Satisfiable Φ.val)] at hsem
  rw [hsem] at he
  have hrun:=BitMachineComposition.composition_outputsWithin _ _ hf
    (BitMachineComposition.composition_outputsWithin _ _ hm he)
  apply BitMachine.outputsWithin_mono _ hrun
  change _≤frontClock (sparseFront D B amp cs cutoff hcut) w+
    sourceRequestClock D B amp C Φ k+classifierClock (extractedEstimator A) (sourceRequest D B Φ k)
  unfold frontClock classifierClock
  rw [sparse_front_result]
  omega

def sourcePipelineAlgorithm (M : BitMachine.Machine) (amp C : ℕ)
    (hamp : 2^64≤amp) (hC : 1040≤C)
    (A : PermittedDeterministicEstimator) (cs T₀ : ℕ)
    (hA : GrowingSquareAccuracy A (errorCoefficient amp:ℝ) T₀)
    (cutoff : ℕ) (hcut : 1≤cutoff)
    (hmin : semanticCutoff D B amp C hamp hC A cs T₀ hA≤cutoff)
    (pendingSourceRun : ∀ (Φ : ValidFormula) (k : ℕ),
      M.OutputsWithin (graphInput (t10Graph D B Φ) Φ.val.variables k)
        (sourceRequest D B Φ k) (sourceRequestClock D B amp C Φ k)) :
    DeterministicSparseETH.Algorithm where
  machine:=sourcePipelineMachine D B M (extractedEstimator A) amp cs cutoff hcut
  answer w:=decide (EncodedCNF.Satisfiable (sparseFormula cs cutoff hcut w).val)
  time:=sourcePipelineTime D B (extractedEstimator A) amp C cs cutoff hcut
  run:=sourcePipeline_outputs D B M amp C hamp hC A cs T₀ hA cutoff hcut hmin pendingSourceRun

theorem sourcePipeline_correct (cs cutoff : ℕ) (hcut : 1≤cutoff) (Φ : ValidFormula)
    (hsp : Φ.val.clauses.length≤cs*Φ.val.variables) :
    decide (EncodedCNF.Satisfiable (sparseFormula cs cutoff hcut (EncodedCNF.encode Φ.val)).val)=true ↔
      EncodedCNF.Satisfiable Φ.val := by
  simp only [decide_eq_true_eq]
  exact routed_sat_iff cs cutoff hcut Φ hsp

#print axioms sourcePipeline_outputs
#print axioms sourcePipelineAlgorithm
#print axioms sourcePipeline_correct
end
end CurrentAdditive.V40DeterministicETHEndpoint
