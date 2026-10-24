import CurrentAdditive.V40DeterministicStoredClassifier
import CurrentAdditive.V40DeterministicSourcePack

/-! Fixed finite routing for the current deterministic estimator consumer.
The sparse guard is used for ETH only. It preserves every sparse original,
including the formulas handled by its charged finite control table. -/
namespace CurrentAdditive.V40DeterministicETHEndpoint
noncomputable section
open Paper2 EthInapproximability.CurrentPaper EncodedCommunication
open EncodedETHSource EncodedETHSourceComposition Unit4Shell.T10Finite
open V39CurrentSourceJoin V39RuntimeETHNumerics V39PermittedDeterministicExtraction
open V40DeterministicSourcePack
open scoped Classical
set_option maxHeartbeats 2000000
set_option maxRecDepth 32768

variable (D : DinurReduction) (B : BOTReduction (booleanOccurrence D))

def semanticCutoff (amp C : ℕ) (hamp : 2^64≤amp) (hC : 1040≤C)
    (A : PermittedDeterministicEstimator) (cs T₀ : ℕ)
    (hA : GrowingSquareAccuracy A (errorCoefficient amp:ℝ) T₀) :=
  max 1 (Classical.choose
    (source_classification_all_large D B amp C hamp hC A (cs+2) T₀ hA))

theorem routed_sparse (cs cutoff : ℕ) (hcut : 1≤cutoff) (w : List Bool) :
    (sparseFormula cs cutoff hcut w).val.clauses.length ≤
      (cs+2)*(sparseFormula cs cutoff hcut w).val.variables := by
  exact AEth4.routed4_sparse (cs+2) cutoff (by nlinarith) w

theorem routed_sat_iff (cs cutoff : ℕ) (hcut : 1≤cutoff) (Φ : ValidFormula)
    (hsp : Φ.val.clauses.length≤cs*Φ.val.variables) :
    EncodedCNF.Satisfiable (sparseFormula cs cutoff hcut (EncodedCNF.encode Φ.val)).val ↔
      EncodedCNF.Satisfiable Φ.val := by
  have hsp' : Φ.val.clauses.length≤(cs+2)*Φ.val.variables := by nlinarith
  have h:=AEth4.routed4_sat_iff (cs+2) hcut Φ.val Φ.property hsp'
  exact h.trans (EncodedCNF.encode_mem_iff Φ.val Φ.property)

theorem routed_original (cs cutoff : ℕ) (hcut : 1≤cutoff) (Φ : ValidFormula)
    (hsp : Φ.val.clauses.length≤cs*Φ.val.variables) (hlarge : cutoff≤Φ.val.variables) :
    sparseFormula cs cutoff hcut (EncodedCNF.encode Φ.val)=Φ := by
  apply Subtype.ext
  exact AEth4.routed4_encode (cs+2) cutoff Φ.val Φ.property (by nlinarith) hlarge

theorem routed_classification (amp C : ℕ) (hamp : 2^64≤amp) (hC : 1040≤C)
    (A : PermittedDeterministicEstimator) (cs T₀ : ℕ)
    (hA : GrowingSquareAccuracy A (errorCoefficient amp:ℝ) T₀)
    (cutoff : ℕ) (hmin : semanticCutoff D B amp C hamp hC A cs T₀ hA≤cutoff)
    (w : List Bool) :
    let hcut : 1≤cutoff := (le_max_left _ _).trans hmin
    let Φ:=sparseFormula cs cutoff hcut w
    (extractedEstimator A).run (sourceRequest D B Φ (rounds amp Φ.val.variables))=
      [decide (EncodedCNF.Satisfiable Φ.val)] := by
  let hcut : 1≤cutoff := (le_max_left _ _).trans hmin
  apply Classical.choose_spec
    (source_classification_all_large D B amp C hamp hC A (cs+2) T₀ hA)
  · exact routed_sparse cs cutoff hcut w
  · exact ((le_max_right _ _).trans hmin).trans (AEth4.routed4_variables (cs+2) cutoff w)

theorem sparse_front_large (amp cs cutoff : ℕ) (hcut : 1≤cutoff) (Φ : ValidFormula)
    (hsp : Φ.val.clauses.length≤cs*Φ.val.variables) (hlarge : cutoff≤Φ.val.variables) :
    (sparseFront D B amp cs cutoff hcut).result (EncodedCNF.encode Φ.val)=
      graphInput (t10Graph D B Φ) Φ.val.variables (rounds amp Φ.val.variables) := by
  rw [sparse_front_result,routed_original cs cutoff hcut Φ hsp hlarge]

#print axioms routed_classification
#print axioms sparse_front_large
end
end CurrentAdditive.V40DeterministicETHEndpoint
