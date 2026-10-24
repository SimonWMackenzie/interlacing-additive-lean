import CurrentAdditive.V40DeterministicRequest
import CurrentAdditive.V40DeterministicSourceLaw

/-! Concrete retained-state request and actual permitted-estimator call.
The whole graph constructor is outside this tail; all its actual inputs
and transitions within the tail are already physical and uniformly charged. -/
namespace CurrentAdditive.V40DeterministicETHEndpoint
noncomputable section
open Paper2 EthInapproximability.CurrentPaper EncodedCommunication
open EncodedETHSource EncodedETHSourceComposition Unit4Shell.T10Finite
open V39GeneratedConstruction V39CurrentSourceJoin V39RuntimeETHNumerics
open V39PermittedDeterministicExtraction V39FramedNumerical PhysicalProducer
open scoped Classical
set_option maxHeartbeats 3000000
set_option maxRecDepth 32768
set_option synthInstance.maxSize 32768

def classifier (E : Estimator) : Producer where
  machine := E.machine
  result := E.run
  coefficient := E.clockCoefficient
  degree := E.clockDegree
  outputs := V39FramedNumerical.machine_outputs E

def classified (E : Estimator) := compose V40DeterministicRequest.request (classifier E)

theorem classified_result (E : Estimator) (L K : ℕ) (ctx : List Bool) (R : StoredMatrix) :
    (classified E).result (V40StoredEnvelope.input L K ctx R)=
      E.run (natField (2*V40StoredThreshold.thresholdNumber L K+K)++R.squareWord) := by
  change E.run (V40DeterministicRequest.request.result _)=_
  rw [V40DeterministicRequest.request_result]

theorem classified_outputs (E : Estimator) (L K : ℕ) (ctx : List Bool) (R : StoredMatrix) :
    (classified E).machine.OutputsWithin (V40StoredEnvelope.input L K ctx R)
      (E.run (natField (2*V40StoredThreshold.thresholdNumber L K+K)++R.squareWord))
      ((classified E).coefficient*((V40StoredEnvelope.input L K ctx R).length+1)^(classified E).degree) := by
  simpa only [classified_result] using (classified E).outputs (V40StoredEnvelope.input L K ctx R)

variable (D : DinurReduction) (B : BOTReduction (booleanOccurrence D))

def sourceLog (Φ : ValidFormula) := publicLogFrom (parameters D B) Φ.val.variables
  (t10Graph D B Φ).vertices (t10Graph D B Φ).edges.length
  (source_geometry D B Φ).1 (source_geometry D B Φ).2.1 (source_geometry D B Φ).2.2

def sourceEnvelope (Φ : ValidFormula) (K : ℕ) (ctx : List Bool) :=
  V40StoredEnvelope.input (sourceLog D B Φ) K ctx (ethRun D B Φ K)

theorem source_classified_outputs (amp C : ℕ) (hamp : 2^64≤amp) (hC : 1040≤C)
    (A : PermittedDeterministicEstimator) (cs T₀ : ℕ)
    (hA : GrowingSquareAccuracy A (errorCoefficient amp:ℝ) T₀) :
    ∃ M₀ : ℕ, ∀ Φ : ValidFormula,
      Φ.val.clauses.length≤cs*Φ.val.variables → M₀≤Φ.val.variables → ∀ ctx,
      (classified (extractedEstimator A)).machine.OutputsWithin
        (sourceEnvelope D B Φ (rounds amp Φ.val.variables) ctx)
        [decide (EncodedCNF.Satisfiable Φ.val)]
        ((classified (extractedEstimator A)).coefficient*
          ((sourceEnvelope D B Φ (rounds amp Φ.val.variables) ctx).length+1)^
            (classified (extractedEstimator A)).degree) := by
  obtain ⟨M₀,h⟩:=source_classification_all_large D B amp C hamp hC A cs T₀ hA
  refine ⟨M₀,?_⟩
  intro Φ hsp hN ctx
  have hr:=classified_outputs (extractedEstimator A) (sourceLog D B Φ)
    (rounds amp Φ.val.variables) ctx (ethRun D B Φ (rounds amp Φ.val.variables))
  have hb : V40StoredThreshold.thresholdNumber (sourceLog D B Φ) (rounds amp Φ.val.variables)=
      ethThreshold D B Φ (rounds amp Φ.val.variables) := rfl
  rw [hb] at hr
  change (classified (extractedEstimator A)).machine.OutputsWithin
    (sourceEnvelope D B Φ (rounds amp Φ.val.variables) ctx)
    ((extractedEstimator A).run (sourceRequest D B Φ (rounds amp Φ.val.variables))) _ at hr
  rw [h Φ hsp hN] at hr
  exact hr

#print axioms classified_outputs
#print axioms source_classified_outputs
end
end CurrentAdditive.V40DeterministicETHEndpoint
