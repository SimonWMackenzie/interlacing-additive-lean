import CurrentAdditive.V40DeterministicStoredClassifier
import CurrentAdditive.V39FloorHeaderBound

/-! Exact original-variable numerical envelopes for the pending physical
constructor composition. These inequalities do not infer a machine clock. -/
namespace CurrentAdditive.V40DeterministicETHEndpoint
noncomputable section
open Paper2 V38Schedule GeneratedCutoff EthInapproximability.CurrentPaper
open EncodedETHSource EncodedETHSourceComposition Unit4Shell.T10Finite
open V39CurrentSourceJoin V39RuntimeETHNumerics V39GeneratedConstruction
open V39ActualETHNumerics V39FramedNumerical
set_option maxHeartbeats 3000000
set_option maxRecDepth 32768

variable (D : DinurReduction) (B : BOTReduction (booleanOccurrence D))

theorem request_length (Φ : ValidFormula) (k : ℕ) :
    (sourceRequest D B Φ k).length+1≤64*((ethWord D B Φ k).length+1)^2 := by
  let R:=ethRun D B Φ k
  have hb:=publicGraphRunFrom_header_bounds (parameters D B) Φ.val.variables
    (source_geometry D B Φ).1 (source_geometry D B Φ).2.1 (source_geometry D B Φ).2.2
    (CanonicalEdgeTape.graphEdge (t10Graph D B Φ) (t10Graph_valid D B Φ)) k
  have ht:=entries_le_length R
  change entryCount R≤(ethWord D B Φ k).length at ht
  have hf:=EncodedGraph.natField_length_upper (2*ethThreshold D B Φ k+k)
  change (sourceRequest D B Φ k).length+1≤_
  simp only [sourceRequest,List.length_append]
  change k≤entryCount R ∧ ethThreshold D B Φ k≤15*(entryCount R)^2 ∧
    2*ethThreshold D B Φ k+k≤31*(entryCount R)^2 at hb
  have hsq:=Nat.pow_le_pow_left ht 2
  nlinarith

def classifierClock (E : Estimator) (request : List Bool) :=
  2*request.length+2+E.clockCoefficient*(request.length+1)^E.clockDegree

theorem classifierClock_polynomial (E : Estimator) (request : List Bool) :
    classifierClock E request≤(E.clockCoefficient+2)*(request.length+1)^(E.clockDegree+1) := by
  have hbase : 1≤request.length+1 := by omega
  have hlin : request.length+1≤(request.length+1)^(E.clockDegree+1) :=
    Nat.le_self_pow (by omega) _
  have hpow : (request.length+1)^E.clockDegree≤(request.length+1)^(E.clockDegree+1) :=
    Nat.pow_le_pow_right hbase (by omega)
  have hmul:=Nat.mul_le_mul_left E.clockCoefficient hpow
  dsimp [classifierClock]
  nlinarith

theorem classifierClock_from_word (E : Estimator) (Φ : ValidFormula) (k Q : ℕ)
    (hQ : 1≤Q) (hword : (ethWord D B Φ k).length≤Q) :
    classifierClock E (sourceRequest D B Φ k)≤
      ((E.clockCoefficient+2)*256^(E.clockDegree+1))*Q^(2*(E.clockDegree+1)) := by
  have hr:=request_length D B Φ k
  have hw : (ethWord D B Φ k).length+1≤2*Q := by omega
  have hp:=Nat.pow_le_pow_left hw 2
  have hc : (sourceRequest D B Φ k).length+1≤256*Q^2 := by nlinarith
  calc
    classifierClock E (sourceRequest D B Φ k)
      ≤(E.clockCoefficient+2)*((sourceRequest D B Φ k).length+1)^(E.clockDegree+1) :=
        classifierClock_polynomial E _
    _ ≤(E.clockCoefficient+2)*(256*Q^2)^(E.clockDegree+1) :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hc _)
    _ = _ := by rw [mul_pow,←pow_mul]; ring

theorem source_scale_envelope (amp C : ℕ) (cs : ℕ) :
    ∃ M₀ : ℕ, ∀ Φ : ValidFormula,
      Φ.val.clauses.length≤cs*Φ.val.variables → M₀≤Φ.val.variables →
      (generatedN (sourceLog D B Φ))^(C*amp^(rounds amp Φ.val.variables))≤
        DeterministicETHFullSubexp.tableBound (amplificationLog amp) C (D.sizeExponent+4) Φ.val.variables := by
  let cut:=generatedN (cutoffLog (parameters D B).degree (parameters D B).deletion)
  refine ⟨max (DeterministicETHSourceBridge.graphPolynomialCutoff D B cs) (max cut 2),?_⟩
  intro Φ hsp hlarge
  let M:=Φ.val.variables
  have hm : 2≤M := (le_max_right _ _).trans ((le_max_right _ _).trans hlarge)
  have hcut : cut≤M := (le_max_left _ _).trans ((le_max_right _ _).trans hlarge)
  have hg : (t10Graph D B Φ).vertices≤M^(D.sizeExponent+3) :=
    DeterministicETHSourceBridge.sparse_graph_vertices_polynomial D B cs Φ hsp ((le_max_left _ _).trans hlarge)
  have hN:=public_floor_polynomial (parameters D B) M (D.sizeExponent+3)
    (source_geometry D B Φ).1 (source_geometry D B Φ).2.1 (source_geometry D B Φ).2.2
    hm (by omega) hg hcut
  have ha:=Nat.pow_le_pow_left (amplification_le amp) (rounds amp M)
  calc
    (generatedN (sourceLog D B Φ))^(C*amp^(rounds amp M))
      ≤(M^(D.sizeExponent+4))^(C*amp^(rounds amp M)) := Nat.pow_le_pow_left hN _
    _ = M^((D.sizeExponent+4)*(C*amp^(rounds amp M))) := by rw [←pow_mul]
    _ ≤ M^((D.sizeExponent+4)*C*(2^amplificationLog amp)^(rounds amp M)) := by
      apply Nat.pow_le_pow_right (by omega)
      have hh:=Nat.mul_le_mul_left ((D.sizeExponent+4)*C) ha
      simpa only [Nat.mul_assoc] using hh
    _ = _ := rfl

#print axioms request_length
#print axioms classifierClock_from_word
#print axioms source_scale_envelope
end
end CurrentAdditive.V40DeterministicETHEndpoint
