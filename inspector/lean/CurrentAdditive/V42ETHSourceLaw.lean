import CurrentAdditive.V42ActualSourceGap
import CurrentAdditive.V42ActualSourceEstimator
import CurrentAdditive.V42ETHNumerics
import CurrentAdditive.V40DeterministicEstimatorDomain

namespace CurrentAdditive.V42ETHSourceLaw
noncomputable section
open Paper2 EthInapproximability.CurrentPaper
open EncodedETHSource EncodedETHSourceComposition Unit4Shell.T10Finite
open V42ActualSource V42Schedule V39GeneratedConstruction
open V39RuntimeETHNumerics V39PermittedDeterministicExtraction V39FramedNumerical V39PermittedNumericalExtraction
open scoped Classical
open CurrentAdditive.V40DeterministicETHEndpoint (GrowingSquareAccuracy GrowingAccuracy stored_accuracy)
set_option maxHeartbeats 20000
set_option maxRecDepth 65536

variable (D:DinurReduction) (B:BOTReduction (booleanOccurrence D))

def amplification := V42GraphRuntime.amplification (k0 D B)
def constructionError : ℝ := errorCoefficient (amplification D B)

theorem constructionError_positive : 0<constructionError D B := by
  change 0<((errorCoefficient (amplification D B):ℚ):ℝ)
  exact_mod_cast coefficient_positive (amplification D B) (V42GraphRuntime.amplification_ge _)

#print axioms constructionError_positive

theorem source_numerics (cs T₀:ℕ) :
    ∃ M₀:ℕ,∀ Φ:ValidFormula,
      Φ.val.clauses.length ≤ cs*Φ.val.variables→M₀ ≤ Φ.val.variables→
      let K:=rounds (amplification D B) Φ.val.variables
      let R:=run D B Φ K
      1 ≤ K ∧ T₀ ≤ V42ActualLower.entryCount R ∧
      2*constructionError D B*Real.logb 2 (Real.logb 2 (V42ActualLower.entryCount R))<K := by
  let k₀:=k0 D B
  let A:=amplification D B
  let C:=V42ETHNumerics.sizeExponent B.degreeBound k₀
  let e:=D.sizeExponent+3
  let big:=2^(max (32*(C*(e+1))+16) (8*amplificationLog A))
  refine ⟨max (DeterministicETHSourceBridge.graphPolynomialCutoff D B cs)
    (max (2^(4*k₀)) (max 16 (max (B.degreeBound*T₀) big))),?_⟩
  intro Φ hsp hlarge
  let M:=Φ.val.variables
  have hgraphcut:DeterministicETHSourceBridge.graphPolynomialCutoff D B cs ≤ M := (le_max_left _ _).trans hlarge
  have hrest:max (2^(4*k₀)) (max 16 (max (B.degreeBound*T₀) big)) ≤ M := (le_max_right _ _).trans hlarge
  have hN₀:2^(4*k₀) ≤ M := (le_max_left _ _).trans hrest
  have hM:16 ≤ M := (le_max_left _ _).trans ((le_max_right _ _).trans hrest)
  have hT₀:B.degreeBound*T₀ ≤ M := (le_max_left _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans hrest))
  have hbig:big ≤ M := (le_max_right _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans hrest))
  have hgeom:=V39CurrentSourceJoin.source_geometry D B Φ
  have hsource:M ≤ B.degreeBound*(t10Graph D B Φ).vertices := by
    have hs:=(DeterministicETHSourceBridge.fixed_graph_source D B Φ).2.1
    exact hs.trans ((Nat.le_mul_of_pos_left _ (by decide : 0<2)).trans hgeom.2.2)
  have hgraph:(t10Graph D B Φ).vertices ≤ M^e :=
    DeterministicETHSourceBridge.sparse_graph_vertices_polynomial D B cs Φ hsp hgraphcut
  have h:=V42ETHNumerics.actual_numerics B.degreeBound k₀ M e T₀ (t10Graph D B Φ)
    (t10Graph_valid D B Φ) B.degreeBound_pos (k0_two D B) hgeom.1 hgeom.2.2 (k0_degree D B)
    hM (by unfold e;omega) hsource hgraph hN₀ hT₀ hbig
  have hout:=And.intro h.2.1 (And.intro h.2.2.1 h.2.2.2.1)
  simpa only [V42ActualSource.run,amplification,constructionError] using hout

#print axioms source_numerics

theorem classification_all_large (A:PermittedDeterministicEstimator) (cs T₀:ℕ)
    (hA:GrowingSquareAccuracy A (constructionError D B) T₀) :
    ∃ M₀:ℕ,∀ Φ:ValidFormula,
      Φ.val.clauses.length ≤ cs*Φ.val.variables→M₀ ≤ Φ.val.variables→
      (V42PermittedExtraction.estimator A).run
        (request D B Φ (rounds (amplification D B) Φ.val.variables))=
          [decide (EncodedCNF.Satisfiable Φ.val)] := by
  obtain ⟨M₀,hnum⟩:=source_numerics D B cs T₀
  refine ⟨M₀,?_⟩
  intro Φ hsp hlarge
  obtain ⟨hk,hT,hgap⟩:=hnum Φ hsp hlarge
  let K:=rounds (amplification D B) Φ.val.variables
  let E:=V42PermittedExtraction.estimator A
  have hv:ValidTable (word D B Φ K) := valid_of_target (word_target D B Φ K)
  have hacc:|E.value (E.output (word D B Φ K))-(Workspace.Types.CommComplexity.D (run D B Φ K).entry:ℝ)| ≤
      constructionError D B*Real.logb 2 (Real.logb 2 (V42ActualLower.entryCount (run D B Φ K))) := by
    rw [V42PermittedExtraction.estimator_value,V42PermittedExtraction.estimator_output A _ hv]
    simpa only [V42ActualSource.word] using stored_accuracy A _ T₀ hA (run D B Φ K) hT
  have hm:=midpoint_outputs E (word D B Φ K) (Workspace.Types.CommComplexity.D (run D B Φ K).entry)
    (threshold D B Φ K) K (constructionError D B*Real.logb 2 (Real.logb 2 (V42ActualLower.entryCount (run D B Φ K))))
    (by simpa only [mul_assoc] using hgap) hacc (source_comparison D B A Φ K)
  by_cases hs:EncodedCNF.Satisfiable Φ.val
  · simpa only [request,hs,decide_true] using hm.1 (run_yes D B Φ K hs)
  · simpa only [request,hs,decide_false] using hm.2 (run_no D B Φ K hs).ge

#print axioms source_numerics
#print axioms classification_all_large
end
end CurrentAdditive.V42ETHSourceLaw






