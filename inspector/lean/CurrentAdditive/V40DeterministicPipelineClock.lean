import CurrentAdditive.V40DeterministicSourcePipeline

/-! Complete original-variable clock arithmetic for the explicit source
pipeline. The sparse-decider theorem remains a CONDITIONAL INTERMEDIATE
until its source-run parameter is instantiated from the actual constructor. -/
namespace CurrentAdditive.V40DeterministicETHEndpoint
noncomputable section
open Paper2 V38Schedule EthInapproximability.CurrentPaper
open EncodedETHSource EncodedETHSourceComposition Unit4Shell.T10Finite
open V39CurrentSourceJoin V39RuntimeETHNumerics V39FramedNumerical
open V39PermittedDeterministicExtraction V40DeterministicSourcePack
open DeterministicETHFullSubexp
set_option maxHeartbeats 5000000
set_option maxRecDepth 32768

variable (D : DinurReduction) (B : BOTReduction (booleanOccurrence D))

theorem sourcePipeline_clock (E : Estimator) (amp C : ℕ) (hamp : 2^64≤amp) (hC : 1040≤C)
    (cs cutoff : ℕ) (hcut : 1≤cutoff) :
    ∃ m₁ K d p : ℕ, 1≤p ∧ ∀ Φ : ValidFormula,
      Φ.val.clauses.length≤cs*Φ.val.variables → m₁≤Φ.val.variables →
      sourcePipelineTime D B E amp C cs cutoff hcut (EncodedCNF.encode Φ.val)≤
        K*(tableBound (amplificationLog amp) C (D.sizeExponent+4) Φ.val.variables)^p*
          ((EncodedCNF.encode Φ.val).length+1)^d := by
  obtain ⟨mScale,hScale⟩:=source_scale_envelope D B amp C cs
  obtain ⟨mWord,hWord⟩:=runtime_source_eth_numerics D B amp C hamp hC cs 0
  let F:=sparseFront D B amp cs cutoff hcut
  let cPost:=(E.clockCoefficient+2)*256^(E.clockDegree+1)
  let p:=2*(E.clockDegree+1)
  refine ⟨max cutoff (max mScale (max mWord 2)),frontClockCoefficient F+(1+cPost),
    frontClockDegree F,p,by dsimp[p];omega,?_⟩
  intro Φ hsp hlarge
  have hcutΦ : cutoff≤Φ.val.variables := (le_max_left _ _).trans hlarge
  have hs : mScale≤Φ.val.variables := (le_max_left _ _).trans ((le_max_right _ _).trans hlarge)
  have hw : mWord≤Φ.val.variables := (le_max_left _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans hlarge))
  have htwo : 2≤Φ.val.variables := (le_max_right _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans hlarge))
  let Q:=tableBound (amplificationLog amp) C (D.sizeExponent+4) Φ.val.variables
  let k:=rounds amp Φ.val.variables
  have hQ : 1≤Q := Nat.one_le_pow _ _ (by omega)
  have hp : 1≤p := by dsimp[p];omega
  have hqpow : Q≤Q^p := Nat.le_self_pow (by omega) _
  have hclock : sourceRequestClock D B amp C Φ k≤Q := hScale Φ hsp hs
  have hword : (ethWord D B Φ k).length≤Q := (hWord Φ hsp hw).2.2.2.2.2
  have hpost:=classifierClock_from_word D B E Φ k Q hQ hword
  have hmain : sourceRequestClock D B amp C Φ k+classifierClock E (sourceRequest D B Φ k)≤
      (1+cPost)*Q^p := by
    change classifierClock E (sourceRequest D B Φ k)≤cPost*Q^p at hpost
    nlinarith
  have hfront:=frontClock_combine F (EncodedCNF.encode Φ.val) Q p (1+cPost)
    (sourceRequestClock D B amp C Φ k+classifierClock E (sourceRequest D B Φ k)) hQ hmain
  have hr:=routed_original cs cutoff hcut Φ hsp hcutΦ
  change sourcePipelineTime D B E amp C cs cutoff hcut (EncodedCNF.encode Φ.val)≤
    (frontClockCoefficient F+(1+cPost))*Q^p*((EncodedCNF.encode Φ.val).length+1)^frontClockDegree F
  unfold sourcePipelineTime
  rw [hr]
  change frontClock F (EncodedCNF.encode Φ.val)+sourceRequestClock D B amp C Φ k+
    classifierClock E (sourceRequest D B Φ k)≤_
  simpa only [Nat.add_assoc] using hfront

theorem sourcePipeline_sparse (M : BitMachine.Machine) (amp C : ℕ)
    (hamp : 2^64≤amp) (hC : 1040≤C)
    (A : PermittedDeterministicEstimator) (cs T₀ : ℕ)
    (hA : GrowingSquareAccuracy A (errorCoefficient amp:ℝ) T₀)
    (cutoff : ℕ) (hcut : 1≤cutoff)
    (hmin : semanticCutoff D B amp C hamp hC A cs T₀ hA≤cutoff)
    (pendingSourceRun : ∀ (Φ : ValidFormula) (k : ℕ),
      M.OutputsWithin (graphInput (t10Graph D B Φ) Φ.val.variables k)
        (sourceRequest D B Φ k) (sourceRequestClock D B amp C Φ k)) :
    DeterministicSparseETH.SparseDecider cs
      (sourcePipelineAlgorithm D B M amp C hamp hC A cs T₀ hA cutoff hcut hmin pendingSourceRun) := by
  obtain ⟨m₁,K,d,p,hp,hclock⟩:=sourcePipeline_clock D B (extractedEstimator A) amp C hamp hC cs cutoff hcut
  apply DeterministicSparseETHEventual.sparse_decider_of_eventual_tableBound_clock
    cs (amplificationLog amp) C (D.sizeExponent+4) p K d m₁
    (sourcePipelineAlgorithm D B M amp C hamp hC A cs T₀ hA cutoff hcut hmin pendingSourceRun)
    (by have h:=amplificationLog_ge amp hamp;omega) (by omega) (by omega) hp
  · intro Φ hsp
    exact sourcePipeline_correct cs cutoff hcut Φ hsp
  · intro Φ hsp hN
    exact hclock Φ hsp hN

#print axioms sourcePipeline_clock
#print axioms sourcePipeline_sparse
end
end CurrentAdditive.V40DeterministicETHEndpoint
