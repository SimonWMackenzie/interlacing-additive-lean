import CurrentAdditive.IndexedActualConstruction
import CurrentAdditive.IndexedNumberedT10NoContract
import CurrentAdditive.DeterministicETHNumberedPresentation
import CurrentAdditive.DeterministicETHDecision
import CurrentAdditive.DeterministicETHConcreteIterationProd
import CurrentAdditive.DeterministicETHGapNo
import CurrentAdditive.IndexedNoContractProd

/-! The eventual deterministic classifier on one literal T10 graph and the
actual lookup-seeded indexed successor.  The only semantic NO input is the
full-W alignment of the internal matrix under the true graph-gap promise;
the physical source/step producer and resource bound remain explicit inputs. -/

namespace CurrentAdditive.DeterministicETHIndexedSeedEndpoint

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.EncodedETHSource
open EthInapproximability.CurrentPaper.EncodedETHSourceComposition
open CurrentAdditive.DeterministicParameters
open CurrentAdditive.DeterministicAdmissibility
open CurrentAdditive.DeterministicIteration
open CurrentAdditive.DeterministicEndpointAssembly
open CurrentAdditive.DeterministicETHConcreteIteration
open CurrentAdditive.DeterministicETHNumberedPresentation
open CurrentAdditive.IndexedExecutableStepRecovery
open CurrentAdditive.DeterministicETHGapNo
open CurrentAdditive.IndexedSemanticIteration
open CurrentAdditive.IndexedStagePresentation
open CurrentAdditive.DeterministicETHDecision
open CurrentAdditive.DeterministicETHComparator
open CurrentAdditive.DeterministicETHEstimator
open CurrentAdditive.DeterministicETHEncodedTable
open Paper2
open Paper2.Unit4Shell.T10Finite
open Workspace.Types.CommComplexity
open scoped Classical

variable (D : DinurReduction) (B : BOTReduction (booleanOccurrence D))
  (Φ : ValidFormula) (L : ℕ)
  [NeZero (t10Graph D B Φ).vertices]
  [NeZero (s L)] [NeZero (s L-3)] [NeZero (q₁ L)]
  [NeZero (q₂ L)] [NeZero (w L)] [NeZero (Q L)]

theorem indexed_t10_eth_midpoint
    (cs a C₁ C₀ : ℕ)
    (hsparse : Φ.val.clauses.length ≤ cs * Φ.val.variables)
    (hgraphlarge : CurrentAdditive.DeterministicETHSourceBridge.graphPolynomialCutoff
      D B cs ≤ Φ.val.variables)
    (hparamlarge : sourceCutoffSize B.degreeBound (sourceGap D B) ≤
      Φ.val.variables)
    (hL : L = publicLog (max (t10Graph D B Φ).vertices Φ.val.variables)
      B.degreeBound (sourceGap D B))
    (T : Schedule (Fin (t10Graph D B Φ).vertices)
      (Fin (t10Graph D B Φ).edges.length) L)
    (inputs : ∀ R : Stage (N L),
      StepInputs (V := Fin (t10Graph D B Φ).vertices)
        (E := Fin (t10Graph D B Φ).edges.length) L R T)
    (numberings : ∀ R : Stage (N L), ExplicitNumberings R)
    (ha : 1 ≤ a) (hC₀ : 2*C₁+2 ≤ C₀)
    (hlarge : 2^(max (32*(C₀*(D.sizeExponent+4))+16) (8*a)) ≤
      Φ.val.variables)
    (hresource : ResourceContract
      (indexedActualConstruction (t10Graph D B Φ).vertices
        (t10Graph D B Φ).edges.length L T inputs)
      (CanonicalEdgeTape.graphEdge (t10Graph D B Φ)
        (t10Graph_valid D B Φ)) (N L) (2^a) C₁)
    (est : List Bool → List Bool)
    (hest : EventuallyAccurate est (1/(4*(a:ℝ))))
    (hthreshold : hest.2.choose ≤ Φ.val.variables^2) :
    let G := CanonicalEdgeTape.graphEdge (t10Graph D B Φ)
      (t10Graph_valid D B Φ)
    let C := indexedActualConstruction (t10Graph D B Φ).vertices
      (t10Graph D B Φ).edges.length L T inputs
    let P := indexedActualNumberedTables (t10Graph D B Φ).vertices
      (t10Graph D B Φ).edges.length L T inputs numberings
    let k := CurrentAdditive.DeterministicEndpointNumeric.ethIterations a Φ.val.variables
    let M := paddedTable C (N L) P (state C G k)
    ∃ z : ℝ,
      Paper2.AModel.decodeDyadic (est (squareWord M)) = some z ∧
      (EncodedCNF.Satisfiable Φ.val →
        z < (budget (Paper2.LookupSeed.exponent L+1) (h L) k:ℝ)+(k:ℝ)/2) ∧
      (¬ EncodedCNF.Satisfiable Φ.val →
        (budget (Paper2.LookupSeed.exponent L+1) (h L) k:ℝ)+(k:ℝ)/2 < z) ∧
      Paper2.CmpOwner.machine.OutputsWithin
        (EncodedComplexity.pair
          (midpointHeader (budget (Paper2.LookupSeed.exponent L+1) (h L) k) k)
          (est (squareWord M)))
        [decide (EncodedCNF.Satisfiable Φ.val)]
        (Paper2.CmpOwner.cmpTime
          (midpointHeader (budget (Paper2.LookupSeed.exponent L+1) (h L) k) k).length
          (est (squareWord M)).length) := by
  let G := CanonicalEdgeTape.graphEdge (t10Graph D B Φ)
    (t10Graph_valid D B Φ)
  let C := indexedActualConstruction (t10Graph D B Φ).vertices
    (t10Graph D B Φ).edges.length L T inputs
  let P := indexedActualNumberedTables (t10Graph D B Φ).vertices
    (t10Graph D B Φ).edges.length L T inputs numberings
  let k := CurrentAdditive.DeterministicEndpointNumeric.ethIterations a Φ.val.variables
  have hs := CurrentAdditive.DeterministicETHSourceBridge.sparse_formula_public_schedule
    D B cs Φ hsparse hgraphlarge hparamlarge
  have hs' : Φ.val.variables ≤ N L ∧
      Admissible L B.degreeBound (t10Graph D B Φ).vertices
        (t10Graph D B Φ).edges.length sourceC128Ceil (sourceGap D B) ∧
      N L ≤ Φ.val.variables^(D.sizeExponent+4) := by
    simpa only [hL] using hs
  rcases hs' with ⟨hNlow, hadm, hNhigh⟩
  have hN : 2 ≤ N L := by
    have hTlarge := T.large
    have h4 := N_ge_four L (by omega : 2 ≤ L)
    omega
  have hY : ∀ g : IndexedSemanticIteration.Graph
      (Fin (t10Graph D B Φ).vertices)
      (Fin (t10Graph D B Φ).edges.length),
      Paper2.FiniteFallbackOutput.ThreeColourable g →
      YesContract C g (Paper2.LookupSeed.exponent L+1) (h L) := by
    intro g hg
    obtain ⟨colour, proper⟩ := hg
    exact indexedActual_yes _ _ L T inputs g colour proper
  have hH : GapNo (sourceGap D B) G →
      NoContract C G (Paper2.LookupSeed.exponent L+1) (h L) := by
    intro hg
    exact indexed_t10_no_contract_of_gap D B Φ L hL T inputs hg
  have hM := encoded_padded_midpoint C G
    Paper2.FiniteFallbackOutput.ThreeColourable
    (GapNo (sourceGap D B)) Φ.val.variables (N L)
    a (D.sizeExponent+4) C₁ C₀ (Paper2.LookupSeed.exponent L+1)
    (h L) ha (by omega : 1 ≤ D.sizeExponent+4) hN hNlow hNhigh
    hC₀ hlarge (indexedActual_valid _ _ L T inputs G)
    (indexedActual_universal _ _ L T inputs G)
    (hY G) hH hresource P est hest hthreshold
  obtain ⟨z, hz, hy, hn, hcmp⟩ := hM
  refine ⟨z, hz, ?_, ?_, ?_⟩
  · intro hsat
    exact hy ((t10_source D B Φ).2.2.2.2.2.1 hsat)
  · intro hunsat
    exact hn (t10_no_gap D B Φ hunsat)
  · have hbit :
        decide (z < (budget (Paper2.LookupSeed.exponent L+1) (h L)
          (CurrentAdditive.DeterministicEndpointNumeric.ethIterations a Φ.val.variables):ℝ)+
          (CurrentAdditive.DeterministicEndpointNumeric.ethIterations a Φ.val.variables:ℝ)/2) =
          decide (EncodedCNF.Satisfiable Φ.val) := by
      by_cases hsat : EncodedCNF.Satisfiable Φ.val
      · have hzlt := hy ((t10_source D B Φ).2.2.2.2.2.1 hsat)
        simp [hsat, hzlt]
      · have hhigh := hn (t10_no_gap D B Φ hsat)
        have hnlt : ¬ z < (budget (Paper2.LookupSeed.exponent L+1) (h L)
          (CurrentAdditive.DeterministicEndpointNumeric.ethIterations a Φ.val.variables):ℝ)+
          (CurrentAdditive.DeterministicEndpointNumeric.ethIterations a Φ.val.variables:ℝ)/2 :=
          not_lt_of_ge (le_of_lt hhigh)
        simp [hsat, hnlt]
    simpa only [hbit] using hcmp

#print axioms indexed_t10_eth_midpoint

end CurrentAdditive.DeterministicETHIndexedSeedEndpoint
