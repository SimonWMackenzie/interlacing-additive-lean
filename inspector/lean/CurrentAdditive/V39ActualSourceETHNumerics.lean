import CurrentAdditive.V39ActualETHNumerics

/-! Source-specialized entry counts and positive deterministic error margin.
The only source assumptions are the approved Dinur and BOT records. These
are size/error statements on the actual word, not an execution theorem.
-/

namespace CurrentAdditive.V39CurrentSourceJoin

open Paper2 Paper2.Unit4Shell.T10Finite V38Schedule GeneratedCutoff
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.EncodedETHSource
open EthInapproximability.CurrentPaper.EncodedETHSourceComposition
open CurrentAdditive.V39GeneratedConstruction
open CurrentAdditive.V39ActualETHNumerics
open CurrentAdditive.DeterministicEndpointNumeric

variable (D : DinurReduction) (B : BOTReduction (booleanOccurrence D))

theorem source_eth_numerics (cs T₀ : ℕ) :
    ∃ M₀ : ℕ, ∀ Φ : ValidFormula,
      Φ.val.clauses.length ≤ cs*Φ.val.variables → M₀ ≤ Φ.val.variables →
      let M := Φ.val.variables
      let k := ethIterations 64 M
      let R := ethRun D B Φ k
      1 ≤ k ∧ (supportAmplification^k)^2 ≤ M ∧ T₀ ≤ entryCount R ∧
        2*(1/256:ℝ)*Real.logb 2 (Real.logb 2 (entryCount R)) < k ∧
        (ethWord D B Φ k).length ≤ M^((D.sizeExponent+4)*1040*supportAmplification^k) := by
  let p := parameters D B
  let g := D.sizeExponent+3
  let cut := generatedN (cutoffLog p.degree p.deletion)
  let big := 2^(max (32*(1040*(g+1))+16) (8*64))
  refine ⟨max (DeterministicETHSourceBridge.graphPolynomialCutoff D B cs)
    (max cut (max 2 (max T₀ big))), ?_⟩
  intro Φ hsparse hlarge
  let M := Φ.val.variables
  have hgraphcut : DeterministicETHSourceBridge.graphPolynomialCutoff D B cs ≤ M :=
    (le_max_left _ _).trans hlarge
  have hrest : max cut (max 2 (max T₀ big)) ≤ M := (le_max_right _ _).trans hlarge
  have hM : 2 ≤ M := (le_max_left _ _).trans ((le_max_right _ _).trans hrest)
  have hcut : cut ≤ M := (le_max_left _ _).trans hrest
  have hT₀ : T₀ ≤ M := (le_max_left _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans hrest))
  have hbig : big ≤ M := (le_max_right _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans hrest))
  have hgraph : (t10Graph D B Φ).vertices ≤ M^g :=
    DeterministicETHSourceBridge.sparse_graph_vertices_polynomial D B cs Φ hsparse hgraphcut
  have hnum := actual_eth_numerics p M g (source_geometry D B Φ).1
    (source_geometry D B Φ).2.1 (source_geometry D B Φ).2.2
    (CanonicalEdgeTape.graphEdge (t10Graph D B Φ) (t10Graph_valid D B Φ))
    hM (by dsimp [g]; omega) hgraph hcut hbig
  have hmin : T₀ ≤ entryCount (ethRun D B Φ (ethIterations 64 M)) := by
    have hMsq : M ≤ M^2 := Nat.le_self_pow (by decide) _
    exact (hT₀.trans hMsq).trans hnum.2.2.1
  exact ⟨hnum.1,hnum.2.1,hmin,hnum.2.2.2.1,by simpa only [g] using hnum.2.2.2.2⟩

theorem source_output_subexponential (cs u : ℕ) (hu : 1 ≤ u) :
    ∃ M₀ : ℕ, ∀ Φ : ValidFormula,
      Φ.val.clauses.length ≤ cs*Φ.val.variables → M₀ ≤ Φ.val.variables →
      ((ethWord D B Φ (ethIterations 64 Φ.val.variables)).length)^u ≤ 2^Φ.val.variables := by
  let p := parameters D B
  let g := D.sizeExponent+3
  let cut := generatedN (cutoffLog p.degree p.deletion)
  let big := 2^(max (32*(u*(g+1)*1040)+16) (8*64))
  refine ⟨max (DeterministicETHSourceBridge.graphPolynomialCutoff D B cs)
    (max cut (max 2 big)), ?_⟩
  intro Φ hsparse hlarge
  let M := Φ.val.variables
  have hgraphcut : DeterministicETHSourceBridge.graphPolynomialCutoff D B cs ≤ M :=
    (le_max_left _ _).trans hlarge
  have hrest : max cut (max 2 big) ≤ M := (le_max_right _ _).trans hlarge
  have hM : 2 ≤ M := (le_max_left _ _).trans ((le_max_right _ _).trans hrest)
  have hcut : cut ≤ M := (le_max_left _ _).trans hrest
  have hbig : big ≤ M := (le_max_right _ _).trans ((le_max_right _ _).trans hrest)
  have hgraph : (t10Graph D B Φ).vertices ≤ M^g :=
    DeterministicETHSourceBridge.sparse_graph_vertices_polynomial D B cs Φ hsparse hgraphcut
  exact actual_output_subexponential p M g u (source_geometry D B Φ).1
    (source_geometry D B Φ).2.1 (source_geometry D B Φ).2.2
    (CanonicalEdgeTape.graphEdge (t10Graph D B Φ) (t10Graph_valid D B Φ))
    hM (by dsimp [g]; omega) hu hgraph hcut hbig

end CurrentAdditive.V39CurrentSourceJoin

#print axioms CurrentAdditive.V39CurrentSourceJoin.source_eth_numerics
#print axioms CurrentAdditive.V39CurrentSourceJoin.source_output_subexponential
