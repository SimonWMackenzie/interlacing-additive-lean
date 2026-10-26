import CurrentAdditive.V39RuntimeETHNumerics

namespace CurrentAdditive.V39CurrentSourceJoin
noncomputable section
set_option autoImplicit false

open Paper2 Paper2.Unit4Shell.T10Finite V38Schedule GeneratedCutoff
open EthInapproximability.CurrentPaper
open EncodedETHSource EncodedETHSourceComposition
open CurrentAdditive.V39GeneratedConstruction
open CurrentAdditive.V39ActualETHNumerics
open CurrentAdditive.V39RuntimeETHNumerics

variable (D : DinurReduction) (B : BOTReduction (booleanOccurrence D))

theorem runtime_source_eth_numerics (A C : ℕ) (hA : 2^64 ≤ A) (hC : 1040 ≤ C)
    (cs T₀ : ℕ) :
    ∃ M₀ : ℕ, ∀ Φ : ValidFormula,
      Φ.val.clauses.length ≤ cs*Φ.val.variables → M₀ ≤ Φ.val.variables →
      let M := Φ.val.variables
      let k := rounds A M
      let R := ethRun D B Φ k
      0 < errorCoefficient A ∧ 1 ≤ k ∧ (A^k)^2 ≤ M ∧ T₀ ≤ entryCount R ∧
        2*(errorCoefficient A:ℝ)*Real.logb 2 (Real.logb 2 (entryCount R)) < k ∧
        (ethWord D B Φ k).length ≤ M^((D.sizeExponent+4)*C*(2^amplificationLog A)^k) := by
  let p := parameters D B
  let g := D.sizeExponent+3
  let cut := generatedN (cutoffLog p.degree p.deletion)
  let big := 2^(max (32*(C*(g+1))+16) (8*amplificationLog A))
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
  have hnum := V39RuntimeETHNumerics.actual_numerics A C hA hC p M g
    (source_geometry D B Φ).1 (source_geometry D B Φ).2.1 (source_geometry D B Φ).2.2
    (CanonicalEdgeTape.graphEdge (t10Graph D B Φ) (t10Graph_valid D B Φ))
    hM (by dsimp [g]; omega) hgraph hcut hbig
  have hmin : T₀ ≤ entryCount (ethRun D B Φ (rounds A M)) :=
    (hT₀.trans (Nat.le_self_pow (by decide : 2 ≠ 0) M)).trans hnum.2.2.2.1
  exact ⟨hnum.1,hnum.2.1,hnum.2.2.1,hmin,hnum.2.2.2.2.1,
    by simpa only [g] using hnum.2.2.2.2.2⟩

/-- The source size accounting is discharged here. Only the separately
proved bound on an actual clock is consumed; no machine or run is supplied. -/
theorem runtime_source_clock_subexponential (A C : ℕ) (hA : 2^64 ≤ A) (hC : 1040 ≤ C)
    (cs u : ℕ) (hu : 1 ≤ u) :
    ∃ M₀ : ℕ, ∀ Φ : ValidFormula,
      Φ.val.clauses.length ≤ cs*Φ.val.variables → M₀ ≤ Φ.val.variables →
      let M := Φ.val.variables
      let k := rounds A M
      let N := generatedN (publicLogFrom (parameters D B) M
        (t10Graph D B Φ).vertices (t10Graph D B Φ).edges.length
        (source_geometry D B Φ).1 (source_geometry D B Φ).2.1 (source_geometry D B Φ).2.2)
      ∀ clock : ℕ, clock ≤ N^(C*A^k) → clock^u ≤ 2^M := by
  let p := parameters D B
  let g := D.sizeExponent+3
  let cut := generatedN (cutoffLog p.degree p.deletion)
  let big := 2^(max (32*(u*(g+1)*C)+16) (8*amplificationLog A))
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
  have hN := public_floor_polynomial p M g (source_geometry D B Φ).1
    (source_geometry D B Φ).2.1 (source_geometry D B Φ).2.2
    hM (by dsimp [g]; omega) hgraph hcut
  dsimp only
  intro clock hclock
  exact clock_subexponential_of_bound A C g u M _ clock hA hC hu hN hclock hbig

theorem runtime_source_output_subexponential (A C : ℕ) (hA : 2^64 ≤ A) (hC : 1040 ≤ C)
    (cs u : ℕ) (hu : 1 ≤ u) :
    ∃ M₀ : ℕ, ∀ Φ : ValidFormula,
      Φ.val.clauses.length ≤ cs*Φ.val.variables → M₀ ≤ Φ.val.variables →
      ((ethWord D B Φ (rounds A Φ.val.variables)).length)^u ≤ 2^Φ.val.variables := by
  obtain ⟨M₀,h⟩ := runtime_source_clock_subexponential D B A C hA hC cs u hu
  refine ⟨M₀,fun Φ hsparse hlarge => ?_⟩
  apply h Φ hsparse hlarge
  exact actual_size_arbitrary A C hA hC (parameters D B) Φ.val.variables
    (source_geometry D B Φ).1 (source_geometry D B Φ).2.1 (source_geometry D B Φ).2.2
    (CanonicalEdgeTape.graphEdge (t10Graph D B Φ) (t10Graph_valid D B Φ))
    (rounds A Φ.val.variables)

end
end CurrentAdditive.V39CurrentSourceJoin

#print axioms CurrentAdditive.V39CurrentSourceJoin.runtime_source_eth_numerics
#print axioms CurrentAdditive.V39CurrentSourceJoin.runtime_source_clock_subexponential
#print axioms CurrentAdditive.V39CurrentSourceJoin.runtime_source_output_subexponential
