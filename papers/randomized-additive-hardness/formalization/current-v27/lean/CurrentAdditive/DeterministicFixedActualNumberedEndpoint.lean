import CurrentAdditive.DeterministicETHNumberedPresentation
import CurrentAdditive.DeterministicFixedDecision
import CurrentAdditive.DeterministicETHGraphAdmissible
import CurrentAdditive.DeterministicETHConcreteIterationProd
import CurrentAdditive.DeterministicETHGapNo
import CurrentAdditive.IndexedNoContractProd

/-! The all-table fixed-additive-error classifier on the exact T10 graph and
the literal lookup-seeded generated successor. No sparsity or eventual-size
condition is needed for this finite source promise. -/

namespace CurrentAdditive.DeterministicFixedActualNumberedEndpoint

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
open CurrentAdditive.DeterministicFixedDecision
open CurrentAdditive.DeterministicETHComparator
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

theorem actual_t10_fixed_midpoint_numbered
    (A C₁ C₀ : ℕ) (u : ℝ)
    (hL : L = publicLog (max (t10Graph D B Φ).vertices Φ.val.variables)
      B.degreeBound (sourceGap D B))
    (T : Schedule (Fin (t10Graph D B Φ).vertices)
      (Fin (t10Graph D B Φ).edges.length) L)
    (inputs : ∀ R : Stage (N L),
      StepInputs (V := Fin (t10Graph D B Φ).vertices)
        (E := Fin (t10Graph D B Φ).edges.length) L R T)
    (numberings : ∀ R : Stage (N L), ExplicitNumberings R)
    (hA : 2 ≤ A) (hC₀ : 2*C₁+2 ≤ C₀)
    (hresource : ResourceContract
      (actualConstruction (t10Graph D B Φ).vertices
        (t10Graph D B Φ).edges.length L T inputs)
      (CanonicalEdgeTape.graphEdge (t10Graph D B Φ)
        (t10Graph_valid D B Φ)) (N L) A C₁)
    (hfull : GapNo (sourceGap D B)
      (CanonicalEdgeTape.graphEdge (t10Graph D B Φ)
        (t10Graph_valid D B Φ)) →
      ∀ R : Stage (N L),
        3 ≤ Workspace.Types.CommComplexity.D R.matrix →
        RestrictionProfile R.matrix R.rowLaw.toFiniteLaw
          R.colLaw.toFiniteLaw (ρ L : ℝ)
          (Workspace.Types.CommComplexity.D R.matrix : ℤ) →
        FullWAt (t10Graph D B Φ).vertices
          (t10Graph D B Φ).edges.length L T inputs
          (CanonicalEdgeTape.graphEdge (t10Graph D B Φ)
            (t10Graph_valid D B Φ))
          B.degreeBound (sourceGap D B) R)
    (est : List Bool → List Bool) (hest : AccurateFixed est u) :
    let G := CanonicalEdgeTape.graphEdge (t10Graph D B Φ)
      (t10Graph_valid D B Φ)
    let C := actualConstruction (t10Graph D B Φ).vertices
      (t10Graph D B Φ).edges.length L T inputs
    let P := numberedActualTables (t10Graph D B Φ).vertices
      (t10Graph D B Φ).edges.length L T inputs numberings
    let k := ⌈2*u⌉₊+1
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
  let C := actualConstruction (t10Graph D B Φ).vertices
    (t10Graph D B Φ).edges.length L T inputs
  let P := numberedActualTables (t10Graph D B Φ).vertices
    (t10Graph D B Φ).edges.length L T inputs numberings
  let k := ⌈2*u⌉₊+1
  have hadm : Admissible L B.degreeBound (t10Graph D B Φ).vertices
      (t10Graph D B Φ).edges.length sourceC128Ceil (sourceGap D B) := by
    simpa only [hL] using
      (CurrentAdditive.DeterministicETHGraphAdmissible.t10_public_admissible D B Φ)
  have hN : 2 ≤ N L := by
    have hTlarge := T.large
    have h4 := N_ge_four L (by omega : 2 ≤ L)
    omega
  have hY : Paper2.FiniteFallbackOutput.ThreeColourable G →
      YesContract C G (Paper2.LookupSeed.exponent L+1) (h L) := by
    rintro ⟨colour, proper⟩
    exact actual_yes _ _ L T inputs G colour proper
  have hH : GapNo (sourceGap D B) G →
      NoContract C G (Paper2.LookupSeed.exponent L+1) (h L) := by
    intro hg
    exact actual_no_of_full_W _ _ L T inputs G B.degreeBound
      sourceC128Ceil (sourceGap D B) B.degreeBound_pos
      (source_gap_pos D B) hadm (hfull hg)
  have hgap : 2*u < (k:ℝ) := (fixed_real_gap_choice u).2
  have hm := fixed_encoded_midpoint C G
    Paper2.FiniteFallbackOutput.ThreeColourable
    (GapNo (sourceGap D B)) (N L) A C₁ C₀
    (Paper2.LookupSeed.exponent L+1) (h L) k
    hN hA hC₀ (actual_valid _ _ L T inputs G)
    (actual_universal _ _ L T inputs G)
    hY hH hresource P est u hest hgap
  obtain ⟨z, hz, hy, hn, hcmp⟩ := hm
  refine ⟨z, hz, ?_, ?_, ?_⟩
  · intro hsat
    exact hy ((t10_source D B Φ).2.2.2.2.2.1 hsat)
  · intro hunsat
    exact hn (t10_no_gap D B Φ hunsat)
  · have hbit :
        decide (z < (budget (Paper2.LookupSeed.exponent L+1) (h L) k:ℝ)+(k:ℝ)/2) =
          decide (EncodedCNF.Satisfiable Φ.val) := by
      by_cases hsat : EncodedCNF.Satisfiable Φ.val
      · have hzlt := hy ((t10_source D B Φ).2.2.2.2.2.1 hsat)
        simp [hsat, hzlt]
      · have hhigh := hn (t10_no_gap D B Φ hsat)
        have hnlt : ¬ z < (budget (Paper2.LookupSeed.exponent L+1) (h L) k:ℝ)+(k:ℝ)/2 :=
          not_lt_of_ge (le_of_lt hhigh)
        simp [hsat, hnlt]
    simpa only [hbit] using hcmp

#print axioms actual_t10_fixed_midpoint_numbered

end CurrentAdditive.DeterministicFixedActualNumberedEndpoint
