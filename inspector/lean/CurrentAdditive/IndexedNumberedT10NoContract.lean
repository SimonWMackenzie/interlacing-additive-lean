import CurrentAdditive.IndexedNumberedNoContract
import CurrentAdditive.DeterministicETHGraphAdmissible
import CurrentAdditive.DeterministicETHGapNo

/-! The physically numbered lookup seed and its literal successor satisfy
the NO induction on the exact sparse T10 source graph. -/

namespace CurrentAdditive.IndexedExecutableStepRecovery

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.EncodedETHSource
open EthInapproximability.CurrentPaper.EncodedETHSourceComposition
open CurrentAdditive.DeterministicParameters
open CurrentAdditive.DeterministicAdmissibility
open CurrentAdditive.IndexedSemanticIteration
open CurrentAdditive.IndexedStagePresentation
open CurrentAdditive.DeterministicIteration
open CurrentAdditive.DeterministicETHGapNo
open Paper2
open Paper2.Unit4Shell.T10Finite

variable (D : DinurReduction) (B : BOTReduction (booleanOccurrence D))
  (Φ : ValidFormula) (L : ℕ)
  [NeZero (t10Graph D B Φ).vertices]
  [NeZero (s L)] [NeZero (s L-3)] [NeZero (q₁ L)]
  [NeZero (q₂ L)] [NeZero (w L)] [NeZero (Q L)]

theorem indexed_t10_no_contract_of_gap
    (hL : L = publicLog (max (t10Graph D B Φ).vertices Φ.val.variables)
      B.degreeBound (sourceGap D B))
    (T : Schedule (Fin (t10Graph D B Φ).vertices)
      (Fin (t10Graph D B Φ).edges.length) L)
    (inputs : ∀ R : Stage (N L),
      StepInputs (V := Fin (t10Graph D B Φ).vertices)
        (E := Fin (t10Graph D B Φ).edges.length) L R T)
    (hgap : GapNo (sourceGap D B)
      (CanonicalEdgeTape.graphEdge (t10Graph D B Φ)
        (t10Graph_valid D B Φ))) :
    NoContract
      (indexedActualConstruction (t10Graph D B Φ).vertices
        (t10Graph D B Φ).edges.length L T inputs)
      (CanonicalEdgeTape.graphEdge (t10Graph D B Φ)
        (t10Graph_valid D B Φ))
      (Paper2.LookupSeed.exponent L+1) (h L) := by
  have hsource :=
    CurrentAdditive.DeterministicETHSourceBridge.fixed_graph_source D B Φ
  have hadm : Admissible L B.degreeBound (t10Graph D B Φ).vertices
      (t10Graph D B Φ).edges.length sourceC128Ceil (sourceGap D B) := by
    simpa only [hL] using
      (CurrentAdditive.DeterministicETHGraphAdmissible.t10_public_admissible D B Φ)
  exact indexed_actual_no_contract (t10Graph D B Φ).vertices
    (t10Graph D B Φ).edges.length L T inputs
    (CanonicalEdgeTape.graphEdge (t10Graph D B Φ)
      (t10Graph_valid D B Φ)) B.degreeBound (sourceGap D B)
    B.degreeBound_pos (source_gap_pos D B)
    hsource.2.2.2.2.1 hsource.2.2.1 hsource.2.2.2.1
    hgap hadm

theorem indexed_t10_no_contract
    (hL : L = publicLog (max (t10Graph D B Φ).vertices Φ.val.variables)
      B.degreeBound (sourceGap D B))
    (T : Schedule (Fin (t10Graph D B Φ).vertices)
      (Fin (t10Graph D B Φ).edges.length) L)
    (inputs : ∀ R : Stage (N L),
      StepInputs (V := Fin (t10Graph D B Φ).vertices)
        (E := Fin (t10Graph D B Φ).edges.length) L R T)
    (hno : ¬ EncodedCNF.Satisfiable Φ.val) :
    NoContract
      (indexedActualConstruction (t10Graph D B Φ).vertices
        (t10Graph D B Φ).edges.length L T inputs)
      (CanonicalEdgeTape.graphEdge (t10Graph D B Φ)
        (t10Graph_valid D B Φ))
      (Paper2.LookupSeed.exponent L+1) (h L) :=
  indexed_t10_no_contract_of_gap D B Φ L hL T inputs (t10_no_gap D B Φ hno)

#print axioms indexed_t10_no_contract_of_gap
#print axioms indexed_t10_no_contract

end CurrentAdditive.IndexedExecutableStepRecovery
