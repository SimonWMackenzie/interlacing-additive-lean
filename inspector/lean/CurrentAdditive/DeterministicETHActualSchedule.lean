import CurrentAdditive.DeterministicETHGraphSize
import CurrentAdditive.DeterministicEndpointSchedule

/-! The source graph's actual counts enter the exact Appendix I dyadic
schedule. Formula variables are included in the public floor so the later
square table has enough entries for the estimator's eventual guarantee. -/

namespace CurrentAdditive.DeterministicETHSourceBridge

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.EncodedETHSource
open EthInapproximability.CurrentPaper.EncodedETHSourceComposition
open CurrentAdditive.DeterministicAdmissibility
open CurrentAdditive.DeterministicParameters
open CurrentAdditive.DeterministicEndpointSchedule
open Paper2.Unit4Shell.T10Finite
open Paper2.Unit4Shell.T10Size

variable (D : DinurReduction) (B : BOTReduction (booleanOccurrence D))

/-- On the exact sparse source graph, the public dyadic choice is
admissible, above the formula size, and polynomially bounded by it. -/
theorem sparse_formula_public_schedule (cs : ℕ) (Φ : ValidFormula)
    (hsparse : Φ.val.clauses.length ≤ cs * Φ.val.variables)
    (hgraphlarge : graphPolynomialCutoff D B cs ≤ Φ.val.variables)
    (hparamlarge : sourceCutoffSize B.degreeBound (sourceGap D B) ≤
      Φ.val.variables) :
    let G := t10Graph D B Φ
    let m := Φ.val.variables
    let L := publicLog (max G.vertices m) B.degreeBound (sourceGap D B)
    m ≤ N L ∧
    Admissible L B.degreeBound G.vertices G.edges.length
      sourceC128Ceil (sourceGap D B) ∧
    N L ≤ m^(D.sizeExponent+4) := by
  let G := t10Graph D B Φ
  have hg := sparse_graph_vertices_polynomial D B cs Φ hsparse hgraphlarge
  have hs := t10_source D B Φ
  have hdeg := (t45_relations D B Φ).2.1
  have hsize := public_schedule_for_eth G.vertices Φ.val.variables
    G.edges.length B.degreeBound (D.sizeExponent+3) (sourceGap D B)
    B.degreeBound_pos (source_gap_pos D B) hs.1 hdeg
    (by omega) ((le_max_left _ _).trans hgraphlarge) hg hparamlarge
  simpa only [Nat.add_assoc] using hsize

#print axioms sparse_formula_public_schedule

end CurrentAdditive.DeterministicETHSourceBridge
