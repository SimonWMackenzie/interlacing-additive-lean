import CurrentAdditive.DeterministicETHGraphSize
import CurrentAdditive.DeterministicAdmissibility

/-! Every valid source formula, without a sparsity or large-input proviso,
has an admissible public dyadic schedule for the exact T10 graph. -/

namespace CurrentAdditive.DeterministicETHGraphAdmissible

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.EncodedETHSource
open EthInapproximability.CurrentPaper.EncodedETHSourceComposition
open CurrentAdditive.DeterministicParameters
open CurrentAdditive.DeterministicAdmissibility
open Paper2.Unit4Shell.T10Finite
open Paper2.Unit4Shell.T10Size

theorem t10_public_admissible
    (D : DinurReduction) (B : BOTReduction (booleanOccurrence D))
    (Φ : ValidFormula) :
    let G := t10Graph D B Φ
    let L := publicLog (max G.vertices Φ.val.variables)
      B.degreeBound (sourceGap D B)
    Admissible L B.degreeBound G.vertices G.edges.length
      sourceC128Ceil (sourceGap D B) := by
  let G := t10Graph D B Φ
  let L := publicLog (max G.vertices Φ.val.variables)
    B.degreeBound (sourceGap D B)
  have hsize := chosen_dyadic_size
    (max G.vertices Φ.val.variables) B.degreeBound
    sourceC128Ceil (sourceGap D B)
  have hn : G.vertices ≤ N L :=
    (le_max_left G.vertices Φ.val.variables).trans hsize.1
  have hdegree : 2 * G.edges.length ≤ B.degreeBound * G.vertices :=
    (t45_relations D B Φ).2.1
  exact admissible_from_cutoff L B.degreeBound G.vertices G.edges.length
    sourceC128Ceil (sourceGap D B)
    B.degreeBound_pos (source_gap_pos D B)
    (t10_source D B Φ).1 hdegree
    (publicLog_ge_cutoff (max G.vertices Φ.val.variables)
      B.degreeBound (sourceGap D B)) hn

#print axioms t10_public_admissible

end CurrentAdditive.DeterministicETHGraphAdmissible
